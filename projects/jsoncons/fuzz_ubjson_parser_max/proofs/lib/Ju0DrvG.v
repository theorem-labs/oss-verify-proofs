(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import RunEnv
PropExec CatExec CatSim SeqExec StoreOk SimInv ExitSim ShapeAlg ShapeLaws Nodes
MmapSim AllocSim FileSim AgentLib SpecConsts DivergeSim SpinAlg SpinAlgX
SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4 LibKnowFrame LibTail
Spec LibWritev RefNodes RefMemcpyLib RefReadLib RefPrintfLib Ju0Startup Ju0MainEntry Hoare MemSplit
Ju0MemcpyBase Ju0Memcpy Ju0ExitBase Ju0StdioDefs Ju0Exit Ju0LibStdioCall
HeapIface DrvKit Ju0Drv_defs Ju0DrvLib Ju0DrvA Ju0DrvB Ju0DrvG_defs.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Import SX2. Import SX2S.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Ju0DrvG () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Nat."; "Corelib.Init.Peano."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.Fs."; "LinuxProcessSemantics.LinuxProcessSem.StackLayout."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Instr."; "LinuxProcessSemantics.Riscv.Prelude."; "LinuxProcessSemantics.Riscv.Sem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.DrvKit."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ju0DrvA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ju0DrvB."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ju0DrvG.FPX_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ju0DrvG.FPX_1.DrvG."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ju0DrvG_defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ju0DrvLib."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ju0Drv_defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Spec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2Sound.SX2S."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymRun."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A"; "0A2"; "0Bc"; "1O"; "1Some"; "1app"; "1bool"; "1cons"; "1fst"; "1length"; "1list"; "1nat"; "1nil"; "1option"; "1pair"; "1prod"]; ["1snd"; "1true"; "2and"; "2eq"; "2not"; "2or"; "3add"; "4le"; "4lt"; "5firstn"; "5map"; "5skipn"; "6Z"; "0ENVb"; "0HI"; "0K"]; ["0Kc"; "0L"; "0LEN"; "7file_read"; "8EntryDraw"; "9FdChannel"; "9FdEntry"; "9Model"; "9VmMaps"; "9fd_lookup"; "9m_fds"; "9m_vmmaps"; ":ALU_ADD"; ":BC_EQ"; ":BC_LTU"; ":M_MUL"]; [";bvmap"; "<alu64"; "<mul_div"; "0M"; "0R"; "0RE"; "=ksubl_b"; "=log_in_b"; ">block_range"; ">credit"; ">defined"; ">hi_heap"; ">lb_remove"; ">model_but_vm"; "?ENV"; "?file_k"]; ["@keep_stage"; "BCAPk"; "Bcred"; "Bhdr_vals"; "Blp_at"; "Brd_at"; "Brefuse_k"; "Agr"; "Akbytes"; "ArelayV"; "Azbytes"; "Ccap2_x"; "CcellC"; "CcellR"; "Ckeep_rd"; "CknGbase"]; ["CknLP"; "CknLP6"; "CknRD"; "CknRa"; "CknRe0"; "Cwant_x"; "DIMG_W"; "Dhz"; "Ekn_blk"; "Frdn"; "Gmsg_refused"; "Gt_die"; "HELit"; "HEVar"; "HKRange"; "HSCBr"]; ["Hedenot"; "Hkentry"; "Hsentry"; "Iknow_ok"; "Imem_denot"; "Isc_denot"; "Jenv_agree"; "Jkn_vars_lt"; "Jvals_ev"; "Kloaded_segments"; "LIn"; "Madd"; "Meqb"; "Mle"; "Mlt"; "Mltb"]; ["Mmin"; "Mmodulo"; "Mmul"; "Mof_nat"; "Mopp"; "Mpow"; "Msub"; "Mto_nat"; "0VM"; "0a"; "0a0s"; "0b"; "0c"; "0cap"; "0cnt"; "0cr"]; ["0cr0"; "0data"; "0envv"; "0ext"; "0fdata"; "0fs0"; "0fx"; "0hi38"; "0hi70"; "0hw"; "0i"; "0j"; "0k"; "0kn"; "0kn6"; "0l"]; ["0len"; "0lo38"; "0lo70"; "0log"; "0m'"; "0mem0"; "0model1o"; "0n"; "0n2"; "0off"; "0path"; "0q"; "0r"; "0rdraw"; "0scfg"; "0sp0"]; ["0stdin0"; "NZ_to_bv"; "Nbv"; "Nbv_unsigned"; "0t"; "0tid"; "0vals"; "0w"; "0x38"; "0x48"; "0x70"; "0z"; "0zs"]]).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Local Ltac lia := first [ solve [ try (match goal with H : (length _ <= S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S _)))))))))))))))))))))))))))))))))%nat |- _ => clear dependent H end); Lia.lia ] | Lia.lia ].
Tactic Notation "run_blockL" constr(scr) constr(NX) := run_block_gen FUEL STOPS_L scr NX false.
Tactic Notation "run_blockL_keep" constr(scr) constr(NX) := run_block_gen FUEL STOPS_L scr NX true.
Tactic Notation "run_blockQ" constr(scr) constr(NX) := run_block_gen FUEL STOPS_Q scr NX false.
Tactic Notation "run_blockQ_keep" constr(scr) constr(NX) := run_block_gen FUEL STOPS_Q scr NX true.
Section FPX_1. Context {fx : PropExec.FPState}.
Variable scfg : SpuriousCfg.
Definition gr (R : bvmap 5 word) (i : nat) : word := getr R (Z_to_bv 5 (Z.of_nat i)).
Definition relayV (vals : list word) (R : bvmap 5 word) (x38 x48 x70 : word) (ext : list word) : list word :=
let z := Z_to_bv 64 0 in
[vals_ev vals 0; vals_ev vals 1; vals_ev vals 2; vals_ev vals 3; vals_ev vals 4; vals_ev vals 5]
++ map (gr R) (seq 0 32)
++ [x38; z; z; z; z; z; z; z; z; z; x48]
++ [z; z; z; z; z; z; z; z; z; z; z; z; z; z; z; z; z; z; z; z; z; x70]
++ ext.
#[using="Type"] Lemma relayV_len : ltac2:(TCodec.tc2 tcn__Ju0DrvG "O':'U2yR0%211%411&Q@y5%2214'C';&9&R9r6r5r4r3r2r1%76654321%92@1&FuR7%<2C5%3221%@3?51pX8E1pZFG1pZDH1pZBI1pS:F1pZ>J1").
Proof. intros. reflexivity. Qed.
#[using="Type"] Lemma relayV_lo : ltac2:(TCodec.tc2 tcn__Ju0DrvG "Q3':'U2yR0%211%411&Q@y5%2214';&Hr1u6%3221'C&S8&R9r8r7r6r5r4r3%76654321r2%:221%;292%=3G21p0?1pXHD1pX8I1pZFK1pZDL1pZBM1pS:J1pZ>N1").
Proof. intros vals R x38 x48 x70 ext j Hj. do 6 (destruct j as [|j]; [reflexivity|]). lia. Qed.
#[using="Type"] Lemma relayV_reg : ltac2:(TCodec.tc2 tcn__Ju0DrvG "Q7':'U2yR0%211%411&Q@y5%2214';&Hr1uQ0%3221'C&S8&R9r8r7r6r5r4r3%76654321&Fu6r2%3221%=251&R7%12<4%A3K31p0C1pXFH1pX8M1pZFO1pZDQ01pZBQ11pS:N1pZ>Q21").
Proof. intros vals R x38 x48 x70 ext i Hi. do 32 (destruct i as [|i]; [reflexivity|]). lia. Qed.
#[using="Type"] Lemma relayV_38 : ltac2:(TCodec.tc2 tcn__Ju0DrvG "K':'U2yR0%211%411&Q@y5%2214'C&S8&R9r6r5r4r3r2r1%76654321uQ6%:221%<3A17pX8A1pZFC1pZDD1pZBE1pS:B1pZ>F1"). Proof. reflexivity. Qed.
#[using="Type"] Lemma relayV_48 : ltac2:(TCodec.tc2 tcn__Ju0DrvG "K':'U2yR0%211%411&Q@y5%2214'C&S8&R9r6r5r4r3r2r1%76654321uQ@%:221%<3A16pX8A1pZFC1pZDD1pZBE1pS:B1pZ>F1"). Proof. reflexivity. Qed.
#[using="Type"] Lemma relayV_70 : ltac2:(TCodec.tc2 tcn__Ju0DrvG "K':'U2yR0%211%411&Q@y5%2214'C&S8&R9r6r5r4r3r2r1%76654321uR6%:221%<3A15pX8A1pZFC1pZDD1pZBE1pS:B1pZ>F1"). Proof. reflexivity. Qed.
#[using="Type"] Lemma relayV_71 : ltac2:(TCodec.tc2 tcn__Ju0DrvG "O':'U2yR0%211%411&Q@y5%2214'C&S8&R9r7r6r5r4r3(7r2r1%33@21%:6987651uR7%=221%?3D16pX8D1pZ@F1pZFG1pZDH1pZBI1pS:F1pZ>J1"). Proof. reflexivity. Qed.
#[using="Type"] Lemma relayV_agree : ltac2:(TCodec.tc2 tcn__Ju0DrvG "Q:':'U2y8%211%411yR0%511'Q4%812&Q@y5%2215&S6u6&QNr;r:r9r8r7r6%76654321&R9r5r4r3r2r1%66854321%?6>=<;:1%B3A91pX8G1pZFJ1pZDK1pZBL1pS:H1pZ>L1pX:Q11pYLO1pXDQ11pYFQ41pWFQ51").
Proof.
intros. split; [|reflexivity]. intros n Hn. cbn [ev ENV]. symmetry. apply relayV_lo. exact Hn.
Qed.
#[using="Type"] Lemma relay_know6 : ltac2:(TCodec.tc2 tcn__Ju0DrvG "R4':'U2y8%211%411yR0%511'Q4%812&Q@y5%2215'=%11:p081'S1%@11&S3&S9&QNr>r=r<r;r:r9%76654321r3r2%<4;321'C'6&QF%1265(A%53421&S7u6%221;%93815rAr@r?&R9r8r7%36HGFE21%L6765KJ1r6r4%Q14Q0321p0<1p0A1p0H1pXNQ61pXLQ71pS8Q:1pX8QA1pZFQD1pZDQE1pZBQF1pS:QB1pZ>QF1pX:QK1pYLQI1pXDQK1pYFQN1pWFQO1").
Proof.
intros a0s path hw rdraw fdata vals R x38 x48 x70 ext M kn kn6 HK Hsub Hv.
eapply (know_ok_agree RSEGS 6); [apply relayV_agree | exact Hv |].
eapply ksubl_sound; [exact HK | exact Hsub].
Qed.
#[using="Type"] Lemma knLP_split : ltac2:(TCodec.tc2 tcn__Ju0DrvG "='C':'S1%211&R@&5&RHuQ@+RPP0%3221&RA%63921%<3981"). Proof. reflexivity. Qed.
#[using="Type"] Lemma knLP6_vars : ltac2:(TCodec.tc2 tcn__Ju0DrvG "8'C'6&S7u6&RA%3221(A%73621"). Proof. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma knRD_split : ltac2:(TCodec.tc2 tcn__Ju0DrvG "@'C':'S1%211&RB(7&R=&5&RHuQ@+RPP0%3221&RA%63;21%93<81%?3<;1"). Proof. reflexivity. Qed.
#[using="Type"] Lemma knRe0_split : ltac2:(TCodec.tc2 tcn__Ju0DrvG "G'C':'S1%211&RD(7(RN(RMuR8%211+1+RPP0%63321&R=&5&RHuQ@%2216&RA%53A21%?3B71%@3C91%F3CB1"). Proof. reflexivity. Qed.
#[using="Type"] Lemma knGbase_sub : ltac2:(TCodec.tc2 tcn__Ju0DrvG "E'C'6&QF&5'S1&RHuQ@+RPP0%3221&RA(7&R<(<%119%43:31%<3;61%=3<81&R?%@221(A%D3C21"). Proof. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma mod_of_decompZ : ltac2:(TCodec.tc2 tcn__Ju0DrvG "O'L&S>zr3%3221'B&S=r2%2261r4%9231%6231'Cr6&S;&SBr5%2218%421?%73C61&SAr7%2219%;3G1>p051p0>1p0F1pYJK1pYHL1pWHM1pWDN1").
Proof. intros a b q r Hb Hr He. symmetry. apply (Zmod_unique a b q r); lia. Qed.
#[using="Type"] Lemma sub_as_add : ltac2:(TCodec.tc2 tcn__Ju0DrvG "Q8'L'B&S=zr1%3221r2%5231%7231&S>r3&SE+2+R0%3221%6251'C'U2yR0%211&QA(Q<&U1r4%2261&QB(Q?-1%62:1%72;C%54<421%;3:71&SF%12:G%<2@1%C3@41p0E1p0M1pY0Q61pWJQ71").
Proof.
intros c l Hl Hc. apply bv_eq. rewrite alu_add. unfold v_add. rewrite u_mul64.
rewrite !Z_to_bv_unsigned. change (bv_modulus 64) with (2 ^ 64)%Z.
rewrite (bv_wrap_small 64 l) by (change (bv_modulus 64) with (2 ^ 64)%Z; lia).
rewrite (bv_wrap_small 64 c) by (change (bv_modulus 64) with (2 ^ 64)%Z; lia).
unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64)%Z.
replace ((-1) mod 2 ^ 64)%Z with (2 ^ 64 - 1)%Z by reflexivity.
destruct (Z.eq_dec l 0) as [->|Hnz].
- rewrite Z.mul_0_r, Z.sub_0_r. cbn [Z.modulo Z.add]. rewrite Z.add_0_r. reflexivity.
- rewrite (mod_of_decompZ ((2 ^ 64 - 1) * l)%Z (2 ^ 64)%Z (l - 1)%Z (2 ^ 64 - l)%Z) by lia.
rewrite (mod_of_decompZ (c + (2 ^ 64 - l))%Z (2 ^ 64)%Z 1%Z (c - l)%Z) by lia.
rewrite (mod_of_decompZ (c - l)%Z (2 ^ 64)%Z 0%Z (c - l)%Z) by lia.
reflexivity.
Qed.
#[using="Type"] Lemma mul2_lit : ltac2:(TCodec.tc2 tcn__Ju0DrvG "O'L&S=zr1%3221&S>&SB+2r2%3221&SE+R0%2251%8241'C'U2yR0%211&QB(Q?&U1%125>r3%3271%648531%C2B3%62:1%=3:31p0?1p0I1pWJN1").
Proof.
intros c H0 H1. apply bv_eq. rewrite u_mul64. rewrite !u_small by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.
#[using="Type"] Lemma firstn_app_skipn : forall {A} (l : list A) (a b : nat),
firstn a l ++ firstn b (skipn a l) = firstn (a + b) l.
Proof.
intros A l a. revert l. induction a as [|a IH]; intros l b.
- reflexivity.
- destruct l as [|x l]; cbn; [rewrite firstn_nil; reflexivity|]. rewrite IH. reflexivity.
Qed.
#[using="Type"] Lemma file_read_lit : ltac2:(TCodec.tc2 tcn__Ju0DrvG "Q9':'U2y8%211%411'L'B&S=zr2%3221&S>&SE+2+R0%3221%5271%;271'C&Q3r5&U1yR0r4%3221r3%5241%83731&I&SG%115&K%319%23N1=%63O41%A3O81p0C1p0D1pWNQ11pYDQ21pX4Q41").
Proof. intros. rewrite file_read_unguarded, !word_to_nat_lit by lia. reflexivity. Qed.
#[using="Type"] Lemma length_read : ltac2:(TCodec.tc2 tcn__Ju0DrvG "Q;':'U2y8%211%411'L&S=zr2%3221r3&SC&9r4%22;1%411%:261%;2:7'C&I&SG%118&Kr5%411r6%43G21%83H61%@2I1%B11&S@&SF%D2M7%F11%321;%52F1%B3O71p0D1p0F1p0N1pWNQ31pYDQ41pX4Q61").
Proof. intros. rewrite length_firstn, length_skipn. lia. Qed.
#[using="Type"] Lemma lb_remove_2 : ltac2:(TCodec.tc2 tcn__Ju0DrvG "N'L&D'Cr4r2%33521%511':'?%1299%311&QLr3(7(>r5%24@@1=%34AA5=(<%11:%73;31%83<51%;2:1%:3>74%F3>21p0C1pY@J1p2K1pYBL1p4M1").
Proof.
intros A2 n2 A n H. cbn [lb_remove fst]. replace (A2 =? A)%Z with false by (symmetry; apply Z.eqb_neq; exact H).
rewrite Z.eqb_refl. reflexivity.
Qed.
#[using="Type"] Lemma keep_rd_Re0 : ltac2:(TCodec.tc2 tcn__Ju0DrvG "8'C':'S1%211&R>&RD%211%73412"). Proof. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma keep_stage_RD : ltac2:(TCodec.tc2 tcn__Ju0DrvG "D'C':'S1%211&R0(7'?';'L%3221(>uQ@+RPP0%346521(<%116%;3731&RB%>221%C3@12"). Proof. vm_compute. reflexivity. Qed.
Fixpoint kbytes (kn : list kentry) (b : expr) (k : Z) (n : nat) : option (list Z) :=
match n with
| O => Some []
| S n' => match kread RSEGS kn b k 1, kbytes kn b (k + 1) n' with
| Some (ELit z), Some r => Some (z :: r)
| _, _ => None
end
end.
Definition zbytes (zs : list Z) : list byte := flat_map (fun z => word_to_le_bytes 1 (Z_to_bv 64 z)) zs.
#[using="Type"] Lemma msg_refused_k : ltac2:(TCodec.tc2 tcn__Ju0DrvG "Q4'B'C'=':'L%211%411&R8&RC(RM(3%211-a@uQ6%746321(4&J'U2y8%211&U3%113&RJ%744C21%92C1%H3C;1%G17&R:%115%L3317';&9%12=:%Q0331D%Q2251%Q32:1").
Proof. vm_compute. repeat split; reflexivity. Qed.
Section DrvG.
Context {RE : RunEnv}.
Local Open Scope Z_scope.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis HIok : heap_iface_ok L scfg HI.
Variable sp0 : word.
Variables a0s path : list byte.
Variable envv : list (list byte).
Variable uid : word.
Variable hw : word.
Variable rdraw : EntryDraw.
Variable tid : word.
Variable regs0 : bvmap 5 word.
Variable mem0 : word -> option byte.
Variable VM0 : VmMaps.
Variable fs0 : Fs.
Variable stdin0 : InputStream.
Variable fdata : list byte.
Variable cr0 : credit.
Hypothesis Hva : valid_argv [a0s; path].
Hypothesis Hve : valid_envp envv.
Hypothesis Hvsp : valid_sp sp0.
Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
Hypothesis ME : main_entry sp0 [a0s; path] envv uid hw rdraw tid regs0 mem0.
Hypothesis Hfile : fs_lookup fs0 path = Some fdata.
Hypothesis Hplen : (length path <= 4095)%nat.
Hypothesis DL : drv_layout L sp0.
Let Hsp : (0x7fff80000000 <= bv_unsigned sp0 <= 0x800000000000)%Z := conj (proj1 Hvsp) (proj1 (proj2 Hvsp)).
Let Hal : (bv_unsigned sp0 mod 16 = 0)%Z := proj2 (proj2 Hvsp).
Let LEN : Z := Z.of_nat (length fdata).
Let ENVb (vals : list word) : env := ENV a0s path hw rdraw fdata vals.
Let above (M : word -> option byte) : Prop := above_sp0 sp0 mem0 M.
Let model1o (off : Z) (VM : VmMaps) : Model := model1o path tid fs0 stdin0 off VM.
Let model2 (VM : VmMaps) : Model := model2 tid fs0 stdin0 VM.
Definition hdr_vals (vals : list word) : Prop :=
vals_ev vals 0 = sp0 /\ vals_ev vals 1 = p0 sp0 a0s path envv /\ vals_ev vals 2 = p1 sp0 a0s path envv /\
vals_ev vals 3 = auxvp sp0 a0s path envv /\ vals_ev vals 4 = rnd sp0 a0s path envv /\ vals_ev vals 5 = tid.
#[using="fdata Hplen LEN"] Lemma hdr_relay : ltac2:(TCodec.tc2 tcn__Ju0DrvG "J':'U2yR0%211%411&Q@y5%2214&R3r6%211&R9r7r5r4r3r2%66584321%:11p091pX8@1pZFB1pZDC1pZBD1pS:A1pZ>E1").
Proof. intros vals R x38 x48 x70 ext H. unfold hdr_vals. rewrite !relayV_lo by lia. exact H. Qed.
#[using="uid hw rdraw Hva Hve Hvsp Hplen"] Lemma hiv_facts' : ltac2:(TCodec.tc2 tcn__Ju0DrvG "Q;':'U2yR0%211%411&R3r1%211';&S:(7u3u4(<%116%53731%63851%839;1'B&S=&U3vTO%22D1&S8r4r2%3221%72I1%9261&S;&SE+2+D%3221%5271+R0%6251%B231%D2:1p0F1pXFQ01p0Q21pZ>Q61").
Proof. intros vals (_ & _ & _ & P3 & P4 & _) i Hi. exact (hiv_facts sp0 a0s path envv uid hw rdraw Hva Hve Hvsp Hplen vals P3 P4 i Hi). Qed.
Definition CAPk (k : Z) : Z := 65536 * 2 ^ k.
Variables Kc Bc : Z.
Hypothesis HKc : 0 <= Kc. Hypothesis HBc : 0 <= Bc.
Definition cred (k : Z) (cr : credit) : Prop :=
(10 - k) * hl_k_per_malloc L + Kc <= fst cr /\ (2 ^ 27 - 2 * CAPk k) + (10 - k) * hl_b_overhead L + Bc <= snd cr.
#[using="sp0 path fdata Hplen LEN"] Lemma CAPk_S : ltac2:(TCodec.tc2 tcn__Ju0DrvG "C'L&S=zr1%3221'C&R1&S;r2+1%3221%511&SB+2%816%3221%;3@51p0=1pXJB1").
Proof. intros k Hk. unfold CAPk. rewrite Z.pow_add_r, Z.pow_1_r by lia. lia. Qed.
#[using="sp0 path fdata Hvsp Hplen Hsp LEN"] Lemma CAPk_range : ltac2:(TCodec.tc2 tcn__Ju0DrvG "C'L'B&S=zr1%3221+:%5231%7231+RPP0&R1r2%211%;241+RPPPP0%=231%?231p091pXJB1").
Proof.
intros k Hk. unfold CAPk. split.
- assert (1 <= 2 ^ k) by (apply Z.pow_pos_nonneg || idtac; pose proof (Z.pow_le_mono_r 2 0 k); cbn in *; lia). lia.
- pose proof (Z.pow_le_mono_r 2 k 10 ltac:(lia) ltac:(lia)) as H. change (2 ^ 10)%Z with 1024%Z in H. lia.
Qed.
#[using="sp0 path fdata Hvsp Hplen Hsp LEN"] Lemma CAPk_lt10 : ltac2:(TCodec.tc2 tcn__Ju0DrvG "A'L'B&S=zr1%3221&S>+:%2241%8241&R1r2%211+QPPPP0%<221p061pXJ@1").
Proof. intros k Hk. unfold CAPk. pose proof (Z.pow_le_mono_r 2 k 9 ltac:(lia) ltac:(lia)) as H. change (2 ^ 9)%Z with 512%Z in H. lia. Qed.
#[using="sp0 path fdata Hplen LEN"] Lemma CAPk_10 : ltac2:(TCodec.tc2 tcn__Ju0DrvG "E'L'B&S=zr1%3221+:%5231%7231'E'C&R1r2%211+RPPPP0%53?21&S>%125;%9231p0;1pXJD1").
Proof. intros k Hk. destruct (Z.eq_dec k 10) as [->|]; [left; reflexivity | right; lia]. Qed.
#[using="scfg HIok"] Lemma heap_facts1 : ltac2:(TCodec.tc2 tcn__Ju0DrvG "Q9'L&QI'U2yR0%211'=y8%511%311p051'Q8&QKvN(7'?%12??(>r5r4%34CC21(<%116%93731r3r2r1%?5>4321'B&QHvQ1r6%3321>&QJ%13:3@%7231p091pWBJ1pS8L1pX0Q51pY@Q71p2Q81").
Proof.
intros A n cr M VM HH. destruct (hio_wf L scfg HI HIok _ cr M VM HH) as [WF _].
destruct (WF (A, n) ltac:(left; reflexivity)) as (B & D & _). cbn [fst snd] in B, D. auto.
Qed.
Variable K : TSet.
Hypothesis HK0 : K [].
Definition close_kg (CAP : Z) (crC : credit) (KC : TSet) : Prop :=
forall vals R M VM (A1 : Z),
length vals = 71%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 48 = Z_to_bv 64 A1 -> vals_ev vals 70 = Z_to_bv 64 LEN ->
vals_ev vals 1 = p0 sp0 a0s path envv -> vals_ev vals 2 = p1 sp0 a0s path envv ->
vals_ev vals 3 = auxvp sp0 a0s path envv -> vals_ev vals 4 = rnd sp0 a0s path envv -> vals_ev vals 5 = tid ->
regs_ok (ENVb vals) srGL R ->
(forall lo hi, (lo <= LEN <= hi)%Z -> know_ok RSEGS (ENVb vals) M (knG lo hi)) ->
above M -> block_range L A1 CAP ->
rdn RSEGS M (Z_to_bv 64 A1) (length fdata) = Some fdata ->
hi_heap HI [(A1, CAP)] crC M VM ->
srealizes RSEGS scfg (mkCfg (mkst R (Z_to_bv 64 0xab160) M (seg_rom RSEGS)) (model2 VM)) KC.
Definition lp_at (z : Z) : Prop := forall (k len A : Z) vals R M VM cr,
0 <= k <= 10 -> 0 <= len <= CAPk k -> len <= LEN -> LEN - len <= z ->
length vals = 71%nat -> hdr_vals vals ->
vals_ev vals 38 = Z_to_bv 64 (CAPk k) -> vals_ev vals 48 = Z_to_bv 64 A -> vals_ev vals 70 = Z_to_bv 64 len ->
regs_ok (ENVb vals) srLP R -> know_ok RSEGS (ENVb vals) M knLP ->
above M -> rdn RSEGS M (Z_to_bv 64 A) (Z.to_nat len) = Some (firstn (Z.to_nat len) fdata) ->
hi_heap HI [(A, CAPk k)] cr M VM -> cred k cr ->
srealizes RSEGS scfg (mkCfg (mkst R (Z_to_bv 64 0x33ea4) M (seg_rom RSEGS)) (model1o len VM)) K.
Definition rd_at (z : Z) : Prop := forall (k len want A : Z) vals R M VM cr,
0 <= k <= 10 -> 0 <= len < CAPk k -> len <= LEN -> LEN - len <= z ->
want = Z.min (CAPk k - len) 65536 ->
length vals = 72%nat -> hdr_vals vals ->
vals_ev vals 38 = Z_to_bv 64 (CAPk k) -> vals_ev vals 48 = Z_to_bv 64 A -> vals_ev vals 70 = Z_to_bv 64 len ->
vals_ev vals 71 = Z_to_bv 64 want ->
regs_ok (ENVb vals) srRD R -> know_ok RSEGS (ENVb vals) M knRD ->
above M -> rdn RSEGS M (Z_to_bv 64 A) (Z.to_nat len) = Some (firstn (Z.to_nat len) fdata) ->
hi_heap HI [(A, CAPk k)] cr M VM -> cred k cr ->
srealizes RSEGS scfg (mkCfg (mkst R (Z_to_bv 64 0xab15c) M (seg_rom RSEGS)) (model1o len VM)) K.
Definition refuse_k (KR : TSet) : Prop := forall (A : Z) vals R M VM cr,
length vals = 71%nat -> hdr_vals vals ->
vals_ev vals 38 = Z_to_bv 64 67108864 -> vals_ev vals 48 = Z_to_bv 64 A -> vals_ev vals 70 = Z_to_bv 64 67108864 ->
regs_ok (ENVb vals) srLP R -> know_ok RSEGS (ENVb vals) M knLP ->
above M -> hi_heap HI [(A, 67108864)] cr M VM ->
srealizes RSEGS scfg (mkCfg (mkst R (Z_to_bv 64 0x33ea4) M (seg_rom RSEGS)) (model1o 67108864 VM)) KR.
Definition refuse_at : Prop := refuse_k K.
Hypothesis HKC : LEN < 67108864 -> forall CAP crC,
65536 <= CAP <= 67108864 -> LEN < CAP -> Kc <= fst crC -> Bc <= snd crC -> close_kg CAP crC K.
Hypothesis HREF : 67108864 <= LEN -> refuse_at.
Ltac norm_srget := repeat match goal with |- context [sr_get ?sr ?r] =>
let x := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with x end.
Ltac norm_nth := repeat match goal with |- context [nth ?i ?l (ELit 0)] =>
let x := eval vm_compute in (nth i l (ELit 0)) in change (nth i l (ELit 0)) with x end.
Ltac relay_absurd := match goal with Hi : (0 < _ < 32)%nat |- _ => solve [exfalso; clear - Hi; Lia.lia] end.
Ltac relay1 HR :=
norm_nth;
first [ relay_absurd
| reflexivity
| rewrite (reg_val _ _ _ _ HR); norm_srget; cbn [edenot ev ENVb ENV]; reflexivity
| idtac ].
Ltac relay_loop HR i :=
first [ relay_absurd | let j := fresh "i" in destruct i as [|j]; [ cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; relay1 HR | relay_loop HR j ] ].
Ltac relay_regs HR := apply regs_ok_by_nth; let i := fresh "i" in let Hi := fresh "Hi" in intros i Hi; relay_loop HR i.
Ltac relay2 HR :=
rewrite (reg_val _ _ _ _ HR); norm_srget; cbn [edenot ev ENVb ENV];
rewrite ?relayV_38, ?relayV_48, ?relayV_70, ?relayV_71; unfold gr;
rewrite ?(reg_val _ _ _ _ HR); norm_srget; cbn [edenot ev ENVb ENV].
Ltac regv1 HR := rewrite (reg_val _ _ _ _ HR); norm_srget; cbn [edenot ev ENVb ENV].
#[using="sp0 Hplen LEN"] Lemma sc_eq_70_38 : ltac2:(TCodec.tc2 tcn__Ju0DrvG "QO':'U2yR0%211%411'=y8%611%311p061'L'6'C&S8r5uR6%3221&U1r3%22A1%83A41r6uQ6%:221%<3E15'B&S=z%221>&S>&SE+2+R0%3221%52D1%:271&S<r7%221A%K3L1I&S5&S9r9vMr:%211(RO(Q=(RM%11Q2%21L%54N421%<4;:71p0>1p0C1p0D1p0Q01p0Q51pZ:Q?1pWLQA1pY2QB1pS8QD1pZ>QJ1").
Proof.
intros vals M len cap t P70 P38 Hl Hc Ht. cbn [sc_denot branch_taken edenot ev ENVb ENV]. rewrite P70, P38.
unfold bv_eqb. rewrite !u_small by lia. exact Ht.
Qed.
#[using="sp0 Hplen LEN"] Lemma want_x_val : ltac2:(TCodec.tc2 tcn__Ju0DrvG "QB':'U2yR0%211%411'L'C&S8r3uR6%3221&U1r2%22;1%83;41r4uQ6%:221%<3?15'B&S=z%2217%328?%5221&S>&SE+2+R0%3221%52?1&S0vMr7%211&RE%5221&SFr5r6%3221%N2Q71%Q43Q761p0=1p0D1p0K1p0Q01pWLQ:1pY2Q;1pZ>Q=1").
Proof.
intros vals len cap P70 P38 H1 H2. cbn [want_x edenot ev ENVb ENV]. rewrite P70, P38. apply sub_as_add; lia.
Qed.
#[using="sp0 Hvsp Hplen Hsp LEN"] Lemma sc_ltu_want : ltac2:(TCodec.tc2 tcn__Ju0DrvG "R4':'U2yR0%211%411'=y8%611%311p061'L'6'C&S8r5uR6%3221&U1r3%22A1%83A41r6uQ6%:221%<3E15'B&S=z%221>r4%42@1%6231&S>&SE+2+R0%3221%52G1&S?&SFr7%22D1+RPP0%5221%Q03Q11N&S5&S9r9vMr:%211(RO(Q>&RE(RL%11=%54Q3431%<4;:71p0>1p0F1p0M1p0Q51p0Q:1pZ:QD1pWLQF1pY2QG1pS8QI1pZ>QO1").
Proof.
intros vals M len cap t P70 P38 H1 H2 Ht. cbn [sc_denot branch_taken].
rewrite (want_x_val vals len cap P70 P38 H1 H2). cbn [edenot]. unfold bv_ltu. rewrite !u_small by lia. exact Ht.
Qed.
#[using="sp0 Hplen LEN"] Lemma cap2_x_val : ltac2:(TCodec.tc2 tcn__Ju0DrvG "Q:':'U2yR0%211%411'L'C&S8r2uR6%3221&U1r1%22;1%83;41&S=z%2219&S>&SB+2r3%3221&SE+R0%2251%8241&S0vMr5%211&R;%5221r4%?2>1%H2Q11%N3Q141p0;1p0E1p0I1pWLQ31pZ>Q51").
Proof. intros vals cap P70 H1 H2. cbn [cap2_x edenot ev ENVb ENV]. rewrite P70. apply mul2_lit; lia. Qed.
#[using="Type"] Lemma m1o_but : ltac2:(TCodec.tc2 tcn__Ju0DrvG "D'L'Q8'Q7&QMvTFr3r2%3221r1%6221'Cr4&Q;%117%:231%53=91p071pY:?1pWBA1pYDC1").
Proof. intros off VM m' H. exact H. Qed.
#[using="Type"] Lemma m1o_vm : ltac2:(TCodec.tc2 tcn__Ju0DrvG "<'L'Q8'C&Q;vTFr2r1%3221%511%73813pWB91pYD;1").
Proof. intros. reflexivity. Qed.
Lemma firstn_len_firstn : forall {X} (l : list X) w, firstn (length (firstn w l)) l = firstn w l.
Proof. intros X l w. rewrite length_firstn. rewrite <- (firstn_firstn l). rewrite firstn_firstn. f_equal. Abort.
#[using="Type"] Lemma firstn_len_firstn : forall {X} (l : list X) w, firstn (length (firstn w l)) l = firstn w l.
Proof.
intros X l. induction l as [|x l IH]; intros w.
- rewrite !firstn_nil. reflexivity.
- destruct w as [|w]; [reflexivity|]. cbn. rewrite IH. reflexivity.
Qed.
Section SE.
Local Abbreviation SEC_T_cred_exit := (ltac2:(TCodec.tc2 tcn__Ju0DrvG "J'L&QI'B&S=zr2%3221+:%5231%7231&R2r3%2217vQ0&8%13??4%=231v2&@%13CC8%A231%C251p0:1p0>1pX0G1pXJI1")) (only parsing).
Variable k : ltac:(sec_ty2 constr:(SEC_T_cred_exit) 0%nat 0%nat).
Variable cr : ltac:(sec_ty2 constr:(SEC_T_cred_exit) 1%nat 0%nat).
Lemma cred_exit : ltac:(sec_stmt2 constr:(SEC_T_cred_exit) 2%nat 0%nat).
Proof using sp0 path fdata Hvsp Hplen DL Hsp LEN k cr.
intros Hk [C1 C2].
pose proof (CAPk_range k Hk). pose proof (dl_k L sp0 DL). pose proof (dl_b L sp0 DL). nia.
Qed.
End SE.
#[using="fdata Hplen LEN"] Lemma hdr_app : ltac2:(TCodec.tc2 tcn__Ju0DrvG "F':'U2yR0%211%411&R3r2%211'Gu6&9r3%2291%5241&5r4%23=15%<11p051p0<1pX8@1pZ>A1").
Proof. intros vals ext H HL. unfold hdr_vals. rewrite !vals_ev_app_l by lia. exact H. Qed.
Section SE.
Local Abbreviation SEC_T_read_ok := (ltac2:(TCodec.tc2 tcn__Ju0DrvG "<'L&R4&SFr1+1%3221%511&R5r2%211p041pZH;1")) (only parsing).
Variable z : ltac:(sec_ty2 constr:(SEC_T_read_ok) 0%nat 0%nat).
Lemma read_ok : ltac:(sec_stmt2 constr:(SEC_T_read_ok) 1%nat 0%nat).
Proof using HIok uid Hva Hve Hvsp Htid Hfile Hplen DL Hsp Hal model2 HKC z.
intros IH.
unfold rd_at.
intros k len want A vals R M VM cr Hk Hlen HlL Hz Hwant HL HV P38 P48 P70 P71 HR HK HA HC HH Hcr.
pose proof Hsp as Hsp'. pose proof Hal as Hal'.
pose proof (CAPk_range k Hk) as HCk.
destruct (heap_facts1 _ _ _ _ _ HH) as [HBR HDEF].
pose proof (hz_of_block_range L sp0 DL _ _ HBR) as HZ. pose proof HZ as (Z1 & Z2 & Z3).
pose proof HV as HV'. destruct HV' as (P0 & P1 & P2 & P3 & P4 & P5).
pose proof (hiv_facts' vals HV) as HIV.
assert (Hw : 1 <= want <= 65536 /\ want <= CAPk k - len) by lia.
eapply (rz_read_file RSEGS scfg _ _ M (model1o len VM) ECALLW (Z_to_bv 64 3) path (Z_to_bv 64 len) fdata want);
try apply is_ecall_ECALLW.
- vm_compute. reflexivity.
- reflexivity.
- reflexivity.
- regv HR (17%bv : reg). reflexivity.
- regv HR (10%bv : reg). reflexivity.
- rewrite u_small by lia. lia.
- unfold model1o. rewrite m1o_fds. apply fds_lookup3.
- unfold model1o. rewrite m1o_fs. exact Hfile.
- regv HR (12%bv : reg). cbn [edenot ev ENVb ENV]. exact P71.
- lia.
- lia.
- lia.
- regv HR (11%bv : reg). cbn [edenot ev ENVb ENV]. apply stage_store_ok. lia.
- regv HR (11%bv : reg). cbn [edenot ev ENVb ENV]. rewrite u_small by lia. unfold TASK_SIZE. lia.
- cbv zeta. regv HR (12%bv : reg). regv HR (11%bv : reg). cbn [edenot ev ENVb ENV]. rewrite P71.
rewrite (file_read_lit fdata len want) by lia.
set (bs := firstn (Z.to_nat want) (skipn (Z.to_nat len) fdata)).
assert (Hnb : Z.of_nat (length bs) = Z.min want (LEN - len)) by (subst bs; unfold LEN; apply length_read; lia).
set (nb := Z.of_nat (length bs)) in Hnb.
rewrite v_addi_pc4 by lia. change (0xab15c + 4)%Z with 0xab160%Z.
unfold model1o. rewrite m1o_fds, with_fds_read. rewrite len_word_Z. fold nb.
replace (Z_to_bv 64 len + Z_to_bv 64 nb)%bv with (Z_to_bv 64 (len + nb))
by (apply bv_eq; rewrite bv_add_unsigned, !u_small by lia; symmetry; apply bv_wrap_small; change (bv_modulus 64) with (2 ^ 64)%Z; lia).
change (mkModelE (fd_insert fds0 (Z_to_bv 64 3) (FdFile path (Z_to_bv 64 (len + nb)))) VM stdin0 fs0 None (Some tid) None)
with (model1o (len + nb) VM).
set (M1 := wbytes M (Z_to_bv 64 750201) bs).
assert (HH1 : hi_heap HI [(A, CAPk k)] cr M1 VM).
{ subst M1. apply (heap_stagewrite scfg L HI HIok sp0 Hvsp DL); [lia | exact HH]. }
assert (HA1 : above M1).
{ subst M1. unfold above. apply (above_wbytes sp0 mem0 Hvsp); [lia | lia | exact HA]. }
assert (HC1 : rdn RSEGS M1 (Z_to_bv 64 A) (Z.to_nat len) = Some (firstn (Z.to_nat len) fdata)).
{ subst M1. rewrite rdn_wbytes_out; [exact HC | rewrite !u_small by lia; lia | rewrite u_small by lia; lia | rewrite u_small by lia; lia]. }
assert (HK1 : know_ok RSEGS (ENVb vals) M1 knRD).
{ rewrite <- keep_stage_RD. subst M1. unfold keep_stage.
eapply (know_stagewrite L sp0 a0s path hw rdraw fdata Hvsp DL vals M bs [(48%nat, 65536%Z)] [(A, CAPk k)] knRD P0 ltac:(lia) _ HIV HK).
Unshelve. intros i nb0 Hf. cbn in Hf.
destruct (Nat.eqb i 48) eqn:Ei; [|discriminate]. apply Nat.eqb_eq in Ei. subst i. injection Hf as <-.
split; [rewrite HL; lia|]. rewrite P48, u_small by lia. exists (CAPk k). split; [lia|]. split; [left; reflexivity | exact HBR]. }
assert (HDEF1 : defined M1 A (CAPk k)).
{ subst M1. intros i Hi. apply wbytes_grows. apply HDEF. exact Hi. }
assert (HSRC : rdn RSEGS M1 (Z_to_bv 64 750201) (length bs) = Some bs).
{ subst M1. apply rdn_wbytes_self. rewrite u_small by lia. lia. }
clearbody M1. clear HK HH HA HC HDEF.
destruct (Z.eq_dec nb 0) as [Hz0 | Hnz].
+
assert (HlenL : len = LEN) by lia.
rewrite Hz0, Z.add_0_r.
set (vals1 := vals ++ [Z_to_bv 64 0]).
assert (HL1 : length vals1 = 73%nat) by (subst vals1; rewrite length_app, HL; reflexivity).
assert (HV1 : hdr_vals vals1) by (subst vals1; unfold hdr_vals; rewrite !vals_ev_app_l by (rewrite HL; lia); exact HV).
assert (Q0 : vals_ev vals1 0 = sp0) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
assert (Q38 : vals_ev vals1 38 = Z_to_bv 64 (CAPk k)) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P38).
assert (Q48 : vals_ev vals1 48 = Z_to_bv 64 A) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P48).
assert (Q70 : vals_ev vals1 70 = Z_to_bv 64 len) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P70).
pose proof (env_app_regs vals [Z_to_bv 64 0] _ srRD R ltac:(rewrite HL; vm_compute; reflexivity) HR) as HR1.
pose proof (env_app_know RSEGS vals [Z_to_bv 64 0] _ M1 knRD ltac:(rewrite HL; vm_compute; reflexivity) HK1) as HK2.
fold vals1 in HR1, HK2. change (Env (vals_ev vals1) (blobs_ev (blobs0 a0s path hw rdraw ++ [fdata]))) with (ENVb vals1) in HR1, HK2.
pose proof (regs_set_a0 (ENVb vals1) _ _ (Z_to_bv 64 0) (ELit 0) HR1 eq_refl) as HR2.
change (sr_upd srRD (ridx 10) (ELit 0)) with srRf0 in HR2.
pose proof (hiv_facts' vals1 HV1) as HIV1.
clear HR HR1 HK1. rename HR2 into HR. rename HK2 into HK.
run_blockL_keep scr0 73%nat.
assert (HH2 : hi_heap HI [(A, CAPk k)] cr M0 VM).
{ rewrite EQM. eapply (heap_block scfg L HI HIok sp0 Hsp' DL vals1 _ []); [exact Q0 | intros i nb' Hf; discriminate | vm_compute; reflexivity | exact HH1]. }
assert (HA2 : above M0).
{ rewrite EQM. unfold above. apply (above_sp0_block sp0 a0s path hw rdraw mem0 fdata Hvsp Hplen vals1); [exact Q0 | vm_compute; reflexivity | exact HA1]. }
assert (HC2 : rdn RSEGS M0 (Z_to_bv 64 A) (length fdata) = Some fdata).
{ rewrite EQM. apply (content_block' sp0 a0s path hw rdraw fdata Hvsp vals1); [exact Q0 | vm_compute; reflexivity | eapply (hz_sub sp0); [exact HZ | lia | lia | unfold LEN in HlL; lia] |].
rewrite HlenL in HC1. unfold LEN in HC1. rewrite Nat2Z.id, firstn_all in HC1. exact HC1. }
destruct (heap_facts1 _ _ _ _ _ HH2) as [_ HDEF2].
clear EQM HH1 HA1 HC1 HDEF1.
eapply (rz_close RSEGS scfg _ _ M0 (model1o len VM) ECALLW (Z_to_bv 64 3)); try apply is_ecall_ECALLW.
* vm_compute. reflexivity.
* reflexivity.
* reflexivity.
* regv HR (17%bv : reg). reflexivity.
* regv HR (10%bv : reg). reflexivity.
* rewrite u_small by lia. lia.
* unfold model1o. rewrite m1o_fds. apply fds_lookup3.
* rewrite v_addi_pc4 by lia. change (0xab15c + 4)%Z with 0xab160%Z.
unfold model1o. rewrite m1o_fds, fds_remove3, with_fds_close.
pose proof (regs_set_a0 (ENVb vals1) _ _ (Z_to_bv 64 0) (ELit 0) HR eq_refl) as HR3. clear HR.
lazymatch goal with |- srealizes _ _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
set (valsG := relayV vals1 Rc (gr Rc 21) (gr Rc 9) (gr Rc 19) []);
pose proof (cred_exit k cr Hk Hcr) as [HX1 HX2];
pose proof (HKC ltac:(lia) (CAPk k) cr ltac:(lia) ltac:(lia) HX1 HX2) as CL;
unfold close_kg in CL;
apply (CL valsG Rc M0 VM A)
end.
-- reflexivity.
-- unfold valsG. rewrite relayV_lo by lia. exact Q0.
-- unfold valsG. rewrite relayV_48. unfold gr. regv1 HR3. exact Q48.
-- unfold valsG. rewrite relayV_70. unfold gr. regv1 HR3. rewrite Q70. f_equal. lia.
-- unfold valsG. rewrite relayV_lo by lia. exact (proj1 (proj2 HV1)).
-- unfold valsG. rewrite relayV_lo by lia. exact (proj1 (proj2 (proj2 HV1))).
-- unfold valsG. rewrite relayV_lo by lia. exact (proj1 (proj2 (proj2 (proj2 HV1)))).
-- unfold valsG. rewrite relayV_lo by lia. exact (proj1 (proj2 (proj2 (proj2 (proj2 HV1))))).
-- unfold valsG. rewrite relayV_lo by lia. exact (proj2 (proj2 (proj2 (proj2 (proj2 HV1))))).
-- unfold valsG, ENVb, ENV. relay_regs HR3.
-- intros lo hi Hlh. unfold knG. constructor.
++ cbn [kentry_ok edenot ev ENVb ENV]. unfold valsG. rewrite relayV_70. unfold gr. regv1 HR3.
rewrite Q70, u_small by lia. lia.
++ eapply ksubl_sound; [| exact knGbase_sub]. apply Forall_app. split.
** eapply (kn_blk_ok L sp0 Hsp' DL); [ | unfold valsG; rewrite relayV_lo by lia; exact Q0 | | ].
{ unfold valsG. rewrite relayV_48. unfold gr. regv1 HR3. exact Q48. }
{ unfold block_range in *. lia. }
{ intros i Hi. apply HDEF2. lia. }
** unfold valsG. eapply relay_know6; [exact HK | vm_compute; reflexivity | vm_compute; reflexivity].
-- exact HA2.
-- exact HBR.
-- exact HC2.
-- exact HH2.
+
set (vals1 := vals ++ [Z_to_bv 64 nb]).
assert (HL1 : length vals1 = 73%nat) by (subst vals1; rewrite length_app, HL; reflexivity).
assert (HV1 : hdr_vals vals1) by (subst vals1; unfold hdr_vals; rewrite !vals_ev_app_l by (rewrite HL; lia); exact HV).
assert (Q0 : vals_ev vals1 0 = sp0) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
assert (Q38 : vals_ev vals1 38 = Z_to_bv 64 (CAPk k)) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P38).
assert (Q48 : vals_ev vals1 48 = Z_to_bv 64 A) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P48).
assert (Q70 : vals_ev vals1 70 = Z_to_bv 64 len) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P70).
assert (Q72 : vals_ev vals1 72 = Z_to_bv 64 nb).
{ subst vals1. rewrite <- HL, <- (Nat.add_0_r (length vals)). rewrite vals_ev_app_r. reflexivity. }
pose proof (env_app_regs vals [Z_to_bv 64 nb] _ srRD R ltac:(rewrite HL; vm_compute; reflexivity) HR) as HR1.
pose proof (env_app_know RSEGS vals [Z_to_bv 64 nb] _ M1 knRD ltac:(rewrite HL; vm_compute; reflexivity) HK1) as HK2.
fold vals1 in HR1, HK2. change (Env (vals_ev vals1) (blobs_ev (blobs0 a0s path hw rdraw ++ [fdata]))) with (ENVb vals1) in HR1, HK2.
pose proof (regs_set_a0 (ENVb vals1) _ _ (Z_to_bv 64 nb) (EVar 72) HR1 ltac:(cbn [edenot ev ENVb ENV]; exact Q72)) as HR2.
change (sr_upd srRD (ridx 10) (EVar 72)) with srRe0 in HR2.
assert (HK3 : know_ok RSEGS (ENVb vals1) M1 knRe0).
{ constructor; [|exact HK2]. cbn [kentry_ok edenot ev ENVb ENV]. rewrite Q72, u_small by lia. lia. }
pose proof (hiv_facts' vals1 HV1) as HIV1.
clear HR HR1 HK1 HK2. rename HR2 into HR. rename HK3 into HK.
run_blockL_keep scr0 73%nat.
cbn [mem_denot] in EQM. subst M0.
assert (Hbl : length bs = Z.to_nat nb) by lia.
assert (WST : store_ok RSEGS M1 (Z_to_bv 64 (A + len)) (length bs) = true).
{ apply store_ok_of_defined; [lia | lia |]. intros i Hi. replace (A + len + i) with (A + (len + i)) by lia. apply HDEF1. lia. }
assert (MCH : mcH M1 (Z_to_bv 64 (A + len)) (Z_to_bv 64 750201) nb bs).
{ constructor; [lia | exact Hbl | exact HSRC | exact WST
| rewrite !u_small by lia; lia | rewrite u_small by lia; lia | rewrite u_small by lia; lia]. }
lazymatch goal with |- srealizes _ _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
destruct (ref_memcpy M1 (Z_to_bv 64 (A + len)) (Z_to_bv 64 750201) nb bs (seg_rom RSEGS) MCH Rc (Z_to_bv 64 0x33e9c)
ltac:(apply ret_ok_even; reflexivity)
ltac:(regv HR (1%bv : reg); reflexivity)
ltac:(regv HR (10%bv : reg); cbn [edenot ev ENVb ENV]; rewrite Q48, Q70, alu_add_Z; reflexivity)
ltac:(regv HR (11%bv : reg); reflexivity)
ltac:(regv HR (12%bv : reg); cbn [edenot ev ENVb ENV]; exact Q72)) as (R2 & MS & KP)
end.
replace (Z_to_bv 64 696756) with (0xaa1b4%bv : word) by (apply bv_eq; reflexivity).
eapply srz_msteps; [reflexivity | reflexivity | exact MS |]. clear MS.
pose proof (regs_after_keeps vals1 _ srRe_tk _ R2 callee_kept ltac:(rewrite HL1; vm_compute; reflexivity) HR KP ltac:(cbn; intuition discriminate)) as HR3.
rewrite HL1 in HR3. change (sr_after_call_j srRe_tk (map ridx callee_kept) 73) with srRm0 in HR3.
set (vals2 := vals1 ++ junk_vals R2) in *.
assert (HL2 : length vals2 = 105%nat) by (subst vals2; rewrite length_app, junk_vals_length, HL1; reflexivity).
pose proof (know_blockwrite sp0 Hsp' vals1 _ M1 A (CAPk k) (A + len) bs knRe0 Q0 HZ ltac:(lia) ltac:(lia) HIV1 HK) as HK3.
change (kn_keep_g 0 0 0 [] [] [3%nat; 4%nat] IMG_CLIENT IMG_RW knRe0) with (keep_rd knRe0) in HK3. rewrite keep_rd_Re0 in HK3.
pose proof (env_app_know RSEGS vals1 (junk_vals R2) _ _ knRe0 ltac:(rewrite HL1; vm_compute; reflexivity) HK3) as HK4.
fold vals2 in HK4. change (Env (vals_ev vals2) (blobs_ev (blobs0 a0s path hw rdraw ++ [fdata]))) with (ENVb vals2) in HR3, HK4.
clear HK HK3 HR. rename HR3 into HR. rename HK4 into HK.
set (M2 := wbytes M1 (Z_to_bv 64 (A + len)) bs) in *.
assert (HH2 : hi_heap HI [(A, CAPk k)] cr M2 VM).
{ subst M2. eapply (heap_wbytes scfg L HI HIok sp0 Hsp' DL); [exact HH1 | left; reflexivity | lia | lia | lia]. }
assert (HA2 : above M2).
{ subst M2. unfold above. apply (above_wbytes sp0 mem0 Hvsp); [lia | lia | exact HA1]. }
assert (HC2 : rdn RSEGS M2 (Z_to_bv 64 A) (Z.to_nat (len + nb)) = Some (firstn (Z.to_nat (len + nb)) fdata)).
{ replace (Z.to_nat (len + nb)) with (Z.to_nat len + length bs)%nat by lia.
rewrite <- firstn_app_skipn.
replace (firstn (length bs) (skipn (Z.to_nat len) fdata)) with bs by (subst bs; symmetry; apply firstn_len_firstn).
apply rdn_app_Z; [ | | lia | lia].
- subst M2. rewrite rdn_wbytes_out; [exact HC1 | rewrite !u_small by lia; lia | rewrite u_small by lia; lia | rewrite u_small by lia; lia].
- subst M2. rewrite Z2Nat.id by lia. apply rdn_wbytes_self. rewrite u_small by lia. lia. }
destruct (heap_facts1 _ _ _ _ _ HH2) as [_ HDEF2].
assert (X0 : vals_ev vals2 0 = sp0) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL1; lia); exact Q0).
assert (XV : hdr_vals vals2) by (subst vals2; apply hdr_app; [exact HV1 | rewrite HL1; lia]).
assert (X38 : vals_ev vals2 38 = Z_to_bv 64 (CAPk k)) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL1; lia); exact Q38).
assert (X48 : vals_ev vals2 48 = Z_to_bv 64 A) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL1; lia); exact Q48).
assert (X70 : vals_ev vals2 70 = Z_to_bv 64 len) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL1; lia); exact Q70).
assert (X72 : vals_ev vals2 72 = Z_to_bv 64 nb) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL1; lia); exact Q72).
pose proof (hiv_facts' vals2 XV) as HIV2.
clearbody M2. clear HH1 HA1 HC1 HDEF1 HSRC WST MCH KP.
run_blockL_keep scr0 105%nat.
cbn [mem_denot] in EQM. subst M0.
lazymatch goal with |- srealizes _ _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
set (valsL := relayV vals2 Rc (gr Rc 21) (gr Rc 9) (gr Rc 19) []);
apply (IH k (len + nb) A valsL Rc M2 VM cr)
end.
* lia.
* lia.
* lia.
* lia.
* reflexivity.
* unfold valsL. apply hdr_relay. exact XV.
* unfold valsL. rewrite relayV_38. unfold gr. regv1 HR. exact X38.
* unfold valsL. rewrite relayV_48. unfold gr. regv1 HR. exact X48.
* unfold valsL. rewrite relayV_70. unfold gr. regv1 HR. rewrite X70, X72, alu_add_Z. reflexivity.
* unfold valsL, ENVb, ENV. relay_regs HR; try (relay2 HR; reflexivity).
* rewrite knLP_split. apply Forall_app. split.
-- eapply (kn_blk_ok L sp0 Hsp' DL); [ | unfold valsL; rewrite relayV_lo by lia; exact X0 | | ].
{ unfold valsL. rewrite relayV_48. unfold gr. regv1 HR. exact X48. }
{ unfold block_range in *. lia. }
{ intros i Hi. apply HDEF2. lia. }
-- unfold valsL. eapply relay_know6; [exact HK | vm_compute; reflexivity | vm_compute; reflexivity].
* exact HA2.
* exact HC2.
* exact HH2.
* exact Hcr.
Qed.
End SE.
#[using="sp0 Hplen LEN"] Lemma know_LP_ranges : ltac2:(TCodec.tc2 tcn__Ju0DrvG "R@':'U2yR0%211%411'=y8%611%311p061'L'C&S8r8uR6%3221&U1r6%22@1%83@41r9uQ6%:221%<3D15'B&S=z%221>&S>&SE+2+R0%3221%52D1%:271r:%;2G1r7%=231%?231%?235%@26H%B221&S3&S9vMr>%211r=&R@%746321r?%711(7'S1(RN(RM%11Q;r;%4321H%41Q7%631Q9Q@%9381=%:3941%E4D<B1p0?1p0H1p0L1p0Q21p0Q31p0Q?1p0QD1pX@QN1pY4QO1pXBR01pY6R11pWLR21pY2R31pS8R51pZ>R;1").
Proof.
intros vals M len cap lo70 hi70 lo38 hi38 P70 P38 Hl Hc H70 H38 HK.
constructor; [|constructor; [|exact HK]]; cbn [kentry_ok edenot ev ENVb ENV]; rewrite ?P70, ?P38, u_small by lia; lia.
Qed.
#[using="Hvsp Hplen Hsp"] Lemma content_block_len : ltac2:(TCodec.tc2 tcn__Ju0DrvG "RK':'U2yR0%211%411'=y8%611%311p061'S2%;11'L'C&S8r6(3%3221vTO%63@21'6&QG&SE+2+Q8%3221(<'?';%221A%411%513&RFr5%=7B994321(A%G3@21&RGr4%23E61'B&S=z%2215%326;%5221vQ2%62>1%Q@1Q9%Q<11&RI&S9r:&U1r8%22QE1&SG%11Q:%847631(4&IvT4%23QG51%42?1%QC3?61&S4vMr<%211r;%5321Br9%C2R61r7%B11%I4H531%@3R52?%B2M1%R13M31p0?1p0Q11p0Q41p0Q;1p0Q?1p0R11pY2R91pY@R:1p2R;1pY8R=1pS8R@1pZ>RF1").
Proof.
intros vals M log A n len P0 Hlog HZ H2 H3 HC. pose proof Hsp as Hsp'.
assert (HLn : length (firstn (Z.to_nat len) fdata) = Z.to_nat len) by (rewrite length_firstn; unfold LEN in H3; lia).
rewrite <- HLn at 1. rewrite <- HLn in HC at 1.
apply (content_block' sp0 a0s path hw rdraw fdata Hvsp vals); [exact P0 | exact Hlog | eapply (hz_sub sp0); [exact HZ | lia | lia | rewrite HLn; lia] | exact HC].
Qed.
Section SE.
Local Abbreviation SEC_T_loop_step := (ltac2:(TCodec.tc2 tcn__Ju0DrvG "9'L&R5r1%211&R4r2%211p041pZH81")) (only parsing).
Variable z : ltac:(sec_ty2 constr:(SEC_T_loop_step) 0%nat 0%nat).
Lemma loop_step : ltac:(sec_stmt2 constr:(SEC_T_loop_step) 1%nat 0%nat).
Proof using HIok uid Hva Hve Hvsp Htid Hplen DL Hsp Hal HKc HBc HK0 HREF z.
intros HRD.
unfold lp_at.
intros k len A vals R M VM cr Hk Hlen HlL Hz HL HV P38 P48 P70 HR HK HA HC HH Hcr.
pose proof Hsp as Hsp'. pose proof Hal as Hal'.
pose proof (CAPk_range k Hk) as HCk.
destruct (heap_facts1 _ _ _ _ _ HH) as [HBR HDEF].
pose proof (hz_of_block_range L sp0 DL _ _ HBR) as HZ. pose proof HZ as (Z1 & Z2 & Z3).
pose proof HV as HV'. destruct HV' as (P0 & P1 & P2 & P3 & P4 & P5).
pose proof (hiv_facts' vals HV) as HIV.
pose proof (dl_k L sp0 DL) as Hkpm. pose proof (dl_b L sp0 DL) as Hovh.
destruct (Z_lt_le_dec len (CAPk k)) as [Hlt | Hge].
-
pose proof (know_LP_ranges vals M len (CAPk k) 0 67108863 65536 67108864 P70 P38 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) HK) as HK1.
change (KRange (EVar 70) 0 67108863 :: KRange (EVar 38) 65536 67108864 :: knLP) with knLPp in HK1.
clear HK. rename HK1 into HK.
assert (TAIL : forall want R1 M1 (sc12 : expr),
want = Z.min (CAPk k - len) 65536 ->
regs_ok (ENVb vals) (sr_upd srPa (ridx 12) sc12) R1 -> edenot (ENVb vals) sc12 = Z_to_bv 64 want ->
know_ok RSEGS (ENVb vals) M1 knRDp ->
M1 = mem_denot (ENVb vals) M (s_log (fst (fst rPa))) ->
srealizes RSEGS scfg (mkCfg (mkst R1 (Z_to_bv 64 0xab15c) M1 (seg_rom RSEGS)) (model1o len VM)) K).
{ intros want R1 M1 sc12 Hwant HR1 H12 HK1 EQM.
assert (HH1 : hi_heap HI [(A, CAPk k)] cr M1 VM).
{ rewrite EQM. eapply (heap_block scfg L HI HIok sp0 Hsp' DL vals _ []); [exact P0 | intros i nb Hf; discriminate | vm_compute; reflexivity | exact HH]. }
assert (HA1 : above M1).
{ rewrite EQM. unfold above. apply (above_sp0_block sp0 a0s path hw rdraw mem0 fdata Hvsp Hplen vals); [exact P0 | vm_compute; reflexivity | exact HA]. }
assert (HC1 : rdn RSEGS M1 (Z_to_bv 64 A) (Z.to_nat len) = Some (firstn (Z.to_nat len) fdata)).
{ rewrite EQM. apply (content_block_len vals _ _ A (CAPk k) len); [exact P0 | vm_compute; reflexivity | exact HZ | lia | lia | exact HC]. }
destruct (heap_facts1 _ _ _ _ _ HH1) as [_ HDEF1].
set (valsR := relayV vals R1 (gr R1 21) (gr R1 9) (gr R1 19) [gr R1 12]).
apply (HRD k len want A valsR R1 M1 VM cr); [lia | lia | lia | lia | exact Hwant | reflexivity | | | | | | | | exact HA1 | exact HC1 | exact HH1 | exact Hcr].
+ unfold valsR. apply hdr_relay. exact HV.
+ unfold valsR. rewrite relayV_38. unfold gr. regv1 HR1. exact P38.
+ unfold valsR. rewrite relayV_48. unfold gr. regv1 HR1. exact P48.
+ unfold valsR. rewrite relayV_70. unfold gr. regv1 HR1. exact P70.
+ unfold valsR. rewrite relayV_71. unfold gr. regv1 HR1. exact H12.
+ unfold valsR, ENVb, ENV. relay_regs HR1; try (relay2 HR1; reflexivity).
+ assert (K6 : know_ok RSEGS (ENVb valsR) M1 (cellR :: knLP6)).
{ unfold valsR. eapply relay_know6; [exact HK1 | vm_compute; reflexivity | vm_compute; reflexivity]. }
assert (KB : know_ok RSEGS (ENVb valsR) M1 (kn_blk 48 65536)).
{ eapply (kn_blk_ok L sp0 Hsp' DL); [ | unfold valsR; rewrite relayV_lo by lia; exact P0 | | ].
- unfold valsR. rewrite relayV_48. unfold gr. regv1 HR1. exact P48.
- unfold block_range in *. lia.
- intros i Hi. apply HDEF1. lia. }
rewrite knRD_split. constructor; [exact (Forall_inv K6)|]. apply Forall_app. split; [exact KB | exact (Forall_inv_tail K6)]. }
destruct (Z_lt_le_dec (CAPk k - len) 65536) as [Hsmall | Hbig].
+
run_blockL_keep (SCR [false; true] [] []) 71%nat.
{ apply (sc_ltu_want vals _ len (CAPk k) true P70 P38); [lia | lia | apply Z.ltb_lt; lia]. }
{ apply (sc_eq_70_38 vals _ len (CAPk k) false P70 P38); [lia | lia | apply Z.eqb_neq; lia]. }
apply (TAIL (CAPk k - len) _ _ want_x); [lia | exact HR | apply (want_x_val vals len (CAPk k) P70 P38); lia | exact HK | exact EQM].
+
run_blockL_keep (SCR [false; false] [] []) 71%nat.
{ apply (sc_ltu_want vals _ len (CAPk k) false P70 P38); [lia | lia | apply Z.ltb_ge; lia]. }
{ apply (sc_eq_70_38 vals _ len (CAPk k) false P70 P38); [lia | lia | apply Z.eqb_neq; lia]. }
apply (TAIL 65536 _ _ (ELit 65536)); [lia | exact HR | reflexivity | exact HK | exact EQM].
-
assert (Heq : len = CAPk k) by lia.
destruct (Z.eq_dec k 10) as [Hk10 | Hk10].
+
assert (HC10 : CAPk k = 67108864) by (rewrite Hk10; reflexivity).
assert (Hl10 : len = 67108864) by lia.
rewrite Hl10 in P70 |- *. rewrite HC10 in P38, HH.
apply (HREF ltac:(lia) A vals R M VM cr); assumption.
+
pose proof (CAPk_lt10 k ltac:(lia)) as HC25.
pose proof (know_LP_ranges vals M len (CAPk k) 65536 33554432 65536 33554432 P70 P38 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) HK) as HK1.
change (KRange (EVar 70) 65536 33554432 :: KRange (EVar 38) 65536 33554432 :: knLP) with knLPg in HK1.
clear HK. rename HK1 into HK.
run_blockL_keep (SCR [true] [] []) 71%nat.
{ apply (sc_eq_70_38 vals _ len (CAPk k) true P70 P38); [lia | lia | apply Z.eqb_eq; lia]. }
cbn [mem_denot] in EQM. subst M0.
lazymatch goal with |- srealizes _ _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
lazymatch type of HK with know_ok _ _ _ ?kn =>
eapply (malloc_site scfg L HI HIok sp0 Hsp' Hal' DL vals _ srGa kn Rc M (model1o len VM) [(A, CAPk k)] cr (2 * CAPk k) (-128)
[(48%nat, 65536%Z)] [] 0x33ec4 K);
[ exact HR | exact HK
| rewrite HL; vm_compute; reflexivity | rewrite HL; vm_compute; reflexivity | rewrite HL; lia
| exact P0 | exact HIV | vm_compute; reflexivity
| regv HR (2%bv : reg); cbn [edenot ev ENVb ENV]; rewrite P0; apply alu_add_w_lit
| lia | reflexivity
| regv HR (10%bv : reg); rewrite Heq in P70; apply (cap2_x_val vals (CAPk k) P70); lia
| lia
| destruct Hcr as [Hc1 Hc2]; unfold credit_ok; split; nia
| regv HR (4%bv : reg); reflexivity
| regv HR (1%bv : reg); reflexivity
| lia | reflexivity
| exact HH | reflexivity | reflexivity | reflexivity
| intros i nb Hf; cbn in Hf;
destruct (Nat.eqb i 48) eqn:Ei; [apply Nat.eqb_eq in Ei; subst i; injection Hf as <-; split; [rewrite HL; lia|];
rewrite P48, u_small by lia; exists (CAPk k); split; [lia|]; split; [left; reflexivity | exact HBR] | discriminate]
| intros v b Hf; discriminate
| exact HK0 | ]
end end.
intros R' M' model' A2 vals' E' HL' HA2 HR' HK' HH' HBUT HBR2 HAP HAB HBLK HIMG. subst vals' E'.
rewrite (m1o_but _ _ _ HBUT). rewrite (m1o_but _ _ _ HBUT), m1o_vm in HH'.
set (VM2 := m_vmmaps model') in *. clearbody VM2.
set (vals2 := vals ++ junk_vals R') in *.
change (Env (vals_ev vals2) (blobs_ev (blobs0 a0s path hw rdraw ++ [fdata]))) with (ENVb vals2) in HR', HK'.
rewrite HL in HL', HA2, HR', HK'. change (71 + 10)%nat with 81%nat in HA2.
pose proof (hz_of_block_range L sp0 DL _ _ HBR2) as HZ2. pose proof HZ2 as (U1 & U2 & U3). pose proof HBR2 as (_ & _ & U4 & _ & _).
assert (X0 : vals_ev vals2 0 = sp0) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
assert (XV : hdr_vals vals2) by (subst vals2; apply hdr_app; [exact HV | rewrite HL; lia]).
assert (X48 : vals_ev vals2 48 = Z_to_bv 64 A) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P48).
assert (X70 : vals_ev vals2 70 = Z_to_bv 64 (CAPk k)) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); rewrite <- Heq; exact P70).
pose proof (hiv_facts' vals2 XV) as HIV2.
apply Forall_app in HK' as [HKB HK'].
assert (HKU : know_ok RSEGS (ENVb vals2) M' knGb0).
{ change knGb0 with (kn_blk2 81 ++ keep_alloc MSO [(48%nat, 65536%Z)] [] knGa). apply Forall_app. split.
- unfold kn_blk2. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; cbn [kentry_ok edenot ev ENVb ENV]; rewrite HA2, u_small by lia; lia.
- exact HK'. }
clear HK' HKB HK HR. rename HKU into HK. rename HR' into HR.
destruct (hio_wf L scfg HI HIok _ _ _ _ HH') as [WF2 _].
destruct (WF2 (A2, 2 * CAPk k) ltac:(left; reflexivity)) as (_ & HDEF2 & _). cbn [fst snd] in HDEF2.
assert (WST : store_ok RSEGS M' (Z_to_bv 64 A2) (Z.to_nat (CAPk k)) = true).
{ apply store_ok_of_defined; [lia | lia |]. intros i Hi. apply HDEF2. lia. }
assert (HC2 : rdn RSEGS M' (Z_to_bv 64 A) (Z.to_nat (CAPk k)) = Some (firstn (Z.to_nat (CAPk k)) fdata)).
{ rewrite <- Heq, <- HC. symmetry. apply rdn_agree. intros j Hj. rewrite u_small by lia. symmetry. apply HBLK; [lia|].
exists (A, CAPk k). split; [left; reflexivity|]. cbn [fst snd]. lia. }
clear HC HH HDEF.
run_blockL_keep scr0 103%nat.
cbn [mem_denot] in EQM. subst M0.
assert (HFL : length (firstn (Z.to_nat (CAPk k)) fdata) = Z.to_nat (CAPk k)) by (rewrite length_firstn; unfold LEN in HlL; lia).
assert (MCH : mcH M' (Z_to_bv 64 A2) (Z_to_bv 64 A) (CAPk k) (firstn (Z.to_nat (CAPk k)) fdata)).
{ constructor; rewrite ?HFL, ?u_small by lia; try lia.
- exact HC2.
- exact WST.
- specialize (HAP (A, CAPk k) ltac:(left; reflexivity)). cbn [fst snd] in HAP. lia. }
lazymatch goal with |- srealizes _ _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
destruct (ref_memcpy M' (Z_to_bv 64 A2) (Z_to_bv 64 A) (CAPk k) (firstn (Z.to_nat (CAPk k)) fdata) (seg_rom RSEGS) MCH Rc (Z_to_bv 64 0x33ee0)
ltac:(apply ret_ok_even; reflexivity)
ltac:(regv HR (1%bv : reg); reflexivity)
ltac:(regv HR (10%bv : reg); cbn [edenot ev ENVb ENV]; exact HA2)
ltac:(regv HR (11%bv : reg); cbn [edenot ev ENVb ENV]; exact X48)
ltac:(regv HR (12%bv : reg); cbn [edenot ev ENVb ENV]; exact X70)) as (R2 & MS & KP)
end.
replace (Z_to_bv 64 696756) with (0xaa1b4%bv : word) by (apply bv_eq; reflexivity).
eapply srz_msteps; [reflexivity | reflexivity | exact MS |]. clear MS.
pose proof (regs_after_keeps vals2 _ srGb _ R2 callee_kept ltac:(rewrite HL'; vm_compute; reflexivity) HR KP ltac:(cbn; intuition discriminate)) as HR3.
rewrite HL' in HR3. change (sr_after_call_j srGb (map ridx callee_kept) 103) with srGc0 in HR3.
set (vals3 := vals2 ++ junk_vals R2) in *.
assert (HL3 : length vals3 = 135%nat) by (subst vals3; rewrite length_app, junk_vals_length, HL'; reflexivity).
pose proof (know_blockwrite sp0 Hsp' vals2 _ M' A2 (2 * CAPk k) A2 (firstn (Z.to_nat (CAPk k)) fdata) knGb0 X0 HZ2 ltac:(lia)
ltac:(rewrite HFL; lia) HIV2 HK) as HK3.
change (kn_keep_g 0 0 0 [] [] [3%nat; 4%nat] IMG_CLIENT IMG_RW knGb0) with knGc0 in HK3.
pose proof (env_app_know RSEGS vals2 (junk_vals R2) _ _ knGc0 ltac:(rewrite HL'; vm_compute; reflexivity) HK3) as HK4.
fold vals3 in HK4. change (Env (vals_ev vals3) (blobs_ev (blobs0 a0s path hw rdraw ++ [fdata]))) with (ENVb vals3) in HR3, HK4.
clear HK HK3 HR. rename HR3 into HR. rename HK4 into HK.
set (M3 := wbytes M' (Z_to_bv 64 A2) (firstn (Z.to_nat (CAPk k)) fdata)) in *.
assert (HH3 : hi_heap HI [(A2, 2 * CAPk k); (A, CAPk k)] (debit L cr (2 * CAPk k)) M3 VM2).
{ subst M3. eapply (heap_wbytes scfg L HI HIok sp0 Hsp' DL); [exact HH' | left; reflexivity | lia | rewrite HFL; lia | lia]. }
assert (HA3 : above M3).
{ subst M3. intros a Ha. rewrite wbytes_out; [rewrite HAB by exact Ha; apply HA; exact Ha | rewrite u_small, HFL by lia; lia | rewrite u_small, HFL by lia; lia]. }
assert (HC3 : rdn RSEGS M3 (Z_to_bv 64 A2) (length (firstn (Z.to_nat (CAPk k)) fdata)) = Some (firstn (Z.to_nat (CAPk k)) fdata)).
{ subst M3. apply rdn_wbytes_self. rewrite u_small, HFL by lia. lia. }
rewrite HFL in HC3.
assert (Y0 : vals_ev vals3 0 = sp0) by (subst vals3; rewrite vals_ev_app_l by (rewrite HL'; lia); exact X0).
assert (YV : hdr_vals vals3) by (subst vals3; apply hdr_app; [exact XV | rewrite HL'; lia]).
assert (Y48 : vals_ev vals3 48 = Z_to_bv 64 A) by (subst vals3; rewrite vals_ev_app_l by (rewrite HL'; lia); exact X48).
assert (Y70 : vals_ev vals3 70 = Z_to_bv 64 (CAPk k)) by (subst vals3; rewrite vals_ev_app_l by (rewrite HL'; lia); exact X70).
assert (Y81 : vals_ev vals3 81 = Z_to_bv 64 A2) by (subst vals3; rewrite vals_ev_app_l by (rewrite HL'; lia); exact HA2).
pose proof (hiv_facts' vals3 YV) as HIV3.
clearbody M3 vals3. clear HC2 WST HDEF2 WF2.
assert (NEQ : A2 <> A).
{ specialize (HAP (A, CAPk k) ltac:(left; reflexivity)). cbn [fst snd] in HAP. lia. }
run_blockL_keep scr0 135%nat.
cbn [mem_denot] in EQM. subst M0.
lazymatch goal with |- srealizes _ _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
lazymatch type of HK with know_ok _ _ _ ?kn =>
eapply (free_site scfg L HI HIok sp0 Hsp' Hal' DL vals3 _ srGc kn Rc M3 (model1o len VM2) [(A2, 2 * CAPk k); (A, CAPk k)]
(debit L cr (2 * CAPk k)) A (CAPk k) (-128) [] [] 0x33ee8 K);
[ exact HR | exact HK
| rewrite HL3; vm_compute; reflexivity | rewrite HL3; vm_compute; reflexivity | rewrite HL3; lia
| exact Y0 | exact HIV3 | vm_compute; reflexivity
| regv HR (2%bv : reg); cbn [edenot ev ENVb ENV]; rewrite Y0; apply alu_add_w_lit
| lia | reflexivity
| right; left; reflexivity
| regv HR (10%bv : reg); cbn [edenot ev ENVb ENV]; exact Y48
| regv HR (4%bv : reg); reflexivity
| regv HR (1%bv : reg); reflexivity
| lia | reflexivity
| exact HH3 | reflexivity | reflexivity | reflexivity
| intros i nb Hf; discriminate
| intros v b Hf; discriminate
| exact HK0 | ]
end end.
intros R4 M4 model4 vals' E' HL4 HR4 HK4 HH4 HBUT4 HAB4 HBLK4 HIMG4. subst vals' E'.
rewrite (lb_remove_2 A2 (2 * CAPk k) A (CAPk k) NEQ) in HH4, HBLK4.
rewrite (m1o_but _ _ _ HBUT4). rewrite (m1o_but _ _ _ HBUT4), m1o_vm in HH4.
set (VM4 := m_vmmaps model4) in *. clearbody VM4.
set (vals4 := vals3 ++ junk_vals R4) in *.
change (Env (vals_ev vals4) (blobs_ev (blobs0 a0s path hw rdraw ++ [fdata]))) with (ENVb vals4) in HR4, HK4.
rewrite HL3 in HL4, HR4.
change (sr_after_call_j srGc (map ridx c_kept) 135) with srGd0 in HR4.
lazymatch type of HK4 with know_ok _ _ _ ?kn => change kn with knGd0 in HK4 end.
assert (W0 : vals_ev vals4 0 = sp0) by (subst vals4; rewrite vals_ev_app_l by (rewrite HL3; lia); exact Y0).
assert (WV : hdr_vals vals4) by (subst vals4; apply hdr_app; [exact YV | rewrite HL3; lia]).
assert (W70 : vals_ev vals4 70 = Z_to_bv 64 (CAPk k)) by (subst vals4; rewrite vals_ev_app_l by (rewrite HL3; lia); exact Y70).
assert (W81 : vals_ev vals4 81 = Z_to_bv 64 A2) by (subst vals4; rewrite vals_ev_app_l by (rewrite HL3; lia); exact Y81).
pose proof (hiv_facts' vals4 WV) as HIV4.
assert (HC4 : rdn RSEGS M4 (Z_to_bv 64 A2) (Z.to_nat (CAPk k)) = Some (firstn (Z.to_nat (CAPk k)) fdata)).
{ rewrite <- HC3. apply rdn_agree. intros j Hj. rewrite u_small by lia. apply HBLK4; [lia|].
exists (A2, 2 * CAPk k). split; [left; reflexivity|]. cbn [fst snd]. lia. }
assert (HA4 : above M4).
{ intros a Ha. rewrite HAB4 by exact Ha. apply HA3. exact Ha. }
clear HR HK HC3 HA3 HH3. rename HR4 into HR. rename HK4 into HK.
run_blockL_keep scr0 167%nat.
assert (HH5 : hi_heap HI [(A2, 2 * CAPk k)] (debit L cr (2 * CAPk k)) M0 VM4).
{ rewrite EQM. eapply (heap_block scfg L HI HIok sp0 Hsp' DL vals4 _ []); [exact W0 | intros i nb Hf; discriminate | vm_compute; reflexivity | exact HH4]. }
assert (HA5 : above M0).
{ rewrite EQM. unfold above. apply (above_sp0_block sp0 a0s path hw rdraw mem0 fdata Hvsp Hplen vals4); [exact W0 | vm_compute; reflexivity | exact HA4]. }
assert (HC5 : rdn RSEGS M0 (Z_to_bv 64 A2) (Z.to_nat (CAPk k)) = Some (firstn (Z.to_nat (CAPk k)) fdata)).
{ rewrite EQM. apply (content_block_len vals4 _ _ A2 (2 * CAPk k) (CAPk k)); [exact W0 | vm_compute; reflexivity | exact HZ2 | lia | lia | exact HC4]. }
destruct (heap_facts1 _ _ _ _ _ HH5) as [_ HDEF5].
clear EQM HH4 HA4 HC4.
lazymatch goal with |- srealizes _ _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
set (valsR := relayV vals4 Rc (gr Rc 21) (gr Rc 9) (gr Rc 19) [gr Rc 12]);
apply (HRD (k + 1) len 65536 A2 valsR Rc M0 VM4 (debit L cr (2 * CAPk k)))
end.
* lia.
* rewrite CAPk_S by lia. lia.
* lia.
* lia.
* rewrite CAPk_S by lia. lia.
* reflexivity.
* unfold valsR. apply hdr_relay. exact WV.
* unfold valsR. rewrite relayV_38. unfold gr. regv1 HR. change (nth 21 srGd (ELit 0)) with cap2_x.
rewrite CAPk_S by lia. apply (cap2_x_val vals4 (CAPk k) W70); lia.
* unfold valsR. rewrite relayV_48. unfold gr. regv1 HR. exact W81.
* unfold valsR. rewrite relayV_70. unfold gr. regv1 HR. rewrite Heq. exact W70.
* unfold valsR. rewrite relayV_71. unfold gr. regv1 HR. reflexivity.
* unfold valsR, ENVb, ENV. relay_regs HR; try (relay2 HR; reflexivity).
* assert (K6 : know_ok RSEGS (ENVb valsR) M0 (cellR :: knLP6)).
{ unfold valsR. eapply relay_know6; [exact HK | vm_compute; reflexivity | vm_compute; reflexivity]. }
assert (KB : know_ok RSEGS (ENVb valsR) M0 (kn_blk 48 65536)).
{ eapply (kn_blk_ok L sp0 Hsp' DL); [ | unfold valsR; rewrite relayV_lo by lia; exact W0 | | ].
- unfold valsR. rewrite relayV_48. unfold gr. regv1 HR. exact W81.
- unfold block_range in *. lia.
- intros i Hi. apply HDEF5. lia. }
rewrite knRD_split. constructor; [exact (Forall_inv K6)|]. apply Forall_app. split; [exact KB | exact (Forall_inv_tail K6)].
* exact HA5.
* rewrite Heq. exact HC5.
* rewrite CAPk_S by lia. exact HH5.
* destruct Hcr as [Hc1 Hc2]. unfold cred, debit. cbn [fst snd]. rewrite CAPk_S by lia. split; nia.
Qed.
End SE.
#[using="HIok uid Hva Hve Hvsp Htid Hfile Hplen DL Hsp Hal model2 HKc HBc HK0 HKC HREF"] Lemma loop_ok : ltac2:(TCodec.tc2 tcn__Ju0DrvG "7';&R4&SCr1%211%411pY@61").
Proof.
induction n as [|n IH].
- apply loop_step. apply read_ok. unfold lp_at. intros. exfalso. lia.
- apply loop_step. apply read_ok. replace (Z.of_nat (S n) - 1) with (Z.of_nat n) by lia. exact IH.
Qed.
Hypothesis Hcr0 : cred 0 (debit L cr0 65536).
#[using="HIok uid Hva Hve Hvsp Htid Hfile Hplen DL Hsp Hal LEN ENVb above model1o model2 Kc Bc HKc HBc HK0 HKC HREF Hcr0"] Theorem drv_file : ltac2:(TCodec.tc2 tcn__Ju0DrvG "D&QOvT6vTNvQEvQ1vNvTOvSJvTJvT2vT9vTMvU5vTEvT5vU0vT4vT0vO%CBBA@?>=<;:987654321").
Proof.
unfold file_k.
intros vals R M VM A1 HL P0 P48 P1 P2 P3 P4 P5 HR HK HA HBR HH.
pose proof Hsp as Hsp'. pose proof Hal as Hal'.
pose proof (hz_of_block_range L sp0 DL _ _ HBR) as HZ. pose proof HZ as (Z1 & Z2 & Z3).
assert (HV : hdr_vals vals) by (unfold hdr_vals; repeat split; assumption).
pose proof (hiv_facts' vals HV) as HIV.
change (Env (vals_ev vals) (blobs_ev (blobs0 a0s path hw rdraw ++ [fdata]))) with (ENVb vals) in HR, HK |- *.
change (Ju0DrvA.above_sp0 sp0 mem0 M) with (above M) in HA.
change (model1 path tid fs0 stdin0 VM) with (model1o 0 VM).
run_blockL_keep scr0 70%nat.
assert (HH1 : hi_heap HI [(A1, 65536)] (debit L cr0 65536) M0 VM).
{ rewrite EQM. eapply (heap_block scfg L HI HIok sp0 Hsp' DL vals _ []); [exact P0 | intros i nb Hf; discriminate | vm_compute; reflexivity | exact HH]. }
assert (HA1 : above M0).
{ rewrite EQM. unfold above. apply (above_sp0_block sp0 a0s path hw rdraw mem0 fdata Hvsp Hplen vals); [exact P0 | vm_compute; reflexivity | exact HA]. }
destruct (heap_facts1 _ _ _ _ _ HH1) as [_ HDEF1].
clear EQM HH HA.
pose proof (read_ok (LEN + 1) ltac:(replace (LEN + 1 - 1) with (Z.of_nat (length fdata)) by (unfold LEN; lia); apply loop_ok)) as RD.
lazymatch goal with |- srealizes _ _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
set (valsR := relayV vals Rc (gr Rc 21) (gr Rc 9) (gr Rc 19) [gr Rc 12]);
apply (RD 0 0 65536 A1 valsR Rc M0 VM (debit L cr0 65536))
end.
- lia.
- unfold CAPk. rewrite Z.pow_0_r. lia.
- unfold LEN. lia.
- unfold LEN. lia.
- unfold CAPk. rewrite Z.pow_0_r. reflexivity.
- reflexivity.
- unfold valsR. apply hdr_relay. exact HV.
- unfold valsR. rewrite relayV_38. unfold gr. regv1 HR. unfold CAPk. rewrite Z.pow_0_r. reflexivity.
- unfold valsR. rewrite relayV_48. unfold gr. regv1 HR. exact P48.
- unfold valsR. rewrite relayV_70. unfold gr. regv1 HR. reflexivity.
- unfold valsR. rewrite relayV_71. unfold gr. regv1 HR. reflexivity.
- unfold valsR, ENVb, ENV. relay_regs HR; try (relay2 HR; reflexivity).
- assert (K6 : know_ok RSEGS (ENVb valsR) M0 (cellR :: knLP6)).
{ unfold valsR. eapply relay_know6; [exact HK | vm_compute; reflexivity | vm_compute; reflexivity]. }
assert (KB : know_ok RSEGS (ENVb valsR) M0 (kn_blk 48 65536)).
{ eapply (kn_blk_ok L sp0 Hsp' DL); [ | unfold valsR; rewrite relayV_lo by lia; exact P0 | | ].
- unfold valsR. rewrite relayV_48. unfold gr. regv1 HR. exact P48.
- exact HBR.
- exact HDEF1. }
rewrite knRD_split. constructor; [exact (Forall_inv K6)|]. apply Forall_app. split; [exact KB | exact (Forall_inv_tail K6)].
- exact HA1.
- reflexivity.
- unfold CAPk. rewrite Z.pow_0_r. exact HH1.
- exact Hcr0.
Qed.
#[using="Hvsp Hplen Hsp LEN"] Lemma kbytes_rdn_sp : ltac2:(TCodec.tc2 tcn__Ju0DrvG "R?':'U2yR0%211%411'=y8%611%311p061'S1%;11';'L%>11'C&S8r6(3%3221vTO%63B21&S3&S9vMr7%211r5%6452;1%H1?&R8(RM%11>r4%44A217(4r3%22G1%G3941&S=&SD&SE+2+D%3221%511%721C&S;&SC%11H%32Q11z%=221%QE1Q>%QA11&RIr:&U1&U3%12QIQ7%=21Q3%42QK1r8%84Q8721&R:%11Q@%O2=1%QD3=41p0@1p0G1p0Q01p0Q;1p0QC1pZJQK1pXJQM1pY@QO1pXLR11pS8R41pZ>R:1").
Proof.
intros vals M kn n. induction n as [|n IH]; intros k zs P0 HK Hkb Hk1 Hk2.
- cbn in Hkb. injection Hkb as <-. reflexivity.
- cbn [kbytes] in Hkb. destruct (kread RSEGS kn (EVar 0) k 1) as [[z| | | | | | |]|] eqn:Hr; try discriminate.
destruct (kbytes kn (EVar 0) (k + 1) n) as [r|] eqn:Hrest; [|discriminate]. injection Hkb as <-.
change (S n) with (1 + n)%nat. unfold zbytes. cbn [flat_map]. fold (zbytes r).
apply rdn_app_Z; [ | | lia | cbn; lia].
+ pose proof (kread_rdn RSEGS (ENVb vals) M kn (EVar 0) k 1 (ELit z) HK Hr ltac:(lia) ltac:(lia)
ltac:(unfold flat, estart; cbn [a_base a_off edenot ev ENVb ENV]; rewrite P0; lia)) as H.
unfold adenot, v_addi in H. cbn [a_base a_off edenot ev ENVb ENV] in H. rewrite P0 in H. exact H.
+ replace (bv_unsigned sp0 + k + Z.of_nat 1) with (bv_unsigned sp0 + (k + 1)) by lia.
apply IH; [exact P0 | exact HK | exact Hrest | lia | lia].
Qed.
#[using="Hvsp Hplen Hsp Hal LEN"] Lemma sc_and3_sp : forall vals M (off : Z) (c : branch_cond) (t : bool),
vals_ev vals 0 = sp0 -> off mod 4 <> 0 -> - 2 ^ 20 <= off <= 0 ->
match c with BC_NE => t = true | BC_EQ => t = false | _ => False end ->
sc_denot RSEGS M (ENVb vals) (SCBr t c (EAlu ALU_AND (EAlu ALU_ADD (EVar 0) (ELit off)) (ELit 3)) (ELit 0)).
Proof.
intros vals M off c t P0 Hoff Hr Hc.
assert (Hv : bv_eqb (edenot (ENVb vals) (EAlu ALU_AND (EAlu ALU_ADD (EVar 0) (ELit off)) (ELit 3))) (edenot (ENVb vals) (ELit 0)) = false).
{ cbn [edenot ev ENVb ENV]. rewrite P0, alu_add_w_lit. unfold bv_eqb. rewrite u_and64, !u_small by lia.
change 3 with (Z.ones 2). rewrite Z.land_ones by lia. change (2 ^ 2) with 4.
destruct (Z.eq_dec ((bv_unsigned sp0 + off) mod 4) 0) as [E|E]; [|apply Z.eqb_neq; exact E].
exfalso. apply Hoff.
assert (Hq : bv_unsigned sp0 = 16 * (bv_unsigned sp0 / 16)).
{ pose proof (Z_div_mod_eq_full (bv_unsigned sp0) 16). lia. }
rewrite Hq in E. replace (16 * (bv_unsigned sp0 / 16) + off) with (off + (4 * (bv_unsigned sp0 / 16)) * 4) in E by lia.
rewrite Z.mod_add in E by lia. exact E. }
destruct c; try contradiction; subst t; cbn [sc_denot branch_taken]; rewrite Hv; reflexivity.
Qed.
#[using="Type"] Lemma m1o_fd2 : ltac2:(TCodec.tc2 tcn__Ju0DrvG "I'L'Q8'C'='Q6%211&Q9&Q:vTFr2r1%3221%511&U1yR0+2%3221%;251(4(Q5%114%32A1%D3A51pWBF1pYDH1").
Proof. intros. reflexivity. Qed.
Ltac close_exit2m HR HK P0 P5 :=
lazymatch type of HK with know_ok ?segs ?E ?M ?kn =>
lazymatch goal with |- srealizes _ _ (mkCfg _ ?model) _ =>
apply (srz_conseq segs scfg _ (t_emit (W 1 []) (t_exit (bv_and (Z_to_bv 64 2) (Z_to_bv 64 255)) (m_fs model))));
[ | cbn [W map];
replace (bv_and (Z_to_bv 64 2) (Z_to_bv 64 255)) with (exit_code 2) by (apply bv_eq; reflexivity);
apply t_eq_sym; apply t_emit_nil_exit ];
apply ref_exit_Z;
let Ktid := fresh "Ktid" in
pose proof (know_nth segs _ _ kn ltac:(let i := kidx kn (is_krange (EVar 5)) in exact i) _ HK eq_refl)
as Ktid; cbn [kentry_ok edenot ev ENVb ENV] in Ktid; rewrite P5 in Ktid;
lazymatch type of HR with regs_ok _ _ ?Rc =>
eexists (Z_to_bv 64 (bv_unsigned sp0 - 128)); exists (Z_to_bv 64 0xc8cb0), (bv_unsigned tid);
eexists; eexists;
split; [|split; [reflexivity|split; [reflexivity|]]];
[ constructor;
[ regv HR (2%bv : reg); rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot ev ENVb ENV];
rewrite P0; f_equal; lia
| regv HR (4%bv : reg); reflexivity
| regv HR (10%bv : reg); reflexivity
| rewrite u_small by lia; lia
| rewrite u_small by lia; lia
| rewrite u_small by lia;
let Hst := fresh "Hst" in
pose proof (kwr_store_ok segs E _ kn ltac:(let i := kidx kn (is_kwr_cov (EVar 0) (-272) 144) in exact i)
_ _ _ (-272) 144 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst;
unfold adenot, v_addi in Hst; cbn [a_base a_off edenot ev ENVb ENV] in Hst; rewrite P0 in Hst;
replace (bv_unsigned sp0 - 128 - 144)%Z with (bv_unsigned sp0 + -272)%Z by lia; exact Hst
| lit_u; lia
| lit_u; lia
| lia
| lit_u; change (822448 - 168)%Z with 0xc8c08%Z;
let Htc := fresh "Htc" in
krd HK 0xc8c08%Z 4%nat Htc; rewrite Htc; cbn [ev ENVb ENV]; rewrite P5;
rewrite ext_val_zx_id by (change (2 ^ (8 * Z.of_nat 4))%Z with 4294967296%Z; lia);
rewrite Z_to_bv_bv_unsigned; reflexivity
| krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK | (exists 0%nat; split; krd_solve HK) | krd_solve HK
| repeat split; krd_solve HK
| repeat split; krd_solve HK ]
| left; split; [reflexivity|]; eexists; eexists; repeat split; krd_solve HK ]
end end end.
#[using="Hvsp Htid Hplen Hsp Hal LEN"] Theorem drv_refuse : ltac2:(TCodec.tc2 tcn__Ju0DrvG "6&R6&RK&RJvT5%3221%511").
Proof.
unfold refuse_k.
intros A vals R M VM cr HL HV P38 P48 P70 HR HK HA HH.
pose proof Hsp as Hsp'. pose proof Hal as Hal'.
pose proof HV as HV'. destruct HV' as (P0 & P1 & P2 & P3 & P4 & P5).
pose proof (know_LP_ranges vals M 67108864 67108864 67108864 67108864 67108864 67108864 P70 P38
ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) HK) as HK1.
change (KRange (EVar 70) 67108864 67108864 :: KRange (EVar 38) 67108864 67108864 :: knLP) with knLPr in HK1.
clear HK. rename HK1 into HK.
run_blockQ_keep scr_refuse 71%nat.
{ apply (sc_and3_sp vals _ (-535) BC_EQ false P0); [vm_compute; lia | lia | reflexivity]. }
{ apply (sc_and3_sp vals _ (-546) BC_NE true P0); [vm_compute; lia | lia | reflexivity]. }
{ apply (sc_and3_sp vals _ (-546) BC_EQ false P0); [vm_compute; lia | lia | reflexivity]. }
{ apply (sc_and3_sp vals _ (-546) BC_EQ false P0); [vm_compute; lia | lia | reflexivity]. }
{ apply (sc_and3_sp vals _ (-557) BC_EQ false P0); [vm_compute; lia | lia | reflexivity]. }
pose proof msg_refused_k as (KB & ZB & LB38).
lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
lazymatch type of HR with regs_ok _ ?sr ?Rc =>
unfold t_die, W;
assert (HSC : stdio_call 71 sr kn = Some scR) by (vm_compute; reflexivity);
pose proof (stdio_call_sound_fr scfg vals _ sr kn Rc Mc (model1o 67108864 VM) scR msg_refused []
(t_exit (exit_code 2) fs0) HR HK (eq_trans (f_equal (fun n => stdio_call n sr kn) HL) HSC)) as Hsc;
cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn scR app Z.of_nat] in Hsc;
rewrite app_nil_r, LB38 in Hsc;
apply Hsc; clear Hsc HSC
end end.
- rewrite !edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev ENVb ENV]. rewrite P0, !u_small by lia. lia.
- rewrite !edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev ENVb ENV]. rewrite P0, !u_small by lia. lia.
- rewrite !edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev ENVb ENV]. rewrite P0, !u_small by lia. lia.
- cbn [edenot length Z.of_nat]. lit_u. reflexivity.
- cbn [length Z.of_nat Z.add]. lia.
- right. rewrite !edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev ENVb ENV]. rewrite P0, !u_small by lia. lia.
- left. rewrite !edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev ENVb ENV]. rewrite P0, !u_small by lia. lia.
- cbn [edenot]. rewrite !u_small by lia. lia.
- rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev ENVb ENV]. rewrite P0, u_small by lia.
rewrite <- ZB. eapply (kbytes_rdn_sp vals _ _ 38%nat (-560)); [exact P0 | exact HK | exact KB | lia | cbn; lia].
- reflexivity.
- apply m1o_fd2.
- reflexivity.
- reflexivity.
- apply t_exit_has_nil.
- clear HR HK EQM.
intros R' M' HR HK HP.
assert (HL' : length (vals ++ junk_vals R') = 103%nat) by (rewrite length_app, junk_vals_length, HL; reflexivity).
assert (P0' : vals_ev (vals ++ junk_vals R') 0 = sp0) by (rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
assert (P5' : vals_ev (vals ++ junk_vals R') 5 = tid) by (rewrite vals_ev_app_l by (rewrite HL; lia); exact P5).
change (Env (vals_ev (vals ++ junk_vals R')) (blobs_ev (blobs0 a0s path hw rdraw ++ [fdata]))) with (ENVb (vals ++ junk_vals R')) in HR, HK.
run_blockQ scr0 103%nat.
close_exit2m HR HK P0' P5'.
Qed.
End DrvG.
End FPX_1.

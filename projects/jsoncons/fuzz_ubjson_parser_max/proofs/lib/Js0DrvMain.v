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
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import RunEnv
PropExec CatExec CatSim SeqExec StoreOk SimInv ExitSim ShapeAlg ShapeLaws Nodes
MmapSim AllocSim FileSim AgentLib SpecConsts DivergeSim SpinAlg SpinAlgX
SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX
Spec BigintSpec RefNodes Js0Startup Js0MainEntry Hoare
Js0Usage Js0OpenFail_defs Js0OpenFail
HeapIface LibIface DrvKit Js0Drv_defs Js0DrvLib Js0DrvA Js0DrvC_defs Js0DrvC Js0DrvD_defs Js0DrvLibL Js0DrvD
Js0DrvE Js0DrvF Js0DrvG_defs Js0DrvG Js0DrvH Js0Exit_run1.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Import SX2. Import SX2S.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Js0DrvMain () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Peano."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.Fs."; "LinuxProcessSemantics.LinuxProcessSem.State."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.BigintSpec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Js0DrvC."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Js0DrvD."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Js0DrvG."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Js0DrvMain.FPX_1.Main."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Spec."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0Bc"; "1O"; "1bool"; "1length"; "1list"; "1nil"; "1true"; "2eq"; "2iff"; "3le"; "3lt"; "4nth"; "5Z"; "0Kc"; "0L"; "6Fs"]; ["7event"; "8t_body"; "9credit_ok"; "9debit"; "9heap_layout"; "9hl_b_overhead"; "9hl_k_per_malloc"; ":CFG"; ":PL"; ";CALLS"; "<cred"; "=src_realizes_stmt2"; ">TSet"; ">t_emit"; ">t_exit"; "?MAX_INPUT"]; ["?W"; "?exit_code"; "?list_byte_eqb"; "?msg_overrun"; "?msg_refused"; "?msg_short"; "?t_die"; "?zero_lines"; "@add"; "@le"; "@lt"; "@modulo"; "@mul"; "@of_nat"; "@sub"; "@to_nat"]; ["0cr0"; "0data"; "0fs"; "0p"; "0q"; "AZ_to_bv"; "Abv"; "Abv_unsigned"]]).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPX_1.
Variable scfg : SpuriousCfg.
#[local] Existing Instance PropExec.fx0.
Local Open Scope Z_scope.
Lemma t_body_nil : ltac2:(TCodec.tc2 tcn__Js0DrvMain "?'4'QFy8%211%411&?&Ar2r1(5'@%211%63541pS681pS4:1").
Proof.
intros data fs. unfold t_body.
repeat (first [apply t_emit_has_nil | destruct (_ <=? _)%Z | destruct (_ <? _)%nat]).
Qed.
Lemma t_body_refused : ltac2:(TCodec.tc2 tcn__Js0DrvMain "J'4'QFy8%211%411&?&Q9&O&Q=&3r2%2281%411%7261'7&L&Ar3%2218&Q6&Q4%221;%83741p0:1pS6C1pS4E1").
Proof. intros data fs H. unfold t_body. replace (MAX_INPUT <=? Z.of_nat (length data))%Z with true by (symmetry; apply Z.leb_le; exact H). reflexivity. Qed.
Lemma t_body_short : ltac2:(TCodec.tc2 tcn__Js0DrvMain "Q0'4'QFy8%211%411&?&Q:&Q=&3r2%2271%411&O%7221&:r3%82=1u6%4221'7&L&Ar4%2218&Q6&Q5%221;%83741p0:1p0@1pS6I1pS4K1").
Proof.
intros data fs H1 H2. unfold t_body.
replace (MAX_INPUT <=? Z.of_nat (length data))%Z with false by (symmetry; apply Z.leb_gt; lia).
replace (length data <? 6)%nat with true by (symmetry; apply Nat.ltb_lt; exact H2). reflexivity.
Qed.
Lemma CFG_eq : ltac2:(TCodec.tc2 tcn__Js0DrvMain "O'4'QFy8%211%411'7'<&Q;&Q8&QG&;(1r1&QEz%22=1%64=541%82?1&Q<+X0u1%;4B196%=2D1%5241%@271+QPP0%C221&G%11@%H3G31pS4J1").
Proof. intros. reflexivity. Qed.
Lemma t_body_overrun : ltac2:(TCodec.tc2 tcn__Js0DrvMain "Q:'4'QFy8%211%411&?&Q:&Q=&3r2%2271%411&O%7221'9u6r3%92>1%4231r4%<2A1%>11&Q8+6&G%116%4231%E261'7&L&Ar5%221=&Q6&Q3%221@%83741p0:1p0D1p0J1pS6Q31pS4Q51").
Proof.
intros data fs H1 H2 H3. pose proof (CFG_range data) as HC. unfold t_body.
replace (MAX_INPUT <=? Z.of_nat (length data))%Z with false by (symmetry; apply Z.leb_gt; lia).
replace (length data <? 6)%nat with false by (symmetry; apply Nat.ltb_ge; lia). cbv zeta. rewrite CFG_eq.
replace (length data <? 6 + Z.to_nat (CFG data))%nat with true by (symmetry; apply Nat.ltb_lt; lia). reflexivity.
Qed.
Lemma t_body_ok : ltac2:(TCodec.tc2 tcn__Js0DrvMain "QB'4'QFy8%211%411&?&Q:&Q=&3r2%2271%411&O%7221&Q9&Q8+6&Gr3%211%5241%=2B3%?11%9231'7&L&Ar4%221:&M&Q0+1&Q7&Q?&I%118%311%511%8271&N&Q1z%211%421I%?261%E3DA1p0G1p0Q21pS6Q;1pS4Q=1").
Proof.
intros data fs H1 H3. pose proof (CFG_range data) as HC. pose proof (B2_range data) as HB. unfold t_body.
replace (MAX_INPUT <=? Z.of_nat (length data))%Z with false by (symmetry; apply Z.leb_gt; lia).
replace (length data <? 6)%nat with false by (symmetry; apply Nat.ltb_ge; lia). cbv zeta. rewrite CFG_eq.
replace (length data <? 6 + Z.to_nat (CFG data))%nat with false by (symmetry; apply Nat.ltb_ge; lia).
unfold CALLS. change (B2 data) with (bv_unsigned (nth 2 data (Z_to_bv 8 0))). fold (B2 data).
destruct (Z.to_nat (CFG data)) eqn:E.
- replace (CFG data =? 0)%Z with true by (symmetry; apply Z.eqb_eq; lia). reflexivity.
- replace (CFG data =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia).
rewrite Z2Nat.inj_add, Nat.add_1_r by lia. reflexivity.
Qed.
Lemma PL_eq : ltac2:(TCodec.tc2 tcn__Js0DrvMain "F'4'QFy8%211%411'7'<&Hr1%211&Q>&Q=&3%12:5%311+6%6221&G%11:%9231%?3>;1pS4A1").
Proof. intros. reflexivity. Qed.
Lemma list_byte_eqb_iff : ltac2:(TCodec.tc2 tcn__Js0DrvMain "B'4'QFy8%211%411&8'7'2&Q2r2r1%3221(6%73621%83:54%:221pS:<1pS8=1").
Proof.
intros p. induction p as [|a p IH]; intros [|b q]; cbn; try (split; [discriminate | discriminate]); [tauto|].
rewrite Bool.andb_true_iff, IH. unfold bv_eqb. rewrite Z.eqb_eq. split.
- intros [H1 H2]. f_equal; [apply bv_eq; exact H1 | exact H2].
- intros H. injection H as -> ->. auto.
Qed.
Section Main.
Variable LF : word -> heap_layout.
Variable HIF : word -> heap_iface.
Variable LayF : word -> lib_layout.
Variable LStF : word -> lib_statics.
Variable cr0 : credit.
Hypothesis HIokF : forall sp, valid_sp sp -> heap_iface_ok (LF sp) scfg (HIF sp).
Hypothesis DLF : forall sp, valid_sp sp -> drv_layout (LF sp) sp.
Hypothesis DLLF : forall sp, valid_sp sp -> drv_lib_layout (LayF sp) (LF sp).
Hypothesis LIokF : forall sp, valid_sp sp -> lib_iface_ok (LayF sp) scfg (HIF sp) (LStF sp).
Hypothesis LSXF : forall sp, valid_sp sp -> forall g M, ls_ok (LStF sp) g M -> exists reg : bool, ax_block M reg.
Hypothesis HINIT : forall sp a0s path envp uid hw rdraw tid regs mem brk mbase,
valid_sp sp -> valid_brk RSEGS brk -> valid_mmap_base mbase -> valid_argv [a0s; path] -> valid_envp envp ->
(0 < bv_unsigned tid < 2 ^ 22)%Z -> main_entry sp [a0s; path] envp uid hw rdraw tid regs mem ->
hi_heap (HIF sp) [] cr0 mem (mkVmMapsFull (segments_reserved RSEGS) [] [] brk brk source_alloc_limit mbase sp).
Hypothesis Hfs : sc_fs scfg = true.
Hypothesis Hbudget : forall sp n, valid_sp sp -> 0 <= n < 67108864 ->
cred (LF sp) (hl_k_per_malloc (LF sp) + 4 * fst (ll_credit (LayF sp) n))
(n + hl_b_overhead (LF sp) + 4 * snd (ll_credit (LayF sp) n)) 0 (debit (LF sp) cr0 65536).
Definition src_realizes_stmt2 : Prop :=
forall sp brk mbase (rdraw : EntryDraw) (inp : ProcInput),
valid_sp sp -> valid_brk RSEGS brk -> valid_mmap_base mbase ->
entry_stack_fits sp (in_argv inp) (in_envp inp) ->
valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> valid_fs (in_fs inp) -> valid_creds inp ->
srealizes RSEGS scfg
(init_config RSEGS Plain.M.init_pc Plain.M.phdrs sp brk mbase rdraw source_alloc_limit inp)
(spec (in_argv inp) (in_fs inp)).
Lemma cred_credit_ok : ltac2:(TCodec.tc2 tcn__Js0DrvMain "Q0'D'<&Q9zr2%3221&Fr5%211%7261&Er6%211%;2:1&Jr7&CvQ@+RPP0%33421%6559=A1&Br8%23165p041p0<1p0A1p0F1p0G1p2L1pLM1pNO1").
Proof.
intros L Kc Bc HK HB Hk Hb [C1 C2]. unfold debit, credit_ok, CAPk in *. cbn [fst snd] in C1, C2. rewrite Z.pow_0_r in C2. lia.
Qed.
Theorem src0_realizes_spec : ltac2:(TCodec.tc2 tcn__Js0DrvMain "1&K").
Proof.
unfold src_realizes_stmt2. intros sp brk mbase rdraw inp Hsp Hbrk Hmb Hfits Hva Hve Hvfs Hcreds.
apply ref_startup; try assumption.
intros tid regs mem Htid ME.
rewrite with_tid_init_model_E.
set (RE := run_env_of inp).
destruct inp as [argv envp fsi stdin0 uid gid groups net nofile sigmask hw abt va urnd tmp0]; unfold in_fs in *; cbn [in_image_fs in_tmp] in *; set (fs0 := fs_seed_tmp fsi tmp0) in *; clearbody fs0.
cbn [in_argv in_envp in_fs in_stdin in_uid in_hwcap] in *.
assert (Huid : bv_unsigned uid < 2 ^ 32) by (destruct Hcreds as [Hu _]; unfold valid_id in Hu; cbn [in_uid] in Hu; lia).
clearbody RE. clear Hcreds.
pose proof (HIokF sp Hsp) as HIok. pose proof (DLF sp Hsp) as DL. pose proof (DLLF sp Hsp) as DLL. pose proof (LIokF sp Hsp) as LIok. pose proof (LSXF sp Hsp) as LSX.
set (L := LF sp) in *. set (HI := HIF sp) in *. set (Lay := LayF sp) in *. set (LSt := LStF sp) in *.
pose proof (dl_k L sp DL) as Hkpm. pose proof (dl_b L sp DL) as Hovh.
assert (Hcr65536 : credit_ok L cr0 65536).
{ destruct (dll_credit_pos Lay L DLL 0 ltac:(lia)) as [P1 P2]. pose proof (Hbudget sp 0 Hsp ltac:(lia)) as HB0.
fold L Lay in HB0. refine (cred_credit_ok L _ _ _ _ Hkpm Hovh HB0); lia. }
destruct argv as [|a0s [|path [|x l]]].
- apply (ref_usage_w scfg sp [] envp uid hw rdraw tid regs mem brk mbase fs0 stdin0 _ Hva Hve Hsp Htid ME Hfits). cbn; lia.
- apply (ref_usage_w scfg sp [a0s] envp uid hw rdraw tid regs mem brk mbase fs0 stdin0 _ Hva Hve Hsp Htid ME Hfits). cbn; lia.
- cbn [spec].
pose proof (HINIT sp a0s path envp uid hw rdraw tid regs mem brk mbase Hsp Hbrk Hmb Hva Hve Htid ME) as HH0. fold HI in HH0.
destruct (Nat.leb_spec0 4096 (length path)) as [Hlong|Hshort].
+ apply (ref_open_fail_toolong_w scfg sp a0s path envp uid hw rdraw tid regs mem brk mbase fs0 stdin0 _ Hva Hve Hsp Htid ME Hfits Hlong).
+ destruct (list_byte_eqb path []) eqn:Hemp.
* apply list_byte_eqb_iff in Hemp.
apply (ref_open_fail_empty_w scfg sp a0s path envp uid hw rdraw tid regs mem brk mbase fs0 stdin0 _ Hva Hve Hsp Htid ME Hfits Hemp).
* assert (Hne : path <> []) by (intros E; apply list_byte_eqb_iff in E; rewrite E in Hemp; discriminate).
assert (HKA : open_err_k scfg sp a0s path envp hw rdraw tid mem (mkVmMapsFull (segments_reserved RSEGS) [] [] brk brk source_alloc_limit mbase sp)
fs0 stdin0 (t_die (msg_cannot_open path) fs0)).
{ unfold open_err_k. intros e vals R M He HL P0 P38 P2 HR HK HA.
exact (ref_open_fail_errno scfg sp a0s path envp uid hw rdraw tid regs mem brk mbase fs0 stdin0 source_alloc_limit Hva Hve Hsp ME Hfits
e vals R M He HL P0 P38 P2 HR HK HA). }
replace (0x33bac%bv : word) with (Z_to_bv 64 0x33bac) by (apply bv_eq; reflexivity).
destruct (list_byte_eqb path dot_path) eqn:Hdot.
--
apply list_byte_eqb_iff in Hdot.
pose proof (drv_dir scfg L HI HIok sp a0s path envp uid hw rdraw tid regs mem _ fs0 stdin0 cr0 Hva Hve Hsp Htid ME Hfits Hfs Hdot DL HH0 Hcr65536
_ HKA) as HD.
rewrite Hdot in HD |- *. exact HD.
-- assert (Hnd : path <> dot_path) by (intros E; apply list_byte_eqb_iff in E; rewrite E in Hdot; discriminate).
assert (Hppl : openat_plain_name path = true).
{ destruct Hva as (_ & _ & _ & _ & Htl). cbn [tl] in Htl. inversion Htl as [|p' l' [Hsl Hdd] _]; subst.
unfold openat_plain_name, path_is_dirref. rewrite Hsl, Hdd.
lazymatch goal with |- context [path_eqb path ?d] => destruct (path_eqb path d) eqn:E; [|reflexivity] end.
exfalso. apply Hnd. apply path_eqb_eq in E. rewrite E. reflexivity. }
destruct (fs_lookup fs0 path) as [fdata|] eqn:Hlk.
++
apply (drv_open scfg L HI HIok sp a0s path envp uid hw rdraw tid regs mem _ fs0 stdin0 fdata cr0 Hva Hve Hsp Htid ME Hlk Hne Hppl Hfs
ltac:(lia) DL HH0 Hcr65536 _ _ HKA); [| apply t_body_nil].
set (PLv := Z.max 0 (Z.min (PL fdata) 67108863)).
assert (HPLv : 0 <= PLv < 67108864) by lia.
destruct (dll_credit_pos Lay L DLL PLv ltac:(lia)) as [CP1 CP2].
apply (drv_file scfg L HI HIok sp a0s path envp uid hw rdraw tid mem
fs0 stdin0 fdata cr0 Hva Hve Hsp Htid Hlk ltac:(lia) DL
(hl_k_per_malloc L + 4 * fst (ll_credit Lay PLv)) (PLv + hl_b_overhead L + 4 * snd (ll_credit Lay PLv))
ltac:(lia) ltac:(lia) (t_body fdata fs0) (t_body_nil fdata fs0)).
**
intros Hlt CAP crC HCAP HltC HK1 HB1.
destruct (Nat.lt_ge_cases (length fdata) 6) as [Hs|Hge6].
{ rewrite (t_body_short fdata fs0) by (unfold MAX_INPUT; lia).
exact (hdr_short scfg L HI HIok sp a0s path envp uid hw rdraw tid mem fs0 stdin0 fdata Hva Hve Hsp Htid ltac:(lia) DL CAP crC Hs). }
destruct (Z.lt_ge_cases (Z.of_nat (length fdata)) (6 + CFG fdata)) as [Hov|Hok].
{ rewrite (t_body_overrun fdata fs0) by (unfold MAX_INPUT; lia).
exact (hdr_overrun scfg L HI HIok sp a0s path envp uid hw rdraw tid mem fs0 stdin0 fdata Hva Hve Hsp Htid ltac:(lia) DL CAP HCAP crC HltC Hge6 Hov). }
rewrite (t_body_ok fdata fs0) by (unfold MAX_INPUT; lia).
apply (hdr_ok scfg L HI sp a0s path envp uid hw rdraw tid mem fs0 stdin0 fdata Hva Hve Hsp ltac:(lia) DL CAP HCAP crC HltC Hok);
[| apply t_emit_has_nil].
assert (HPLeq : PL fdata = PLv) by (unfold PLv; rewrite !PL_eq; pose proof (CFG_range fdata); lia).
apply (drv_target scfg L HI HIok sp a0s path envp uid hw rdraw tid mem (mkVmMapsFull (segments_reserved RSEGS) [] [] brk brk source_alloc_limit mbase sp) fs0 stdin0 fdata Hva Hve Hsp Htid ltac:(lia) DL CAP HCAP crC HltC Hok);
[ intros HPLp; unfold credit_ok; rewrite HPLeq; lia | | apply t_emit_has_nil].
apply (drv_loop scfg L HI HIok sp a0s path envp uid hw rdraw tid regs mem (mkVmMapsFull (segments_reserved RSEGS) [] [] brk brk source_alloc_limit mbase sp) fs0 stdin0 fdata Hva Hve Hsp Htid ME ltac:(lia) DL CAP HCAP crC HltC
Lay LSt DLL LIok LSX Huid Hfits Hok).
pose proof (CALLS_range fdata) as HCL.
unfold credit_le, credit_scale, cr1. rewrite HPLeq. cbn [fst snd].
destruct (PLv =? 0)%Z eqn:EP; unfold debit; cbn [fst snd]; split; nia.
**
intros Hge. unfold refuse_at. rewrite (t_body_refused fdata fs0) by (unfold MAX_INPUT; lia).
exact (drv_refuse scfg HI sp a0s path envp hw rdraw tid mem fs0 stdin0 fdata Hsp Htid ltac:(lia)).
** pose proof (Hbudget sp PLv Hsp HPLv) as HB. fold L Lay in HB. exact HB.
++ replace (Z_to_bv 64 0x33bac) with (0x33bac%bv : word) by (apply bv_eq; reflexivity).
apply (ref_open_fail_absent_w scfg sp a0s path envp uid hw rdraw tid regs mem brk mbase fs0 stdin0 _ Hva Hve Hsp Htid ME Hfits ltac:(lia) Hne Hppl Hlk).
- apply (ref_usage_w scfg sp (a0s :: path :: x :: l) envp uid hw rdraw tid regs mem brk mbase fs0 stdin0 _ Hva Hve Hsp Htid ME Hfits). cbn; lia.
Qed.
End Main.
End FPX_1.

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
SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4 LibKnowFrame
Spec LibWritev RefNodes RefMemcpyLib RefReadLib Js0Startup Js0MainEntry Hoare MemSplit
HeapIface DrvKit Js0Drv_defs Js0DrvLib Js0DrvA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Import SX2. Import SX2S.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Js0DrvB () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Nat."; "Corelib.Init.Peano."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.Fs."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.DrvKit."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Js0DrvA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Js0DrvB.FPX_1.DrvB."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Js0DrvLib."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Js0Drv_defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Js0MainEntry."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.RunEnv."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2Sound.SX2S."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymRun."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A"; "1None"; "1O"; "1Some"; "1app"; "1bool"; "1cons"; "1length"; "1list"; "1nat"; "1nil"; "1option"; "1prod"; "1true"; "2False"; "2and"]; ["2eq"; "2not"; "3add"; "4le"; "4lt"; "5firstn"; "5nth"; "6Z"; "0E"; "0ENVb"; "0HI"; "0L"; "0LB"; "7Fs"; "8store_ok"; "9FdEntry"]; ["9FdFile"; "9Model"; "9VmMaps"; "9fd_insert"; "9fd_lookup"; "9fd_remove"; "9m_fds"; "9m_fs"; "9with_fds"; ":bvmap"; "0M"; "0R"; "0RE"; ";wbytes"; "<find_nz"; "<log_in_b"]; ["<regions_ok"; "=credit"; "=hi_heap"; ">fds0"; ">model1"; "?CPout_stage"; "?IMG_NOSTAGE"; "?keep_stage"; "?model1o"; "?model2"; "@IMG_W"; "@hz"; "@sub_block"; "AIMG_RW"; "Bauxvp"; "Brnd"]; ["Cgetr"; "Crdn"; "DmkModelE"; "EELit"; "Eedenot"; "Eenv"; "Eexpr"; "Ekentry"; "Esentry"; "Fknow_ok"; "Fmem_denot"; "Fregs_ok"; "Gvals_ev"; "Hloaded_segments"; "IIn"; "Jadd"]; ["Jle"; "Jlt"; "Jof_nat"; "Jpow"; "0VM"; "0a"; "0a0s"; "0above"; "0bls"; "0bs"; "0cr"; "0data"; "0envv"; "0ext"; "0fs0"; "0i"]; ["0j"; "0kn"; "0log"; "0m"; "0n"; "0nb"; "0off"; "0off'"; "0path"; "0sp0"; "0sr"; "0stdin0"; "KZ_to_bv"; "Kbv"; "Kbv_unsigned"; "0tid"]; ["0vals"; "0x"]]).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Tactic Notation "run_block" constr(scr) constr(NX) := run_block_gen FUEL STOPS scr NX false.
Tactic Notation "run_block_keep" constr(scr) constr(NX) := run_block_gen FUEL STOPS scr NX true.
Section FPX_1. Context {fx : PropExec.FPState}.
Variable scfg : SpuriousCfg.
Lemma vals_lo : ltac2:(TCodec.tc2 tcn__Js0DrvB "Q0'8'S=yR0%211%411'9'Cr2&7r4%2271%5241&Dr3%2271'@&R<&4&Er6%23A;1r5%53C21%721:%825;%:3F21p0<1p0@1pV2G1pV:H1pULJ1pW2K1").
Proof.
intros vals ext n j Hn Hj. unfold vals_ev. rewrite app_nth1 by (rewrite length_firstn; lia).
rewrite nth_firstn. replace (j <? n)%nat with true by (symmetry; apply Nat.ltb_lt; exact Hj). reflexivity.
Qed.
Lemma vals_hi : ltac2:(TCodec.tc2 tcn__Js0DrvB "Q2'8'S=yR0%211%411'9'Cr2&7r4%2271%5241'@&R<&4&Er3r5%33?21%53@1:&B%125>%9231&F&S<z%22H1%44HDB1%@3I61p0B1pV0I1pV:J1pULL1pW2M1").
Proof.
intros vals ext n i Hn. unfold vals_ev. rewrite app_nth2 by (rewrite length_firstn; lia).
rewrite length_firstn. replace (n + i - Nat.min n (length vals))%nat with i by lia. reflexivity.
Qed.
Lemma len_lay : ltac2:(TCodec.tc2 tcn__Js0DrvB "K'8'S=yR0%211%411'9'Cr1&7r3%2271%5241'@&4&Er2r4%33>21%53?19%;2@1&B%126;%:3A31p0<1pV:C1pULE1pW2F1").
Proof. intros. rewrite length_app, length_firstn. lia. Qed.
Lemma regs_ok_by_nth : ltac2:(TCodec.tc2 tcn__Js0DrvB "Q>'R5'8'R6%211&Q9y5'S=yR0%211%5241'9'?&D(2r1%3221uQ0%5231%7231'@&R0r3&S<&RBr2%211%42E1%7261&R4r5&Fr4(R3z%211%54Q1;41%8271%B3M:1p0D1pV0M1&R;%13:DAp031pRHQ21pVFQ91pQBQ=1").
Proof.
intros E sr R H r. unfold sr_get. destruct (bv_eqb r 0) eqn:Hr0.
- assert (r = 0%bv) by (apply bv_eq; unfold bv_eqb in Hr0; lia). subst r. cbn [edenot]. reflexivity.
- assert (Hnz : ridx r <> 0%nat).
{ intros Hc. assert (r = 0%bv) by (rewrite <- (ridx_roundtrip r), Hc; apply bv_eq; reflexivity). subst r.
rewrite bv_eqb_refl in Hr0. discriminate. }
pose proof (H (ridx r) ltac:(pose proof (ridx_range r); lia)) as Hx. rewrite ridx_roundtrip in Hx. exact Hx.
Qed.
Lemma store_ok_of_defined : ltac2:(TCodec.tc2 tcn__Js0DrvB "QL'S=yR0%211';y8%511%311pW451'G'9&R@zr2%3221&R?r3&RB%115%4231&RC+2+R0%3221%=251'?r1%@2?1&RAr4%=11%3251%7251&A'@r7&S<r6%G21I%32Q51%511(1%11Q4%93Q431%;11p0=1pV0Q51'5&N&R=r5%?2QA1%443?1G(=%D3721p091p0Q01p0Q;1pV8Q@1pU<QB1pRFQD1").
Proof.
intros M a m Ha Ham Hdef. destruct m as [|m']; [reflexivity|].
apply store_ok_of_all; [rewrite u_small by lia; lia|].
intros x Hx. rewrite u_small in Hx by lia. unfold wview.
specialize (Hdef (bv_unsigned x - a)%Z ltac:(lia)). replace (a + (bv_unsigned x - a))%Z with (bv_unsigned x) in Hdef by lia.
rewrite Z_to_bv_bv_unsigned in Hdef. destruct (M x); [discriminate | exfalso; apply Hdef; reflexivity].
Qed.
Lemma stage_store_ok : ltac2:(TCodec.tc2 tcn__Js0DrvB "N'S=yR0%211';y8%511%311p051'9&R@&RBr1%211+RPP0%5221'@'5&N&R=r3&S<+fha9%22E1r2%746521(=%;3:21p0=1pV:D1pRFF1").
Proof.
intros M n Hn. eapply (store_ok_window RSEGS M (Z_to_bv 64 0xb5000) _ 212992%nat n 0xb5000 0xe9000);
[reflexivity | reflexivity | lia | exact wseg_5f000 | rewrite u_small by lia; lia | rewrite u_small by lia; lia].
Qed.
Section DrvB.
Context {RE : RunEnv}.
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
Hypothesis Hpne : path <> [].
Hypothesis Hplen : (length path <= 4095)%nat.
Hypothesis DL : drv_layout L sp0.
Let Hsp : (0x7fff80000000 <= bv_unsigned sp0 <= 0x800000000000)%Z := conj (proj1 Hvsp) (proj1 (proj2 Hvsp)).
Let Hal : (bv_unsigned sp0 mod 16 = 0)%Z := proj2 (proj2 Hvsp).
Let LEN : Z := Z.of_nat (length fdata).
Let ENVb (vals : list word) : env := ENV a0s path hw rdraw fdata vals.
Let above (M : word -> option byte) : Prop := above_sp0 sp0 mem0 M.
Definition model2 (VM : VmMaps) : Model := mkModelE fds0 VM stdin0 fs0 None (Some tid) None.
Definition model1o (off : Z) (VM : VmMaps) : Model := mkModelE (fd_insert fds0 (Z_to_bv 64 3) (FdFile path (Z_to_bv 64 off))) VM stdin0 fs0 None (Some tid) None.
Lemma model1_o : ltac2:(TCodec.tc2 tcn__Js0DrvB "@'Q2'@'Q1&QDvQ<vS8vS?vRNvS;r1%76654321&QHz%2214%=3<41pU:?1"). Proof. reflexivity. Qed.
Lemma m1o_fds : ltac2:(TCodec.tc2 tcn__Js0DrvB "N'G'Q2'@'8'<'S=yR0%211'O%5221%711&Q6&QHr2r1%3221%511&Q3&QC&S<+3%22?1(Q0vS8%52B;%3221%93851%I3A;1pU:K1pV>M1").
Proof. reflexivity. Qed.
Lemma m1o_fs : ltac2:(TCodec.tc2 tcn__Js0DrvB ">'G'Q2'@&M&Q7&QHr2r1%3221%511vRN%93821pU:;1pV>=1"). Proof. reflexivity. Qed.
Lemma fds_lookup3 : ltac2:(TCodec.tc2 tcn__Js0DrvB "G'G'@';'O%211&Q4&Q3&QC&S<yR0+3%3221(Q0vS8r1%7261%4231%;3:61%=217(3%12A4%D3A31pV>F1").
Proof. intros. reflexivity. Qed.
Lemma fds_remove3 : ltac2:(TCodec.tc2 tcn__Js0DrvB "I'G'@'8'<'S=yR0%211'O%5221%711&Q5&Q3&QC&S<+3%22:1(Q0vS8r1%62>1%4231%:3961%<217%F3>1;pV>H1").
Proof. intros. reflexivity. Qed.
Lemma with_fds_read : ltac2:(TCodec.tc2 tcn__Js0DrvB "Q>'G'S=yR0%211'Q2'@'Q1&Q8&Q3&QC&S<+3%22:1(Q0vS8r3%62>1%4231%:3961r2%7261%=3391&QHr1%2291%B241&R2vQ<%D3C@8vS;vRN(1%11M(3vS?%22Q01'8y8%Q511%311%911%?8>=B<;961%Q53Q4A1pU:Q71pV@Q91pV>Q=1").
Proof. intros. reflexivity. Qed.
Lemma with_fds_close : ltac2:(TCodec.tc2 tcn__Js0DrvB "@'G'Q2'@'Q1&Q8&QC&QHr2r1%3221%6251&QI%114%;3:31pU:=1pV>?1").
Proof. intros. reflexivity. Qed.
Lemma hiv_facts' : ltac2:(TCodec.tc2 tcn__Js0DrvB "QF'8'S=yR0%211%411'@&R<r1u3%3221&QNvS9vRFvS8vRL%544321%;3=71r2u4%=221&QO%14:987%A3C31'9&R>(6(:%114%335:1%436E1%637G1'?&R@&S>%12Q0Gr5%N21C%42Q31%6241&R?&RC+2+D%3221%5271+R0%6251%?231%A2:1p0C1pV0K1p0M1p0Q41pW2QA1").
Proof. intros vals P3 P4 i Hi. exact (hiv_facts sp0 a0s path envv uid hw rdraw Hva Hve Hvsp Hplen vals P3 P4 i Hi). Qed.
Lemma content_block' : ltac2:(TCodec.tc2 tcn__Js0DrvB "R='8'S=yR0%211%411';y8%611%311p061'R8%;11'G%=16'@&R<r5(2%3221vS9%63A21'5&Q?&RC+2+Q8%3221(:'<'9%221B%411%513&QJr4%=7B994321(=%G3@21&QK&RB&7r3%22Q31%411%63I:1%Q81Q0&R1&R=r7&S<%12Q@Q2%;2Q<A%645421(3%12Q9D%Q93:31&R:vIr9%211r8%5321=r6%>2QM1%H2QIQ@%C4B421%=2QEQB%QE3F21p0=1p0I1p0Q11p0QC1pUHQK1p2QM1pV6QO1pRFR21pW2R81").
Proof.
clear Htid Hplen Hal. intros vals M log A data P0 Hlog HZ Hc. unfold ENVb, ENV.
rewrite (rdn_heap_frame sp0 Hsp vals _ M log A (length data) P0 Hlog HZ). exact Hc.
Qed.
Lemma above_wbytes : ltac2:(TCodec.tc2 tcn__Js0DrvB "Q:'S=yR0%211';y8%511%311p051'G'8%115&R@zr2%3221&R?r3&RB&7%12>6%311%6251&S>vS9%22G1%>241vRGr5%211&Q=r6&S<%12O5r4%53421%911p081p0<1p0H1pUDM1pU<Q01pRFQ21").
Proof.
clear Htid Hplen Hal LEN. intros M a bs Ha Hab HA x Hx. pose proof Hsp as Hsp'. rewrite wbytes_out; [apply HA; exact Hx | rewrite u_small by lia; lia | rewrite u_small by lia; lia].
Qed.
Lemma heap_stagewrite : ltac2:(TCodec.tc2 tcn__Js0DrvB "Q='8'<'G%2211%411&QA'S=yR0%211';y8%511%311p051'Q2%?14&R@&RB&7r1%2291%411+RPP0%7221&QBvJr6r5r4r3%6554321r7&Q=&S<+fha9%22L1%43917%=5<6;19p081p0@1pUDI1pU:K1pRFM1pUFQ61pQJQ81").
Proof.
clear Htid Hplen Hal LEN ENVb. intros LB cr M VM bs Hn HH. pose proof Hsp as Hsp'.
apply (hio_frame L scfg HI HIok LB cr M _ VM HH).
- intros x Hx Hp. apply wbytes_out; rewrite ?u_small by lia; [lia|].
destruct (Z.lt_ge_cases x 0xb6229) as [Hlt|Hge]; [left; exact Hlt|]. right.
destruct (Z.lt_ge_cases x (0xb6229 + Z.of_nat (length bs))) as [Hlt2|Hge2]; [|exact Hge2].
exfalso. destruct Hp as [(_ & _ & Hni)|Hro].
+ apply Hni. rewrite (dl_img_lo L sp0 DL), (dl_img_hi L sp0 DL). split; [lia|]. intros Hs. apply (dl_static L sp0 DL) in Hs. lia.
+ apply (dl_ro L sp0 DL) in Hro. lia.
- intros x Hx. exact (wbytes_grows bs M (Z_to_bv 64 0xb6229) x Hx).
Qed.
Definition IMG_NOSTAGE : list (Z * Z) := [(0x10000, 0xb6229); (0xc6229, 0xc7bbc); (0xc7bc0, 0xe8068); (0xe8410, 0xe9000)]%Z.
Definition CPout_stage (n : Z) (a : Z) : Prop := ~ (0xb6229 <= a < 0xb6229 + n)%Z.
Lemma regions_stagewrite : ltac2:(TCodec.tc2 tcn__Js0DrvB "S3'8'S=yR0%211%411'G'<'9%2213%911%4255%;11'@&R<r4(2%3221vS9%63?21'?&R@z%2218+RPP0%42:1%6231';%11F&Q>r2r6%3221(3r1%22M1%G3841&Dr3&7r9%22Q51%5241&QLvK&S>%Q0268%22Q<1%544A1B%M271p0>1pV<Q=1pV0Q<1&R>(6u3u4(:%11QB%53QC31%63QD51%83QEK1%A2QKQ<%QA2GQ1%C2QM1%Q<231&R?&RC+2+D%3221%5271+R0%6251%QE231%QG2:1p0?1pV0R51'Q@&R=%G1R7&QF&QMvIr8%211&QEr7%211'>q0RD1%=<<R;R5R5QL;O:9631p0?1p0Q91p0R41p0R<1pQJRD1pUBRG1pV:RL1pW2RN1").
Proof.
clear Htid Hplen Hal. intros vals n bls LB P0 Hn Hbl Hhi. pose proof Hsp as Hsp'.
constructor; cbn [ev ENVb ENV]; rewrite ?P0.
- lia.
- lia.
- intros z Hz Hnot. unfold CPout_stage. lia.
- intros z Hz. exfalso. lia.
- intros i nb Hf. destruct (Hbl i nb Hf) as (Hi & HSB). pose proof (sub_block_hz L sp0 DL _ _ _ HSB) as (Z1 & Z2 & Z3).
destruct HSB as (cap & Hnb & Hin & HB). pose proof (hz_of_block_range L sp0 DL _ _ HB) as (Y1 & Y2 & Y3).
split; [lia|]. intros z Hz. unfold CPout_stage. lia.
- intros v b Hf. discriminate.
- intros i Hi. destruct (Hhi i Hi) as [H1 H2]. split; [exact H1|]. split; [exact H2|]. intros z Hz. unfold CPout_stage. lia.
- intros lo hi Hin. unfold IMG_NOSTAGE in Hin.
destruct Hin as [E1|[E1|[E1|[E1|[]]]]]; injection E1 as <- <-; (split; [lia|]); (split; [lia|]); intros a Ha; unfold CPout_stage; lia.
- intros lo hi Hin. unfold IMG_RW in Hin.
destruct Hin as [E1|[E1|[]]]; injection E1 as <- <-; (split; [lia|]); (split; [lia|]); intros Mx d m Hd Hm.
+ eapply (store_ok_window RSEGS Mx (Z_to_bv 64 0xaf000) _ 24576%nat m 0xaf000 0xb5000);
[reflexivity | reflexivity | lia | exact wseg_5a000 | rewrite u_small by lia; lia | rewrite u_small by lia; lia].
+ eapply (store_ok_window RSEGS Mx (Z_to_bv 64 0xb5000) _ 212992%nat m 0xb5000 0xe9000);
[reflexivity | reflexivity | lia | exact wseg_5f000 | rewrite u_small by lia; lia | rewrite u_small by lia; lia].
Qed.
Definition keep_stage (bls : list (nat * Z)) (kn : list kentry) : list kentry :=
kn_keep_g 0 0 0 bls [] [3%nat; 4%nat] IMG_NOSTAGE IMG_RW kn.
Lemma know_stagewrite : ltac2:(TCodec.tc2 tcn__Js0DrvB "SA'8'S=yR0%211%411';y8%611%311p061%:13'<'9'G%3221%?11%5233%A11'R7%C11'@&R<r6(2%3221vS9%63G21&R@&RB&7r5%22H1%411+RPP0%7221%N1F&Q>r2r7%3221(3r1%22M1%G3841'?&Dr3r;%C2Q=1%4231&QLvK&S>%Q0267%22QD1%544A1B%<271p0>1pV<Q=1pV0Q?1&R>(6u3u4(:%11QE%53QF31%63QG51%83QHK1%A2R3Q<%QA2GQ1%C2R51%Q=231&R?&RC+2+D%3221%5271+R0%6251%QF231%Q62:1p0?1pV0R81&R9&R=vIr:%211r9%64521QM%51Q=&Q=&S<+fha9%22RN1%43917&QGr8%221R>%@4?941p0;1p0C1p0Q=1p0R71p0R@1pV4RH1pQJRK1pUBRN1pUDS41pRFS61pW2S<1").
Proof.
clear Htid Hplen Hal. intros vals M bs bls LB kn P0 Hn Hbl Hhi HK.
eapply (know_keep_g_sound RSEGS 0 0 0 bls [] [3%nat; 4%nat] IMG_NOSTAGE IMG_RW (ENVb vals) (CPout_stage (Z.of_nat (length bs))) (fun _ => False)
(regions_stagewrite vals (Z.of_nat (length bs)) bls LB P0 ltac:(lia) Hbl Hhi) M).
- intros x Hx Hout. unfold CPout_stage in Hout. apply wbytes_out; rewrite ?u_small by lia; [lia|lia].
- intros x [].
- apply wbytes_grows.
- exact HK.
Qed.
End DrvB.
End FPX_1.

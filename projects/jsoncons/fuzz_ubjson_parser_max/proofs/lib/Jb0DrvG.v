(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import
PropExec CatExec CatSim StoreOk StreamSim ShapeAlg SpinAlg Hoare AsanAcctShape FileSim SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4
LibTail RefReadLib RefPrintfLib RefNodes HeapIface HeapIfaceA IcptIfaceAB0 DrvKitA DrvNodesLazyK As0DrvKitA Jb0DrvEntry Jb0Drv_defs Jb0DrvLib Jb0DrvRead Jb0DrvA Jb0DrvG_defs.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Import SX2. Import SX2S.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Jb0DrvG () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Nat."; "Corelib.Init.Peano."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.Fs."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Instr."; "LinuxProcessSemantics.Riscv.Prelude."; "LinuxProcessSemantics.Riscv.Sem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanAcct."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.DrvKitA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Jb0DrvA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Jb0DrvG."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Jb0DrvG.FPX_1.DrvG."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Jb0DrvG_defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Jb0DrvLib."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Jb0Drv_defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2Sound.SX2S."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymRun."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A"; "0A0"; "0A2"; "0Bc"; "1O"; "1Some"; "1app"; "1bool"; "1cons"; "1fst"; "1length"; "1list"; "1nat"; "1nil"; "1option"; "1pair"]; ["1prod"; "1snd"; "1true"; "2True"; "2and"; "2eq"; "2not"; "3add"; "4le"; "4lt"; "5firstn"; "5nth"; "5skipn"; "6Z"; "0E"; "0HI"]; ["0K"; "0Kc"; "0L"; "0LB"; "0LK"; "0LK0"; "7file_read"; "8FdEntry"; "8Model"; "8fd_insert"; "8fd_lookup"; "8fd_remove"; "9ALU_ADD"; "9BC_EQ"; "9BC_LTU"; "9M_MUL"]; [":bvmap"; ";alu64"; ";mul_div"; "0M"; "0M'"; "0M0"; "0R"; "<mrestrict"; "=ksubl_b"; "=log_in_b"; "=regions_ok"; ">credit"; ">defined"; ">lb_remove"; "?ablock_range"; "?ahid"]; ["?fframe"; "@ENVA"; "@fds0"; "@file_kA"; "BCAPk"; "BCW0"; "BcredA"; "Bhdr_valsA"; "Blp_atA"; "Brd_atA"; "ArelayV"; "Ccap2_xA"; "CcellCA"; "CknGbaseA"; "CknLP6A"; "CknLPA"]; ["Cwant_xA"; "Ddinv"; "DhzA"; "EIMG_W_A"; "Ekn_blkA"; "Fgetr"; "Frdn"; "GELit"; "GEVar"; "GEnv"; "GKRange"; "GSCBr"; "Gedenot"; "Genv"; "Gexpr"; "Gkentry"]; ["Gsentry"; "Hknow_ok"; "Hmem_denot"; "Hregs_ok"; "Hsc_denot"; "Ienv_agree"; "Ikn_vars_lt"; "Ivals_ev"; "Jloaded_segments"; "KIn"; "Ladd"; "Leqb"; "Lle"; "Llt"; "Lltb"; "Lmin"]; ["Lmodulo"; "Lmul"; "Lof_nat"; "Lpow"; "Lsub"; "Lto_nat"; "0a"; "0ar"; "0b"; "0bs"; "0c"; "0can"; "0cap"; "0cnt"; "0cr"; "0cr0"]; ["0data"; "0e"; "0e'"; "0ebs"; "0ext"; "0fdata"; "0fs0"; "0fx"; "0hi38"; "0hi70"; "0i"; "0j"; "0k"; "0kn"; "0kn6"; "0l"]; ["0len"; "0lo38"; "0lo70"; "0log"; "0m"; "0model"; "0n"; "0n2"; "0off"; "0p0"; "0p1"; "0path"; "0q"; "0r"; "0scfg"; "0sp0"]; ["0sr"; "MZ_to_bv"; "Mbv"; "0t"; "0u"; "0vals"; "0w"; "0x38"; "0x48"; "0x70"; "0z"]]).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Definition gr (R : bvmap 5 word) (i : nat) : word := getr R (Z_to_bv 5 (Z.of_nat i)).
Definition relayV (vals : list word) (R : bvmap 5 word) (x38 x48 x70 : word) (ext : list word) : list word :=
let z := Z_to_bv 64 0 in
[vals_ev vals 0; vals_ev vals 1; vals_ev vals 2; vals_ev vals 3; vals_ev vals 4; vals_ev vals 5]
++ map (gr R) (seq 0 32)
++ [x38; z; z; z; z; z; z; z; z; z; x48]
++ [z; z; z; z; z; z; z; z; z; z; z; z; z; z; z; z; z; z; z; z; z; x70]
++ ext.
Lemma relayV_len : ltac2:(TCodec.tc2 tcn__Jb0DrvG "O';'U2yR0%211%411&Q@y5%2214'E'<&:&R:r6r5r4r3r2r1%76654321%92@1&GuR7%<2C5%3221%@3?51pX:E1pZDG1pZBH1pZ@I1pS>F1pZ<J1").
Proof. intros. reflexivity. Qed.
Lemma relayV_lo : ltac2:(TCodec.tc2 tcn__Jb0DrvG "Q3';'U2yR0%211%411&Q@y5%2214'<&Ir1u6%3221'E&S7&R:r8r7r6r5r4r3%76654321r2%:221%;292%=3G21p0?1pXHD1pX:I1pZDK1pZBL1pZ@M1pS>J1pZ<N1").
Proof. intros vals R x38 x48 x70 ext j Hj. do 6 (destruct j as [|j]; [reflexivity|]). lia. Qed.
Lemma relayV_38 : ltac2:(TCodec.tc2 tcn__Jb0DrvG "K';'U2yR0%211%411&Q@y5%2214'E&S7&R:r6r5r4r3r2r1%76654321uQ6%:221%<3A17pX:A1pZDC1pZBD1pZ@E1pS>B1pZ<F1"). Proof. reflexivity. Qed.
Lemma relayV_48 : ltac2:(TCodec.tc2 tcn__Jb0DrvG "K';'U2yR0%211%411&Q@y5%2214'E&S7&R:r6r5r4r3r2r1%76654321uQ@%:221%<3A16pX:A1pZDC1pZBD1pZ@E1pS>B1pZ<F1"). Proof. reflexivity. Qed.
Lemma relayV_70 : ltac2:(TCodec.tc2 tcn__Jb0DrvG "K';'U2yR0%211%411&Q@y5%2214'E&S7&R:r6r5r4r3r2r1%76654321uR6%:221%<3A15pX:A1pZDC1pZBD1pZ@E1pS>B1pZ<F1"). Proof. reflexivity. Qed.
Lemma relayV_71 : ltac2:(TCodec.tc2 tcn__Jb0DrvG "O';'U2yR0%211%411&Q@y5%2214'E&S7&R:r7r6r5r4r3(8r2r1%33@21%:6987651uR7%=221%?3D16pX:D1pZ>F1pZDG1pZBH1pZ@I1pS>F1pZ<J1"). Proof. reflexivity. Qed.
Lemma relayV_agree : ltac2:(TCodec.tc2 tcn__Jb0DrvG "Q6'<';'U2y8%211%411p061yR0%611%811&Q@y5%2214&S5u6(RI&S7r6%211r7%5221&R:r5r4r3r2r1%66:54321%<11%>21:%A3@:1pX:F1pZDH1pZBI1pZ@J1pS>G1pZ<K1pX8O1").
Proof. intros. split; [|reflexivity]. intros n Hn. cbn [ev]. symmetry. apply relayV_lo. exact Hn. Qed.
Lemma relay_know6 : ltac2:(TCodec.tc2 tcn__Jb0DrvG "R0'<';'U2y8%211%411p061yR0%611%811&Q@y5%2214'>%11:p071'RO%@11&S1&S8(RI&S7r9%211r:%5221r3r2%:49321'E'7&QH%1265(B%53421&S6u6%221;%93815&R:r<r;r8r7%5643DF21%H11r=%K221r6r4%Q04O321p0=1p0B1p0I1pXNQ51pXLQ61pS8Q91pX:Q@1pZDQB1pZBQC1pZ@QD1pS>QA1pZ<QE1pX8QI1").
Proof.
intros ebs vals R x38 x48 x70 ext M kn kn6 HK Hsub Hv.
eapply (know_ok_agree ASEGS 6); [apply relayV_agree | exact Hv |].
eapply ksubl_sound; [exact HK | exact Hsub].
Qed.
Lemma knLPA_split : ltac2:(TCodec.tc2 tcn__Jb0DrvG "='E';'RO%211&R?&6&RDuQ@+RPP0%3221&R>%63921%<3981"). Proof. reflexivity. Qed.
Lemma knGbaseA_sub : ltac2:(TCodec.tc2 tcn__Jb0DrvG "B'E'7&QH&6'RO&RDuQ@+RPP0%3221(8&R<&R>%33821%:3951&R=%=221(B%A3@21"). Proof. vm_compute. reflexivity. Qed.
Lemma knLP6A_vars : ltac2:(TCodec.tc2 tcn__Jb0DrvG "8'E'7&S6u6&R>%3221(B%73621"). Proof. vm_compute. reflexivity. Qed.
Lemma mod_of_decompZ : ltac2:(TCodec.tc2 tcn__Jb0DrvG "O'M&S=zr3%3221'D&S<r2%2261r4%9231%6231'Er6&S:&SAr5%2218%421?%73C61&S@r7%2219%;3G1>p051p0>1p0F1pYLK1pYJL1pWBM1pW>N1").
Proof. intros a b q r Hb Hr He. symmetry. apply (Zmod_unique a b q r); lia. Qed.
Lemma sub_as_addA : ltac2:(TCodec.tc2 tcn__Jb0DrvG "Q8'M'D&S<zr1%3221r2%5231%7231&S=r3&SC+2+R0%3221%6251'E'U2yR0%211&QA(Q<&U1r4%2261&QB(Q?-1%62:1%72;C%54<421%;3:71&SD%12:G%<2@1%C3@41p0E1p0M1pY0Q61pWFQ71").
Proof.
intros c l Hl Hc. apply bv_eq. rewrite alu_add. unfold v_add. rewrite u_mul64.
rewrite !Z_to_bv_unsigned. change (bv_modulus 64) with (2 ^ 64).
rewrite (bv_wrap_small 64 l) by (change (bv_modulus 64) with (2 ^ 64); lia).
rewrite (bv_wrap_small 64 c) by (change (bv_modulus 64) with (2 ^ 64); lia).
unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
replace ((-1) mod 2 ^ 64) with (2 ^ 64 - 1) by reflexivity.
destruct (Z.eq_dec l 0) as [->|Hnz].
- rewrite Z.mul_0_r, Z.sub_0_r. cbn [Z.modulo Z.add]. rewrite Z.add_0_r. reflexivity.
- rewrite (mod_of_decompZ ((2 ^ 64 - 1) * l) (2 ^ 64) (l - 1) (2 ^ 64 - l)) by lia.
rewrite (mod_of_decompZ (c + (2 ^ 64 - l)) (2 ^ 64) 1 (c - l)) by lia.
rewrite (mod_of_decompZ (c - l) (2 ^ 64) 0 (c - l)) by lia.
reflexivity.
Qed.
Lemma mul2_litA : ltac2:(TCodec.tc2 tcn__Jb0DrvG "O'M&S<zr1%3221&S=&SA+2r2%3221&SC+R0%2251%8241'E'U2yR0%211&QB(Q?&U1%125>r3%3271%648531%C2B3%62:1%=3:31p0?1p0I1pWFN1").
Proof. intros c H0 H1. apply bv_eq. rewrite u_mul64. rewrite !u_small by lia. rewrite Z.mod_small by lia. reflexivity. Qed.
Lemma firstn_app_skipnA : forall {X} (l : list X) (a b : nat), firstn a l ++ firstn b (skipn a l) = firstn (a + b) l.
Proof.
intros X l a. revert l. induction a as [|a IH]; intros l b; [reflexivity|].
destruct l as [|x l]; cbn; [rewrite firstn_nil; reflexivity|]. rewrite IH. reflexivity.
Qed.
Lemma file_read_litA : ltac2:(TCodec.tc2 tcn__Jb0DrvG "Q9';'U2y8%211%411'M'D&S<zr2%3221&S=&SC+2+R0%3221%5271%;271'E&Q6r5&U1yR0r4%3221r3%5241%83731&J&SE%115&L%319%23N1=%63O41%A3O81p0C1p0D1pWLQ11pYBQ21pX2Q41").
Proof. intros. rewrite file_read_unguarded, !word_to_nat_lit by lia. reflexivity. Qed.
Lemma length_readA : ltac2:(TCodec.tc2 tcn__Jb0DrvG "Q;';'U2y8%211%411'M&S<zr2%3221r3&SB&:r4%22;1%411%:261%;2:7'E&J&SE%118&Lr5%411r6%43G21%83H61%@2I1%B11&S?&SD%D2M7%F11%321;%52F1%B3O71p0D1p0F1p0N1pWLQ31pYBQ41pX2Q61").
Proof. intros. rewrite length_firstn, length_skipn. lia. Qed.
Lemma firstn_len_firstnA : forall {X} (l : list X) w, firstn (length (firstn w l)) l = firstn w l.
Proof.
intros X l. induction l as [|x l IH]; intros w; [rewrite !firstn_nil; reflexivity|].
destruct w as [|w]; [reflexivity|]. cbn. rewrite IH. reflexivity.
Qed.
Lemma lb_remove_2A : ltac2:(TCodec.tc2 tcn__Jb0DrvG "N'M&F'Er4r2%33521%511';'@%1299%311&QMr3(8(?r5%24@@1=%34AA5=(=%11:%73;31%83<51%;2:1%:3>74%F3>21p0C1pY>J1p2K1pY@L1p6M1").
Proof.
intros A2 n2 A n H. cbn [lb_remove fst]. replace (A2 =? A) with false by (symmetry; apply Z.eqb_neq; exact H).
rewrite Z.eqb_refl. reflexivity.
Qed.
Lemma regs_ok_by_nth : ltac2:(TCodec.tc2 tcn__Jb0DrvG "Q>'RM';'RN%211&Q@y5'U2yR0%211%5241'<'D&I(4r1%3221uQ0%5231%7231'E&REr3&U1&SBr2%211%42E1%7261&RLr5&Kr4(RGz%211%54Q1;41%8271%B3M:1p0D1pXFM1&S3%13:DAp031pS>Q21pZ2Q91pQNQ=1").
Proof.
intros E sr R H r. unfold sr_get. destruct (bv_eqb r 0) eqn:Hr0.
- assert (r = 0%bv) by (apply bv_eq; unfold bv_eqb in Hr0; lia). subst r. cbn [edenot]. reflexivity.
- assert (Hnz : ridx r <> 0%nat).
{ intros Hc. assert (r = 0%bv) by (rewrite <- (ridx_roundtrip r), Hc; apply bv_eq; reflexivity). subst r.
rewrite bv_eqb_refl in Hr0. discriminate. }
pose proof (H (ridx r) ltac:(pose proof (ridx_range r); lia)) as Hx. rewrite ridx_roundtrip in Hx. exact Hx.
Qed.
Lemma lb_remove_hdA : ltac2:(TCodec.tc2 tcn__Jb0DrvG "C'M';'@%1233%311'E&QMr3(8(?r2%24;;41r1%53:21%8271%:3;13pY0<1pY>A1p2B1").
Proof. intros A n l. cbn [lb_remove fst]. rewrite Z.eqb_refl. reflexivity. Qed.
Lemma lb_remove_1A : ltac2:(TCodec.tc2 tcn__Jb0DrvG "C'M'E';'@%1244%311&QMr2(8(?r1%24;;41(=%119%63:31%9281%?3;13pY>A1p2B1").
Proof. intros A n. cbn [lb_remove fst]. rewrite Z.eqb_refl. reflexivity. Qed.
Section FPX_1. Context {fx : PropExec.FPState}.
Variable scfg : SpuriousCfg.
Section DrvG.
Variable L : asan_layout.
Variable ar : asan_run.
Variable C : asan_statics_cells.
Variable IL : icpt_layout.
Variable HI : asan_iface.
Hypothesis HIok : asan_iface_ok L ar C scfg HI.
Hypothesis ICok : aicpt_ok L ar IL scfg HI.
Hypothesis ILY : as0_icpt_layout IL.
Variable sp0 : word.
Hypothesis Hsp : 0x7fff80000000 <= bv_unsigned sp0 <= 2 ^ 47.
Hypothesis Hal : bv_unsigned sp0 mod 16 = 0.
Hypothesis DL : drv_layoutA L ar IL sp0.
Hypothesis Hcells : incl RD_CELLS (asc_cells C).
Hypothesis HCOST : 0 <= hl_k_per_malloc L /\ 0 <= hl_b_lin L /\ 0 <= hl_b_overhead L.
Variables a0s path : list byte.
Variable fs0 : Fs.Fs.
Variable fdata : list byte.
Variables p0 p1 can : word.
Variable M0 : word -> option byte.
Hypothesis M0_def : defined M0 (bv_unsigned sp0) (ar_stack_top ar - bv_unsigned sp0).
Hypothesis Hfile : fs_lookup fs0 path = Some fdata.
Variable LK0 : list fframe.
Variable A0 : list (Z * Z).
#[local] Notation dinvA := (dinv ar HI sp0 M0).
#[local] Notation ENVG := (ENVA fdata).
Let LEN : Z := Z.of_nat (length fdata).
Definition hdr_valsA (vals : list word) : Prop :=
vals_ev vals 0 = sp0 /\ vals_ev vals 1 = p0 /\ vals_ev vals 2 = p1 /\ vals_ev vals 3 = can.
Lemma hdr_relayA : ltac2:(TCodec.tc2 tcn__Jb0DrvG "J';'U2yR0%211%411&Q@y5%2214&R7r6%211&R:r7r5r4r3r2%66584321%:11p091pX:@1pZDB1pZBC1pZ@D1pS>A1pZ<E1").
Proof. intros vals R x38 x48 x70 ext H. unfold hdr_valsA. rewrite !relayV_lo by lia. exact H. Qed.
Lemma hdr_appA : ltac2:(TCodec.tc2 tcn__Jb0DrvG "F';'U2yR0%211%411&R7r2%211'Hu6&:r3%2291%5241&6r4%23=15%<11p051p0<1pX:@1pZ<A1").
Proof. intros vals ext H HL. unfold hdr_valsA. rewrite !vals_ev_app_l by lia. exact H. Qed.
Definition mdl3 (model : Model) (off : Z) : Prop :=
m_fds model = fd_insert fds0 (Z_to_bv 64 3) (FdFile path (Z_to_bv 64 off)) /\ m_fs model = fs0.
Lemma fds_lookup3A : ltac2:(TCodec.tc2 tcn__Jb0DrvG "B'Q7'E'>%113&Q:&Q9&R2&U1yR0+3%3221r1%73621%9213(5%12?4%?3=31pX4A1").
Proof. intros. reflexivity. Qed.
Lemma fds_remove3A : ltac2:(TCodec.tc2 tcn__Jb0DrvG "D'Q7'E';'@'U2yR0%211%4217%611&Q;&Q9&R2&U1+3%2291r1%63521%8213%A3:17pX4C1").
Proof. intros. reflexivity. Qed.
Lemma fds_ins3A : ltac2:(TCodec.tc2 tcn__Jb0DrvG "F'Q7'E';'@'U2yR0%211%4217%611&Q9&R2&U1+3%2281r2%63521r1%83241%93852%B3;21pX6D1pX4E1").
Proof. intros. reflexivity. Qed.
Definition CAPk (k : Z) : Z := 65536 * 2 ^ k.
Variables Kc Bc : Z.
Hypothesis HKc : 0 <= Kc. Hypothesis HBc : 0 <= Bc.
Definition credA (k : Z) (cr : credit) : Prop :=
(10 - k) * hl_k_per_malloc L + Kc <= fst cr
/\ hl_b_lin L * (2 ^ 27 - 2 * CAPk k) + (10 - k) * hl_b_overhead L + Bc <= snd cr.
Lemma CAPk_S : ltac2:(TCodec.tc2 tcn__Jb0DrvG "C'M&S<zr1%3221'E&R4&S:r2+1%3221%511&SA+2%816%3221%;3@51p0=1pXJB1").
Proof. intros k Hk. unfold CAPk. rewrite Z.pow_add_r, Z.pow_1_r by lia. lia. Qed.
Lemma CAPk_range : ltac2:(TCodec.tc2 tcn__Jb0DrvG "C'M'D&S<zr1%3221+:%5231%7231+RPP0&R4r2%211%;241+RPPPP0%=231%?231p091pXJB1").
Proof.
intros k Hk. unfold CAPk. split.
- assert (1 <= 2 ^ k) by (pose proof (Z.pow_le_mono_r 2 0 k); cbn in *; lia). lia.
- pose proof (Z.pow_le_mono_r 2 k 10 ltac:(lia) ltac:(lia)) as H. change (2 ^ 10) with 1024 in H. lia.
Qed.
Lemma CAPk_lt10 : ltac2:(TCodec.tc2 tcn__Jb0DrvG "A'M'D&S<zr1%3221&S=+:%2241%8241&R4r2%211+QPPPP0%<221p061pXJ@1").
Proof. intros k Hk. unfold CAPk. pose proof (Z.pow_le_mono_r 2 k 9 ltac:(lia) ltac:(lia)) as H. change (2 ^ 9) with 512 in H. lia. Qed.
Lemma credA_exit : ltac2:(TCodec.tc2 tcn__Jb0DrvG "J'M&QK'D&S<zr2%3221+:%5231%7231&R6r3%2217vQ1&9%13??4%=231v3&A%13CC8%A231%C251p0:1p0>1pWNG1pXJI1").
Proof. intros k cr Hk [C1 C2]. pose proof (CAPk_range k Hk). destruct HCOST as (H1 & H2 & H3). nia. Qed.
Lemma inv_block1 : ltac2:(TCodec.tc2 tcn__Jb0DrvG "QG';'@'M%2211%411&R0%611&QK'U2yR0%211'>y8%511%311p051'Q8'RAvSGvOvTOvQEr8r7r6r5r4r3%;::987654321&S9(?r2%24NN51r9%53O21'D&QNvQ2%241D<;&QL%13@>=&RB%13F@?%8231%9261p0;1p0B1pY>Q=1pZ:Q>1pY<Q11pS8Q31p2Q?1pWNQ=1pR:Q?1pR8QB1").
Proof.
intros LB LK cr A M model u n D Hin.
destruct (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ (di_inv _ _ _ _ _ _ _ _ _ _ D)) as (WF & _).
destruct (WF (u, n) Hin) as (B & Df & _). cbn [fst snd] in B, Df. split; [exact B|]. split; [exact Df|].
exact (hzA_of_block_range L ar IL sp0 DL _ _ B).
Qed.
Variable K : TSet.
Hypothesis HK0 : K [].
Definition close_kgA (CAP : Z) (crC : credit) (KC : TSet) : Prop :=
forall vals R M (model : Model) A (A1 : Z),
length vals = 71%nat -> hdr_valsA vals -> vals_ev vals 48 = Z_to_bv 64 A1 -> vals_ev vals 70 = Z_to_bv 64 LEN ->
regs_ok (ENVG vals) srGLA R ->
(forall lo hi, lo <= LEN <= hi -> know_ok ASEGS (ENVG vals) (mrestrict (ahid A model) M) (knGA lo hi)) ->
rdn ASEGS M (Z_to_bv 64 A1) (length fdata) = Some fdata ->
dinvA [(A1, CAP)] LK0 crC A M model -> incl A0 A ->
m_fds model = fds0 -> m_fs model = fs0 ->
srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 0x1277c0) M (seg_rom ASEGS)) model) KC.
Definition lp_atA (z : Z) : Prop := forall (k len A1 : Z) vals R M (model : Model) A cr,
0 <= k <= 10 -> 0 <= len <= CAPk k -> len <= LEN -> LEN - len <= z ->
length vals = 71%nat -> hdr_valsA vals ->
vals_ev vals 38 = Z_to_bv 64 (CAPk k) -> vals_ev vals 48 = Z_to_bv 64 A1 -> vals_ev vals 70 = Z_to_bv 64 len ->
regs_ok (ENVG vals) srLPA R -> know_ok ASEGS (ENVG vals) (mrestrict (ahid A model) M) knLPA ->
rdn ASEGS M (Z_to_bv 64 A1) (Z.to_nat len) = Some (firstn (Z.to_nat len) fdata) ->
dinvA [(A1, CAPk k)] LK0 cr A M model -> incl A0 A -> mdl3 model len -> credA k cr ->
srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 0xa7504) M (seg_rom ASEGS)) model) K.
Definition rd_atA (z : Z) : Prop := forall (k len want A1 : Z) vals R M (model : Model) A cr,
0 <= k <= 10 -> 0 <= len < CAPk k -> len <= LEN -> LEN - len <= z ->
want = Z.min (CAPk k - len) 65536 ->
length vals = 72%nat -> hdr_valsA vals ->
vals_ev vals 38 = Z_to_bv 64 (CAPk k) -> vals_ev vals 48 = Z_to_bv 64 A1 -> vals_ev vals 70 = Z_to_bv 64 len ->
vals_ev vals 71 = Z_to_bv 64 want ->
regs_ok (ENVG vals) srRDA R -> know_ok ASEGS (ENVG vals) (mrestrict (ahid A model) M) knLPA ->
rdn ASEGS M (Z_to_bv 64 A1) (Z.to_nat len) = Some (firstn (Z.to_nat len) fdata) ->
dinvA [(A1, CAPk k)] LK0 cr A M model -> incl A0 A -> mdl3 model len -> credA k cr ->
srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 0x62d08) M (seg_rom ASEGS)) model) K.
Definition refuse_kA (KR : TSet) : Prop := forall (A1 : Z) vals R M (model : Model) A cr,
length vals = 71%nat -> hdr_valsA vals ->
vals_ev vals 38 = Z_to_bv 64 67108864 -> vals_ev vals 48 = Z_to_bv 64 A1 -> vals_ev vals 70 = Z_to_bv 64 67108864 ->
regs_ok (ENVG vals) srLPA R -> know_ok ASEGS (ENVG vals) (mrestrict (ahid A model) M) knLPA ->
dinvA [(A1, 67108864)] LK0 cr A M model -> incl A0 A -> mdl3 model 67108864 ->
srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 0xa7504) M (seg_rom ASEGS)) model) KR.
Hypothesis HKC : LEN < 67108864 -> forall CAP crC,
65536 <= CAP <= 67108864 -> LEN < CAP -> Kc <= fst crC -> Bc <= snd crC -> close_kgA CAP crC K.
Hypothesis HREF : 67108864 <= LEN -> refuse_kA K.
Ltac norm_srget := repeat match goal with |- context [sr_get ?sr ?r] =>
let x := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with x end.
Ltac norm_nth := repeat match goal with |- context [nth ?i ?l (ELit 0)] =>
let x := eval vm_compute in (nth i l (ELit 0)) in change (nth i l (ELit 0)) with x end.
Ltac relay1 HR :=
norm_nth;
first [ lia
| reflexivity
| rewrite (reg_val _ _ _ _ HR); norm_srget; cbn [edenot ev ENVA]; reflexivity
| idtac ].
Ltac relay_loop HR i :=
first [ lia | let j := fresh "i" in destruct i as [|j]; [ cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; relay1 HR | relay_loop HR j ] ].
Ltac relay_regs HR := apply regs_ok_by_nth; let i := fresh "i" in let Hi := fresh "Hi" in intros i Hi; relay_loop HR i.
Ltac relay2 HR :=
rewrite (reg_val _ _ _ _ HR); norm_srget; cbn [edenot ev ENVA];
rewrite ?relayV_38, ?relayV_48, ?relayV_70, ?relayV_71; unfold gr;
rewrite ?(reg_val _ _ _ _ HR); norm_srget; cbn [edenot ev ENVA].
Ltac regv1 HR := rewrite (reg_val _ _ _ _ HR); norm_srget; cbn [edenot ev ENVA].
Lemma sc_eq_70_38A : ltac2:(TCodec.tc2 tcn__Jb0DrvG "R0';'U2yR0%211%411'>y8%611%311p061'M'7'E&S7r5uR6%3221&U1r3%22A1%83A41r6uQ6%:221%<3E15'D&S<z%221>&S=&SC+2+R0%3221%52D1%:271&S;r7%221A%K3L1I&S4&S8r9&R1vT5r:%3221(RK(Q=(RH%11Q3%21M%54O421%=4<;71p0?1p0D1p0E1p0Q11p0Q61pZ8Q@1pWJQB1pY2QC1pS8QE1pZ<QK1").
Proof.
intros vals M len cap t P70 P38 Hl Hc Ht. cbn [sc_denot branch_taken edenot ev ENVA]. rewrite P70, P38.
unfold bv_eqb. rewrite !u_small by lia. exact Ht.
Qed.
Lemma want_x_valA : ltac2:(TCodec.tc2 tcn__Jb0DrvG "QC';'U2yR0%211%411'M'E&S7r3uR6%3221&U1r2%22;1%83;41r4uQ6%:221%<3?15'D&S<z%2217%328?%5221&S=&SC+2+R0%3221%52?1&RL&R1vT5r7%3221&R@%6221&SDr5r6%3221%O2Q81%Q53Q861p0>1p0E1p0L1p0Q11pWJQ;1pY2Q<1pZ<Q>1").
Proof. intros vals len cap P70 P38 H1 H2. cbn [want_xA edenot ev ENVA]. rewrite P70, P38. apply sub_as_addA; lia. Qed.
Lemma sc_ltu_wantA : ltac2:(TCodec.tc2 tcn__Jb0DrvG "R5';'U2yR0%211%411'>y8%611%311p061'M'7'E&S7r5uR6%3221&U1r3%22A1%83A41r6uQ6%:221%<3E15'D&S<z%221>r4%42@1%6231&S=&SC+2+R0%3221%52G1&S>&SDr7%22D1+RPP0%5221%Q03Q11N&S4&S8r9&R1vT5r:%3221(RK(Q>&R@(RG%11>%54Q4431%=4<;71p0?1p0G1p0N1p0Q61p0Q;1pZ8QE1pWJQG1pY2QH1pS8QJ1pZ<R01").
Proof.
intros vals M len cap t P70 P38 H1 H2 Ht. cbn [sc_denot branch_taken].
rewrite (want_x_valA vals len cap P70 P38 H1 H2). cbn [edenot]. unfold bv_ltu. rewrite !u_small by lia. exact Ht.
Qed.
Lemma cap2_x_valA : ltac2:(TCodec.tc2 tcn__Jb0DrvG "Q;';'U2yR0%211%411'M'E&S7r2uR6%3221&U1r1%22;1%83;41&S<z%2219&S=&SA+2r3%3221&SC+R0%2251%8241&RL&R1vT5r5%3221&R;%6221r4%@2?1%I2Q21%O3Q241p0<1p0F1p0J1pWJQ41pZ<Q61").
Proof. intros vals cap P70 H1 H2. cbn [cap2_xA edenot ev ENVA]. rewrite P70. apply mul2_litA; lia. Qed.
Lemma know_LP_rangesA : ltac2:(TCodec.tc2 tcn__Jb0DrvG "RA';'U2yR0%211%411'>y8%611%311p061'M'E&S7r8uR6%3221&U1r6%22@1%83@41r9uQ6%:221%<3D15'D&S<z%221>&S=&SC+2+R0%3221%52D1%:271r:%;2G1r7%=231%?231%?235%@26H%B221&S1&S8&R1vT5r>%3221r=&R?%847321r?%8271(8'RO(RJ(RH%11Q<r;%4321I%41Q8%631Q:QA%9381=%:3941%F4E<B1p0?1p0I1p0M1p0Q31p0Q41p0Q@1p0QE1pXBQO1pY4R01pXDR11pY6R21pWJR31pY2R41pS8R61pZ<R<1").
Proof.
intros vals M len cap lo70 hi70 lo38 hi38 P70 P38 Hl Hc H70 H38 HK.
constructor; [|constructor; [|exact HK]]; cbn [kentry_ok edenot ev ENVA]; rewrite ?P70, ?P38, u_small by lia; lia.
Qed.
Definition CW0 (a : Z) : Prop :=
bv_unsigned sp0 - 8388608 <= a < bv_unsigned sp0 \/ (exists lo hi, In (lo, hi) IMG_W_A /\ lo <= a < hi).
Lemma regions_write0 : ltac2:(TCodec.tc2 tcn__Jb0DrvG "Q>';'U2yR0%211%411'<y8%611%811p041'RM(RI&S7r2%211r1%5221'Er3(4%8221vTO%53C21'QJ&S8&SC+2+Q8%3221(='@'M%22K1%411%51M&RC%6255%811&R5'Cq091%B<AF==88764L31p0D1tQNQ1K1pX8Q31pZ<Q91").
Proof.
intros vals ebs E P0. pose proof Hsp as Hsp'.
constructor; cbn [ev E]; rewrite ?P0.
- lia.
- lia.
- intros z Hz Hnot. unfold CW0. left. lia.
- intros z Hz. right. exact I.
- intros i nb Hf. discriminate.
- intros v b Hf. discriminate.
- intros i [].
- intros lo hi Hin. destruct (img_w_client sp0 lo hi Hin) as (_ & _ & _ & _ & _ & H3 & H4).
split; [lia|]. split; [lia|]. intros a Ha. unfold CW0. right. exists lo, hi. auto.
- intros lo hi [].
Qed.
Lemma block_frame0 : ltac2:(TCodec.tc2 tcn__Jb0DrvG "S8';'U2yR0%211%411'<y8%611%811p041'@'M%2211%=11'>%118p0=1'Q8'S0%C11'RM(RI&S7r7%211r6%5221'Er8(4%8221vTO%53M21'7&QI&SC+2+Q8%3221(=%N2Q3M%211%31Q5&RCr3%;7@774321(B%D3>21&QG&QOr5%22G1%421K&S2%623Or4%33<21%N3Q951r:r1%;32Q51%Q23L1?r9r2%211%712%Q73QC21p061pW>R11'D&S<z%221=&S=+R0%Q82Q71%32A1%8251&F&R5%11A%311r;&U1%12RBQ8%311r<%113%QM3R931p081p0=1pW>R@1p0H1p0Q41p0Q?1p0QO1tQNR<R61pY8R>1pY<RA1pS:RC1pS8RD1p2RH1pX8RM1pZ<S31").
Proof.
intros vals ebs A M M' model log E P0 Hlog EQM EQH a Ha HC.
pose proof (regions_write0 vals ebs P0) as RG.
destruct (ahid A model (Z_to_bv 64 a)) eqn:Hh; [apply EQH; exact Hh|].
assert (E1 : M' (Z_to_bv 64 a) = mrestrict (ahid A model) M' (Z_to_bv 64 a)) by (unfold mrestrict; rewrite Hh; reflexivity).
rewrite E1, EQM.
rewrite (mem_denot_frame_Z ASEGS 0 (2 ^ 40) (2 ^ 40) [] [] [] IMG_W_A _ CW0 (fun _ => True) [] RG _ log a Hlog Ha HC).
unfold mrestrict. rewrite Hh. reflexivity.
Qed.
Lemma block_nolog : ltac2:(TCodec.tc2 tcn__Jb0DrvG "QE'RM';'@'M%2211%411'U2yR0%211'>y8%511%311p051'Q8'E&QG&QOr4r1%3221r2%6221&S2r5r3%:261(='S0%211%73641%@3B91'7r6%A319?(B%E3421%=1@%51A%H3K21p041pW>Q11%B1G%:1H%M3Q021pW>Q51p051p0@1pY<Q21pS:Q41pS8Q51p2Q>1pQNQD1").
Proof.
intros E A M M' model EQM EQH a. destruct (ahid A model a) eqn:Hh; [exact (EQH a Hh)|].
cbn [mem_denot] in EQM. pose proof (f_equal (fun f => f a) EQM) as X. cbv beta in X. unfold mrestrict in X. rewrite Hh in X. exact X.
Qed.
Lemma content_block0 : ltac2:(TCodec.tc2 tcn__Jb0DrvG "S=';'U2yR0%211%411'<y8%611%811p041'@'M%2211%=11'>%118p0=1'Q8'S0%C11'RM(RI&S7r;%211r:%5221'Er<(4%8221vTO%53M21'7&QI&SC+2+Q8%3221(=%N2Q3M%211%31Q5&RCr7%;7@774321(B%D3>21&QG&QOr9%22G1%421K&S2r3%724Q0r8%43321%O3Q:61r>r1%<32Q61%Q33M1@r=r2%211%712%Q83QD21p061pW>R21&RB%13Q8E?&S<&SB%11B%321I%QN1R4&RF&S8r?&U1%12R?QJ%54431Q0(5%12R<L%QJ3931%62RDQJ%:4981QN%52R@Q6%QN3=21p051p0@1p0E1p0H1p0Q41p0Q@1p0R01tQNR=R71pWDRJ1pY:RN1pY>RI1pZ:RJ1pY8RC1pY<RF1pS:RH1pS8RI1p2RM1pX8S21pZ<S81").
Proof.
intros vals ebs A M M' model log u n m bs E P0 Hlog EQM EQH (Z1 & Z2 & Z3) Hm HC. pose proof Hsp as Hsp'.
rewrite <- HC. apply rdn_agree. intros j Hj. rewrite u_small by lia.
apply (block_frame0 vals ebs A M M' model log P0 Hlog EQM EQH); [lia|].
intros [HS|(lo & hi & Hin & Hr)]; [lia|].
destruct (img_w_client sp0 lo hi Hin) as (_ & _ & _ & _ & _ & H3 & H4). lia.
Qed.
Section SE.
Local Abbreviation SEC_T_read_okA := (ltac2:(TCodec.tc2 tcn__Jb0DrvG "<'M&R8&SDr1+1%3221%511&R9r2%211p041pZF;1")) (only parsing).
Variable z : ltac:(sec_ty2 constr:(SEC_T_read_okA) 0%nat 0%nat).
Lemma read_okA : ltac:(sec_stmt2 constr:(SEC_T_read_okA) 1%nat 0%nat).
Proof.
intros IH.
unfold rd_atA.
intros k len want A1 vals R M model A cr Hk Hlen HlL Hz Hwant HL HV P38 P48 P70 P71 HR HK HC DI HINC (MF & MS) Hcr.
pose proof Hsp as Hsp'. pose proof Hal as Hal'.
pose proof (CAPk_range k Hk) as HCk.
destruct (inv_block1 _ _ _ _ _ _ _ _ DI (or_introl eq_refl)) as (HBR & HDEF & HZ). pose proof HZ as (Z1 & Z2 & Z3).
pose proof HV as (P0 & P1 & P2 & P3).
assert (Hw : 1 <= want <= 65536 /\ want <= CAPk k - len) by lia.
eapply (aread_site scfg L ar C IL HI HIok ICok ILY sp0 Hsp DL Hcells M0 vals _ srRDA knLPA R M model [(A1, CAPk k)] LK0 cr A want path (Z_to_bv 64 len) fdata
MSO [(48%nat, 65536)] [] 0xa7564 K);
[ exact HR | exact HK
| rewrite HL; vm_compute; reflexivity | rewrite HL; vm_compute; reflexivity | rewrite HL; lia
| exact P0 | vm_compute; reflexivity
| regv HR (2%bv : reg); cbn [edenot ev ENVA]; rewrite P0; apply alu_add_w_litA
| unfold MSO; lia | reflexivity
| regv HR (10%bv : reg); reflexivity
| regv HR (11%bv : reg); reflexivity
| regv HR (12%bv : reg); cbn [edenot ev ENVA]; exact P71
| lia
| regv HR (1%bv : reg); reflexivity
| lia | reflexivity
| exact DI
| rewrite MF; apply fds_lookup3A
| rewrite MS; exact Hfile
| intros i nb Hf; cbn in Hf;
destruct (Nat.eqb i 48) eqn:Ei; [apply Nat.eqb_eq in Ei; subst i; injection Hf as <-; split; [rewrite HL; lia|];
rewrite P48, u_small by lia; exists (CAPk k); split; [lia|]; split; [left; reflexivity | exact HBR] | discriminate]
| intros v b Hf; discriminate
| ].
intros R' M' model' bs vals' E' HL' HA' HR' HK' DI' HFD' HFS' HSRC HFRM. subst vals' E'.
rewrite HL in HL', HA', HR'. change (72 + 10)%nat with 82%nat in HA'.
change (sr_after_call_j srRDA (map ridx c_kept) 72) with srRA0 in HR'.
change (keep_readA MSO [(48%nat, 65536)] [] knLPA) with knRA in HK'.
assert (Ebs : bs = firstn (Z.to_nat want) (skipn (Z.to_nat len) fdata)) by (subst bs; apply file_read_litA; lia).
assert (Hnb : Z.of_nat (length bs) = Z.min want (LEN - len)) by (rewrite Ebs; unfold LEN; apply length_readA; lia).
clearbody bs. set (nb := Z.of_nat (length bs)) in *.
rewrite len_word_Z in HA', HFD'. fold nb in HA', HFD'.
assert (MF' : m_fds model' = fd_insert fds0 (Z_to_bv 64 3) (FdFile path (Z_to_bv 64 (len + nb)))).
{ rewrite HFD', MF, fds_ins3A. f_equal. f_equal. apply bv_eq. rewrite bv_add_unsigned, !u_small by lia.
apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). lia. }
assert (MS' : m_fs model' = fs0) by (rewrite HFS'; exact MS).
assert (HC1 : rdn ASEGS M' (Z_to_bv 64 A1) (Z.to_nat len) = Some (firstn (Z.to_nat len) fdata)).
{ rewrite <- HC. apply rdn_agree. intros j Hj. rewrite u_small by lia. apply HFRM; unfold MSO, STAGE; lia. }
set (vals2 := vals ++ junk_vals R') in *.
change (Env (vals_ev vals2) (blobs_ev [[]; []; []; []; fdata])) with (ENVG vals2) in HR', HK'.
assert (X0 : vals_ev vals2 0 = sp0) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
assert (XV : hdr_valsA vals2) by (subst vals2; apply hdr_appA; [exact HV | rewrite HL; lia]).
assert (X38 : vals_ev vals2 38 = Z_to_bv 64 (CAPk k)) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P38).
assert (X48 : vals_ev vals2 48 = Z_to_bv 64 A1) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P48).
assert (X70 : vals_ev vals2 70 = Z_to_bv 64 len) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P70).
clear HR HK DI HC MF MS HFD' HFS' HFRM HDEF. clear M model.
destruct (Z.eq_dec nb 0) as [Hz0 | Hnz].
-
assert (HlenL : len = LEN) by lia.
assert (HKf : know_ok ASEGS (ENVG vals2) (mrestrict (ahid A model') M') knRf0A).
{ constructor; [|exact HK']. cbn [kentry_ok edenot ev ENVA]. rewrite HA', u_small by lia. lia. }
clear HK'.
drv_block0 HIok Hsp DL HR' HKf DI' X0 scr0 104%nat.
destruct (sbm_fds _ _ SBM) as (F1 & F2). rewrite MF' in F1. rewrite MS' in F2.
assert (HC2 : rdn ASEGS M (Z_to_bv 64 A1) (length fdata) = Some fdata).
{ lazymatch type of EQM with _ = mem_denot _ _ ?lg =>
apply (content_block0 vals2 _ A M' M model' lg A1 (CAPk k) (length fdata) fdata X0 ltac:(vm_compute; reflexivity) EQM EQH HZ) end; [unfold LEN in *; lia|].
rewrite HlenL in HC1. unfold LEN in HC1. rewrite Nat2Z.id, firstn_all in HC1. exact HC1. }
clear EQM EQH SBM HR' HKf DI' HC1 MF' MS' HSRC. clear M' model'.
eapply (rz_close_lz ASEGS scfg _ _ M model ECALLW (Z_to_bv 64 3)); try apply is_ecall_ECALLW.
+ vm_compute. reflexivity.
+ exact (di_halt _ _ _ _ _ _ _ _ _ _ DI).
+ regv HR (17%bv : reg). reflexivity.
+ regv HR (10%bv : reg). reflexivity.
+ rewrite u_small by lia. lia.
+ rewrite F1. apply fds_lookup3A.
+ rewrite v_addi_pc4 by lia. change (0x1277bc + 4) with 0x1277c0.
rewrite F1, fds_remove3A.
set (model2 := with_fds fds0 model).
assert (DI2 : dinvA [(A1, CAPk k)] LK0 cr A M model2).
{ apply (dinv_model scfg L ar C IL HI HIok sp0 Hsp DL M0 _ _ _ _ _ model model2 DI); [apply with_fds_vm|].
unfold model2. rewrite with_fds_halted'. exact (di_halt _ _ _ _ _ _ _ _ _ _ DI). }
assert (HK2 : know_ok ASEGS (ENVG vals2) (mrestrict (ahid A model2) M) (cellCA :: knRf0A)) by exact HK.
assert (G1 : m_fds model2 = fds0) by (unfold model2; apply with_fds_fds).
assert (G2 : m_fs model2 = fs0) by (unfold model2; rewrite with_fds_fs; exact F2).
pose proof (regs_set_a0 (ENVG vals2) _ _ (Z_to_bv 64 0) (ELit 0) HR eq_refl) as HR3.
clearbody model2. clear HR HK DI F1 F2. clear model.
lazymatch goal with |- srealizes _ _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
set (valsG := relayV vals2 Rc (gr Rc 21) (gr Rc 9) (gr Rc 19) []);
pose proof (credA_exit k cr Hk Hcr) as [HX1 HX2];
pose proof (HKC ltac:(lia) (CAPk k) cr ltac:(lia) ltac:(lia) HX1 HX2) as CL;
unfold close_kgA in CL;
apply (CL valsG Rc M model2 A A1)
end.
* reflexivity.
* unfold valsG. apply hdr_relayA. exact XV.
* unfold valsG. rewrite relayV_48. unfold gr. regv1 HR3. exact X48.
* unfold valsG. rewrite relayV_70. unfold gr. regv1 HR3. rewrite X70. f_equal. lia.
* unfold valsG, ENVA. relay_regs HR3.
* intros lo hi Hlh. unfold knGA. constructor.
-- cbn [kentry_ok edenot ev ENVA]. unfold valsG. rewrite relayV_70. unfold gr. regv1 HR3. rewrite X70, u_small by lia. lia.
-- eapply ksubl_sound; [| exact knGbaseA_sub]. apply Forall_app. split.
++ apply (kn_blkA_of_inv scfg L ar C IL HI HIok sp0 Hsp DL M0 valsG _ [(A1, CAPk k)] LK0 cr A M model2 48%nat A1 (CAPk k) 65536 DI2);
[left; reflexivity | lia | | unfold valsG; rewrite relayV_lo by lia; exact X0].
unfold valsG. rewrite relayV_48. unfold gr. regv1 HR3. exact X48.
++ unfold valsG, ENVA. eapply relay_know6; [exact HK2 | vm_compute; reflexivity | vm_compute; reflexivity].
* exact HC2.
* exact DI2.
* exact HINC.
* exact G1.
* exact G2.
-
assert (HKe : know_ok ASEGS (ENVG vals2) (mrestrict (ahid A model') M') knRe0A).
{ constructor; [|exact HK']. cbn [kentry_ok edenot ev ENVA]. rewrite HA', u_small by lia. lia. }
clear HK'.
drv_block0 HIok Hsp DL HR' HKe DI' X0 scr0 104%nat.
destruct (sbm_fds _ _ SBM) as (F1 & F2). rewrite MF' in F1. rewrite MS' in F2.
pose proof (block_nolog _ _ _ _ _ EQM EQH) as EQA.
assert (HC2 : rdn ASEGS M (Z_to_bv 64 A1) (Z.to_nat len) = Some (firstn (Z.to_nat len) fdata)).
{ rewrite <- HC1. apply rdn_agree. intros j Hj. apply EQA. }
assert (HSRC2 : rdn ASEGS M (Z_to_bv 64 STAGE) (Z.to_nat nb) = Some bs).
{ unfold nb. rewrite Nat2Z.id. rewrite <- HSRC. apply rdn_agree. intros j Hj. apply EQA. }
clear EQM EQH EQA SBM HR' HKe DI' HC1 MF' MS' HSRC. clear M' model'.
lazymatch type of HR with regs_ok _ ?sr _ => lazymatch type of HK with know_ok _ _ _ ?kn =>
eapply (amemcpy_site scfg L ar C IL HI HIok sp0 Hsp Hal DL M0 M0_def ICok vals2 _ sr kn R0 M model [(A1, CAPk k)] LK0 cr A A1 (CAPk k) (A1 + len) STAGE nb bs
MSO [] [] 0xa74fc K) end end;
[ exact HR | exact HK
| rewrite HL'; vm_compute; reflexivity | rewrite HL'; vm_compute; reflexivity | rewrite HL'; lia
| exact X0 | vm_compute; reflexivity
| regv HR (2%bv : reg); cbn [edenot ev ENVA]; rewrite X0; apply alu_add_w_litA
| unfold MSO; lia | reflexivity
| regv HR (10%bv : reg); cbn [edenot ev ENVA]; rewrite X48, X70, alu_add_Z; reflexivity
| regv HR (11%bv : reg); reflexivity
| regv HR (12%bv : reg); cbn [edenot ev ENVA]; exact HA'
| lia
| regv HR (4%bv : reg); reflexivity
| regv HR (1%bv : reg); reflexivity
| lia | reflexivity
| exact DI
| left; reflexivity | lia | lia
| apply (src_stage_aacc scfg L ar IL HI sp0 Hsp DL ICok ILY _ _ _ _ _ _ _ STAGE nb (di_inv _ _ _ _ _ _ _ _ _ _ DI)); unfold STAGE; lia
| unfold STAGE; lia | unfold STAGE; lia
| apply (src_stage_app_rng L ar IL sp0 Hsp DL); unfold STAGE; lia
| intros i Hi; left; unfold STAGE; lia
| exact HSRC2
| unfold STAGE; lia
| intros i nb0 Hf; discriminate
| intros v b Hf; discriminate
| exact HK0
| ].
intros R2 M2 model2 vals' E' HL2 HR2 HK2 DI2 HRT2 HDST HBLK HIMG. subst vals' E'.
rewrite HL' in HL2, HR2. change (72 + 32 + 32)%nat with 136%nat in HL2.
change (sr_after_call_j _ (map ridx c_kept) (72 + 32)) with srRm0 in HR2.
change (keep_allocA MSO 4096 [] [] _) with knRm0 in HK2.
destruct (model_rt_fds _ _ HRT2) as (G1 & G2). rewrite F1 in G1. rewrite F2 in G2.
assert (HC3 : rdn ASEGS M2 (Z_to_bv 64 A1) (Z.to_nat (len + nb)) = Some (firstn (Z.to_nat (len + nb)) fdata)).
{ replace (Z.to_nat (len + nb)) with (Z.to_nat len + length bs)%nat by lia.
rewrite <- firstn_app_skipnA.
replace (firstn (length bs) (skipn (Z.to_nat len) fdata)) with bs by (rewrite Ebs at 1; rewrite Ebs at 1; symmetry; apply firstn_len_firstnA).
apply rdn_app_Z; [ | | lia | lia].
- rewrite <- HC2. apply rdn_agree. intros j Hj. rewrite u_small by lia.
apply HBLK; [lia | exists (A1, CAPk k); split; [left; reflexivity | cbn [fst snd]; lia] | lia].
- rewrite Z2Nat.id by lia. unfold nb in HDST. rewrite Nat2Z.id in HDST. exact HDST. }
set (vals3 := vals2 ++ junk_vals R2) in *.
change (Env (vals_ev vals3) (blobs_ev [[]; []; []; []; fdata])) with (ENVG vals3) in HR2, HK2.
assert (Y0 : vals_ev vals3 0 = sp0) by (subst vals3; rewrite vals_ev_app_l by (rewrite HL'; lia); exact X0).
assert (YV : hdr_valsA vals3) by (subst vals3; apply hdr_appA; [exact XV | rewrite HL'; lia]).
assert (Y38 : vals_ev vals3 38 = Z_to_bv 64 (CAPk k)) by (subst vals3; rewrite vals_ev_app_l by (rewrite HL'; lia); exact X38).
assert (Y48 : vals_ev vals3 48 = Z_to_bv 64 A1) by (subst vals3; rewrite vals_ev_app_l by (rewrite HL'; lia); exact X48).
assert (Y70 : vals_ev vals3 70 = Z_to_bv 64 len) by (subst vals3; rewrite vals_ev_app_l by (rewrite HL'; lia); exact X70).
assert (Y82 : vals_ev vals3 82 = Z_to_bv 64 nb) by (subst vals3; rewrite vals_ev_app_l by (rewrite HL'; lia); exact HA').
clear HR HK DI HC2 HSRC2 HDST HBLK HIMG F1 F2 HRT2. clear M model R0.
drv_block0 HIok Hsp DL HR2 HK2 DI2 Y0 scr0 136%nat.
destruct (sbm_fds _ _ SBM) as (F1 & F2). rewrite G1 in F1. rewrite G2 in F2.
pose proof (block_nolog _ _ _ _ _ EQM EQH) as EQA.
assert (HC4 : rdn ASEGS M (Z_to_bv 64 A1) (Z.to_nat (len + nb)) = Some (firstn (Z.to_nat (len + nb)) fdata)).
{ rewrite <- HC3. apply rdn_agree. intros j Hj. apply EQA. }
lazymatch goal with |- srealizes _ _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
set (valsL := relayV vals3 Rc (gr Rc 21) (gr Rc 9) (gr Rc 19) []);
apply (IH k (len + nb) A1 valsL Rc M model A cr)
end.
+ lia.
+ lia.
+ lia.
+ lia.
+ reflexivity.
+ unfold valsL. apply hdr_relayA. exact YV.
+ unfold valsL. rewrite relayV_38. unfold gr. regv1 HR. exact Y38.
+ unfold valsL. rewrite relayV_48. unfold gr. regv1 HR. exact Y48.
+ unfold valsL. rewrite relayV_70. unfold gr. regv1 HR. rewrite Y70, Y82, alu_add_Z. reflexivity.
+ unfold valsL, ENVA. relay_regs HR; try (relay2 HR; reflexivity).
+ rewrite knLPA_split. apply Forall_app. split.
* apply (kn_blkA_of_inv scfg L ar C IL HI HIok sp0 Hsp DL M0 valsL _ [(A1, CAPk k)] LK0 cr A M model 48%nat A1 (CAPk k) 65536 DI);
[left; reflexivity | lia | | unfold valsL; rewrite relayV_lo by lia; exact Y0].
unfold valsL. rewrite relayV_48. unfold gr. regv1 HR. exact Y48.
* unfold valsL, ENVA. eapply relay_know6; [exact HK | vm_compute; reflexivity | vm_compute; reflexivity].
+ exact HC4.
+ exact DI.
+ exact HINC.
+ split; [exact F1 | exact F2].
+ exact Hcr.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_loop_stepA := (ltac2:(TCodec.tc2 tcn__Jb0DrvG "9'M&R9r1%211&R8r2%211p041pZF81")) (only parsing).
Variable z : ltac:(sec_ty2 constr:(SEC_T_loop_stepA) 0%nat 0%nat).
Lemma loop_stepA : ltac:(sec_stmt2 constr:(SEC_T_loop_stepA) 1%nat 0%nat).
Proof.
intros HRD.
unfold lp_atA.
intros k len A1 vals R M model A cr Hk Hlen HlL Hz HL HV P38 P48 P70 HR HK HC DI HINC HMD Hcr.
pose proof Hsp as Hsp'. pose proof Hal as Hal'.
pose proof (CAPk_range k Hk) as HCk.
destruct (inv_block1 _ _ _ _ _ _ _ _ DI (or_introl eq_refl)) as (HBR & HDEF & HZ). pose proof HZ as (Z1 & Z2 & Z3).
pose proof HV as (P0 & P1 & P2 & P3).
destruct HCOST as (Hkpm & Hlin & Hovh).
destruct (Z_lt_le_dec len (CAPk k)) as [Hlt | Hge].
-
pose proof (know_LP_rangesA vals _ len (CAPk k) 0 67108863 65536 67108864 P70 P38 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) HK) as HK1.
change (KRange (EVar 70) 0 67108863 :: KRange (EVar 38) 65536 67108864 :: knLPA) with knLPpA in HK1.
clear HK. rename HK1 into HK.
assert (TAIL : forall want R1 M1 (model1 : Model) (sc12 : expr),
want = Z.min (CAPk k - len) 65536 ->
regs_ok (ENVG vals) (sr_upd srPa (ridx 12) sc12) R1 -> edenot (ENVG vals) sc12 = Z_to_bv 64 want ->
know_ok ASEGS (ENVG vals) (mrestrict (ahid A model1) M1) knLPpA ->
(forall a : word, M1 a = M a) -> dinvA [(A1, CAPk k)] LK0 cr A M1 model1 -> mdl3 model1 len ->
srealizes ASEGS scfg (mkCfg (mkst R1 (Z_to_bv 64 0x62d08) M1 (seg_rom ASEGS)) model1) K).
{ intros want R1 M1 model1 sc12 Hwant HR1 H12 HK1 EQA DI1 HMD1.
assert (HC1 : rdn ASEGS M1 (Z_to_bv 64 A1) (Z.to_nat len) = Some (firstn (Z.to_nat len) fdata)).
{ rewrite <- HC. apply rdn_agree. intros j Hj. apply EQA. }
set (valsR := relayV vals R1 (gr R1 21) (gr R1 9) (gr R1 19) [gr R1 12]).
apply (HRD k len want A1 valsR R1 M1 model1 A cr); [lia | lia | lia | lia | exact Hwant | reflexivity | | | | | | | | exact HC1 | exact DI1 | exact HINC | exact HMD1 | exact Hcr].
+ unfold valsR. apply hdr_relayA. exact HV.
+ unfold valsR. rewrite relayV_38. unfold gr. regv1 HR1. exact P38.
+ unfold valsR. rewrite relayV_48. unfold gr. regv1 HR1. exact P48.
+ unfold valsR. rewrite relayV_70. unfold gr. regv1 HR1. exact P70.
+ unfold valsR. rewrite relayV_71. unfold gr. regv1 HR1. exact H12.
+ unfold valsR, ENVA. relay_regs HR1; try (relay2 HR1; reflexivity).
+ rewrite knLPA_split. apply Forall_app. split.
* apply (kn_blkA_of_inv scfg L ar C IL HI HIok sp0 Hsp DL M0 valsR _ [(A1, CAPk k)] LK0 cr A M1 model1 48%nat A1 (CAPk k) 65536 DI1);
[left; reflexivity | lia | | unfold valsR; rewrite relayV_lo by lia; exact P0].
unfold valsR. rewrite relayV_48. unfold gr. regv1 HR1. exact P48.
* unfold valsR, ENVA. eapply relay_know6; [exact HK1 | vm_compute; reflexivity | vm_compute; reflexivity]. }
destruct (Z_lt_le_dec (CAPk k - len) 65536) as [Hsmall | Hbig].
+
drv_block0 HIok Hsp DL HR HK DI P0 (SCR [false; true] [] []) 71%nat.
{ apply (sc_ltu_wantA vals _ len (CAPk k) true P70 P38); [lia | lia | apply Z.ltb_lt; lia]. }
{ apply (sc_eq_70_38A vals _ len (CAPk k) false P70 P38); [lia | lia | apply Z.eqb_neq; lia]. }
apply (TAIL (CAPk k - len) R0 M1 model0 want_xA); [lia | exact HR0 | apply (want_x_valA vals len (CAPk k) P70 P38); lia | exact HK1
| exact (block_nolog _ _ _ _ _ EQM EQH) | exact DI0 |].
destruct (sbm_fds _ _ SBM) as (F1 & F2). destruct HMD as (MF & MS). split; [rewrite F1; exact MF | rewrite F2; exact MS].
+
drv_block0 HIok Hsp DL HR HK DI P0 (SCR [false; false] [] []) 71%nat.
{ apply (sc_ltu_wantA vals _ len (CAPk k) false P70 P38); [lia | lia | apply Z.ltb_ge; lia]. }
{ apply (sc_eq_70_38A vals _ len (CAPk k) false P70 P38); [lia | lia | apply Z.eqb_neq; lia]. }
apply (TAIL 65536 R0 M1 model0 (ELit 65536)); [lia | exact HR0 | reflexivity | exact HK1
| exact (block_nolog _ _ _ _ _ EQM EQH) | exact DI0 |].
destruct (sbm_fds _ _ SBM) as (F1 & F2). destruct HMD as (MF & MS). split; [rewrite F1; exact MF | rewrite F2; exact MS].
-
assert (Heq : len = CAPk k) by lia.
destruct (Z.eq_dec k 10) as [Hk10 | Hk10].
+
assert (HC10 : CAPk k = 67108864) by (rewrite Hk10; reflexivity).
assert (Hl10 : len = 67108864) by lia.
rewrite Hl10 in P70, HMD. rewrite HC10 in P38, DI.
apply (HREF ltac:(lia) A1 vals R M model A cr); assumption.
+
pose proof (CAPk_lt10 k ltac:(lia)) as HC25.
pose proof (know_LP_rangesA vals _ len (CAPk k) 65536 33554432 65536 33554432 P70 P38 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) HK) as HK1.
change (KRange (EVar 70) 65536 33554432 :: KRange (EVar 38) 65536 33554432 :: knLPA) with knLPgA in HK1.
clear HK. rename HK1 into HK.
drv_block0 HIok Hsp DL HR HK DI P0 (SCR [true] [] []) 71%nat.
{ apply (sc_eq_70_38A vals _ len (CAPk k) true P70 P38); [lia | lia | apply Z.eqb_eq; lia]. }
pose proof (block_nolog _ _ _ _ _ EQM EQH) as EQA.
destruct (sbm_fds _ _ SBM) as (F1 & F2). destruct HMD as (MF & MS). rewrite MF in F1. rewrite MS in F2.
assert (HC1 : rdn ASEGS M1 (Z_to_bv 64 A1) (Z.to_nat len) = Some (firstn (Z.to_nat len) fdata)).
{ rewrite <- HC. apply rdn_agree. intros j Hj. apply EQA. }
clear EQM EQH EQA SBM HR HK DI HC MF MS HDEF. clear M model R.
lazymatch type of HR0 with regs_ok _ ?sr _ => lazymatch type of HK1 with know_ok _ _ _ ?kn =>
eapply (amalloc_site scfg L ar C IL HI HIok sp0 Hsp Hal DL M0 M0_def vals _ sr kn R0 M1 model0 [(A1, CAPk k)] LK0 cr A (2 * CAPk k) MSO
[(48%nat, 65536)] [] 0xa7524 K) end end;
[ exact HR0 | exact HK1
| rewrite HL; vm_compute; reflexivity | rewrite HL; vm_compute; reflexivity | rewrite HL; lia
| exact P0 | vm_compute; reflexivity
| regv HR0 (2%bv : reg); cbn [edenot ev ENVA]; rewrite P0; apply alu_add_w_litA
| unfold MSO; lia | reflexivity
| regv HR0 (10%bv : reg); rewrite Heq in P70; apply (cap2_x_valA vals (CAPk k) P70); lia
| lia
| destruct Hcr as [Hc1 Hc2]; unfold acredit_ok; split; nia
| regv HR0 (4%bv : reg); reflexivity
| regv HR0 (1%bv : reg); reflexivity
| lia | reflexivity
| exact DI0
| intros i nb Hf; cbn in Hf;
destruct (Nat.eqb i 48) eqn:Ei; [apply Nat.eqb_eq in Ei; subst i; injection Hf as <-; split; [rewrite HL; lia|];
rewrite P48, u_small by lia; exists (CAPk k); split; [lia|]; split; [left; reflexivity | exact HBR] | discriminate]
| intros v b Hf; discriminate
| exact HK0 | ].
intros R' M' model' A' u vals' E' HL' HA2 HR' HK' DI' HRT HINC' HBR2 HAP HSHB HAB HBLK HIMG. subst vals' E'.
set (vals2 := vals ++ junk_vals R') in *.
change (Env (vals_ev vals2) (blobs_ev [[]; []; []; []; fdata])) with (ENVG vals2) in HR', HK'.
rewrite HL in HL', HA2, HR', HK'. change (71 + 10)%nat with 81%nat in HA2, HK'. change (71 + 32)%nat with 103%nat in HL'.
destruct (model_rt_fds _ _ HRT) as (G1 & G2). rewrite F1 in G1. rewrite F2 in G2.
pose proof (hzA_of_block_range L ar IL sp0 DL _ _ HBR2) as HZ2. pose proof HZ2 as (U1 & U2 & U3). pose proof HBR2 as (_ & _ & U4 & _ & _).
assert (NEQ : u <> A1).
{ specialize (HAP (A1, CAPk k) ltac:(left; reflexivity)). cbn [fst snd] in HAP. lia. }
assert (X0 : vals_ev vals2 0 = sp0) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
assert (XV : hdr_valsA vals2) by (subst vals2; apply hdr_appA; [exact HV | rewrite HL; lia]).
assert (X48 : vals_ev vals2 48 = Z_to_bv 64 A1) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P48).
assert (X70 : vals_ev vals2 70 = Z_to_bv 64 (CAPk k)) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); rewrite <- Heq; exact P70).
apply Forall_app in HK' as [HKB HK'].
assert (HKU : know_ok ASEGS (ENVG vals2) (mrestrict (ahid A' model') M') knGb0).
{ change knGb0 with (kn_blk2A 81 ++ keepalloc_G knLPgA). apply Forall_app. split.
- unfold kn_blk2A. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; cbn [kentry_ok edenot ev ENVA]; rewrite HA2, u_small by lia; lia.
- exact HK'. }
clear HK' HKB HK1 HR0.
assert (HC2 : rdn ASEGS M' (Z_to_bv 64 A1) (Z.to_nat (CAPk k)) = Some (firstn (Z.to_nat (CAPk k)) fdata)).
{ rewrite <- Heq, <- HC1. symmetry. apply rdn_agree. intros j Hj. rewrite u_small by lia. symmetry. apply HBLK; [lia|].
exists (A1, CAPk k). split; [left; reflexivity|]. cbn [fst snd]. lia. }
clear HC1 DI0 HBLK HIMG HAB F1 F2 HRT. clear M1 model0 R0.
drv_block0 HIok Hsp DL HR' HKU DI' X0 scr0 103%nat.
pose proof (block_nolog _ _ _ _ _ EQM EQH) as EQA.
destruct (sbm_fds _ _ SBM) as (F1 & F2). rewrite G1 in F1. rewrite G2 in F2.
assert (HC3 : rdn ASEGS M (Z_to_bv 64 A1) (Z.to_nat (CAPk k)) = Some (firstn (Z.to_nat (CAPk k)) fdata)).
{ rewrite <- HC2. apply rdn_agree. intros j Hj. apply EQA. }
clear EQM EQH EQA SBM HR' HKU DI' HC2 G1 G2 HSHB. clear M' model'.
assert (HFL : length (firstn (Z.to_nat (CAPk k)) fdata) = Z.to_nat (CAPk k)) by (rewrite length_firstn; unfold LEN in HlL; lia).
lazymatch type of HR with regs_ok _ ?sr _ => lazymatch type of HK with know_ok _ _ _ ?kn =>
eapply (amemcpy_site scfg L ar C IL HI HIok sp0 Hsp Hal DL M0 M0_def ICok vals2 _ sr kn R M model [(u, 2 * CAPk k); (A1, CAPk k)] LK0
(adebit L cr (2 * CAPk k)) A' u (2 * CAPk k) u A1 (CAPk k) (firstn (Z.to_nat (CAPk k)) fdata) MSO [(48%nat, 65536)] [] 0xa7540 K) end end;
[ exact HR | exact HK
| rewrite HL'; vm_compute; reflexivity | rewrite HL'; vm_compute; reflexivity | rewrite HL'; lia
| exact X0 | vm_compute; reflexivity
| regv HR (2%bv : reg); cbn [edenot ev ENVA]; rewrite X0; apply alu_add_w_litA
| unfold MSO; lia | reflexivity
| regv HR (10%bv : reg); cbn [edenot ev ENVA]; exact HA2
| regv HR (11%bv : reg); cbn [edenot ev ENVA]; exact X48
| regv HR (12%bv : reg); cbn [edenot ev ENVA]; exact X70
| lia
| regv HR (4%bv : reg); reflexivity
| regv HR (1%bv : reg); reflexivity
| lia | reflexivity
| exact DI
| left; reflexivity | lia | lia
| apply (src_blk_aacc scfg L ar C HI HIok sp0 Hsp _ _ _ _ _ _ _ A1 (CAPk k) A1 (CAPk k) (di_inv _ _ _ _ _ _ _ _ _ _ DI)); [right; left; reflexivity | lia | lia]
| lia | lia
| apply (src_blk_app_rng scfg L ar C HI HIok sp0 Hsp _ _ _ _ _ _ _ A1 (CAPk k) A1 (CAPk k) (di_inv _ _ _ _ _ _ _ _ _ _ DI)); [right; left; reflexivity | lia | lia]
| intros i Hi; right; exists (A1, CAPk k); split; [right; left; reflexivity | cbn [fst snd]; lia]
| exact HC3
| specialize (HAP (A1, CAPk k) ltac:(left; reflexivity)); cbn [fst snd] in HAP; lia
| intros i nb Hf; cbn in Hf;
destruct (Nat.eqb i 48) eqn:Ei; [apply Nat.eqb_eq in Ei; subst i; injection Hf as <-; split; [rewrite HL'; lia|];
rewrite X48, u_small by lia; rewrite lb_remove_hdA; exists (CAPk k); split; [lia|]; split; [left; reflexivity | exact HBR] | discriminate]
| intros v b Hf; discriminate
| exact HK0
| ].
intros R3 M3 model3 vals' E' HL3 HR3 HK3 DI3 HRT3 HDST HBLK3 HIMG3. subst vals' E'.
rewrite HL' in HL3, HR3. change (103 + 32)%nat with 135%nat in HL3.
change (sr_after_call_j _ (map ridx c_kept) 103) with srGc0 in HR3.
change (keep_allocA MSO 4096 [(48%nat, 65536)] [] _) with knGc0 in HK3.
destruct (model_rt_fds _ _ HRT3) as (G1 & G2). rewrite F1 in G1. rewrite F2 in G2.
set (vals3 := vals2 ++ junk_vals R3) in *.
change (Env (vals_ev vals3) (blobs_ev [[]; []; []; []; fdata])) with (ENVG vals3) in HR3, HK3.
assert (Y0 : vals_ev vals3 0 = sp0) by (subst vals3; rewrite vals_ev_app_l by (rewrite HL'; lia); exact X0).
assert (YV : hdr_valsA vals3) by (subst vals3; apply hdr_appA; [exact XV | rewrite HL'; lia]).
assert (Y48 : vals_ev vals3 48 = Z_to_bv 64 A1) by (subst vals3; rewrite vals_ev_app_l by (rewrite HL'; lia); exact X48).
assert (Y70 : vals_ev vals3 70 = Z_to_bv 64 (CAPk k)) by (subst vals3; rewrite vals_ev_app_l by (rewrite HL'; lia); exact X70).
assert (Y81 : vals_ev vals3 81 = Z_to_bv 64 u) by (subst vals3; rewrite vals_ev_app_l by (rewrite HL'; lia); exact HA2).
clear HR HK DI HC3 HBLK3 HIMG3 F1 F2 HRT3. clear M model R.
drv_block0 HIok Hsp DL HR3 HK3 DI3 Y0 scr0 135%nat.
pose proof (block_nolog _ _ _ _ _ EQM EQH) as EQA.
destruct (sbm_fds _ _ SBM) as (F1 & F2). rewrite G1 in F1. rewrite G2 in F2.
assert (HC4 : rdn ASEGS M (Z_to_bv 64 u) (Z.to_nat (CAPk k)) = Some (firstn (Z.to_nat (CAPk k)) fdata)).
{ rewrite <- HDST. apply rdn_agree. intros j Hj. apply EQA. }
clear EQM EQH EQA SBM HR3 HK3 DI3 HDST G1 G2. clear M3 model3.
lazymatch type of HR with regs_ok _ ?sr _ => lazymatch type of HK with know_ok _ _ _ ?kn =>
eapply (afree_site scfg L ar C IL HI HIok sp0 Hsp Hal DL M0 M0_def vals3 _ sr kn R M model [(u, 2 * CAPk k); (A1, CAPk k)] LK0
(adebit L cr (2 * CAPk k)) A' A1 (CAPk k) MSO [] [] 0xa7548 K) end end;
[ exact HR | exact HK
| rewrite HL3; vm_compute; reflexivity | rewrite HL3; vm_compute; reflexivity | rewrite HL3; lia
| exact Y0 | vm_compute; reflexivity
| regv HR (2%bv : reg); cbn [edenot ev ENVA]; rewrite Y0; apply alu_add_w_litA
| unfold MSO; lia | reflexivity
| right; left; reflexivity
| regv HR (10%bv : reg); cbn [edenot ev ENVA]; exact Y48
| regv HR (4%bv : reg); reflexivity
| regv HR (1%bv : reg); reflexivity
| lia | reflexivity
| exact DI
| intros i nb Hf; discriminate
| intros v b Hf; discriminate
| exact HK0 | ].
intros R4 M4 model4 A4 vals' E' HL4 HR4 HK4 DI4 HRT4 HINC4 HAB4 HBLK4 HIMG4. subst vals' E'.
rewrite (lb_remove_2A u (2 * CAPk k) A1 (CAPk k) NEQ) in DI4, HBLK4.
rewrite HL3 in HL4, HR4. change (135 + 32)%nat with 167%nat in HL4.
change (sr_after_call_j _ (map ridx c_kept) 135) with srGd0 in HR4.
change (keep_allocA MSO 4096 [] [] _) with knGd0 in HK4.
destruct (model_rt_fds _ _ HRT4) as (G1 & G2). rewrite F1 in G1. rewrite F2 in G2.
set (vals4 := vals3 ++ junk_vals R4) in *.
change (Env (vals_ev vals4) (blobs_ev [[]; []; []; []; fdata])) with (ENVG vals4) in HR4, HK4.
assert (W0 : vals_ev vals4 0 = sp0) by (subst vals4; rewrite vals_ev_app_l by (rewrite HL3; lia); exact Y0).
assert (WV : hdr_valsA vals4) by (subst vals4; apply hdr_appA; [exact YV | rewrite HL3; lia]).
assert (W70 : vals_ev vals4 70 = Z_to_bv 64 (CAPk k)) by (subst vals4; rewrite vals_ev_app_l by (rewrite HL3; lia); exact Y70).
assert (W81 : vals_ev vals4 81 = Z_to_bv 64 u) by (subst vals4; rewrite vals_ev_app_l by (rewrite HL3; lia); exact Y81).
assert (HC5 : rdn ASEGS M4 (Z_to_bv 64 u) (Z.to_nat (CAPk k)) = Some (firstn (Z.to_nat (CAPk k)) fdata)).
{ rewrite <- HC4. apply rdn_agree. intros j Hj. rewrite u_small by lia. apply HBLK4; [lia|].
exists (u, 2 * CAPk k). split; [left; reflexivity|]. cbn [fst snd]. lia. }
clear HR HK DI HC4 HBLK4 HIMG4 HAB4 F1 F2 HRT4. clear M model R.
drv_block0 HIok Hsp DL HR4 HK4 DI4 W0 scr0 167%nat.
pose proof (block_nolog _ _ _ _ _ EQM EQH) as EQA.
destruct (sbm_fds _ _ SBM) as (F1 & F2). rewrite G1 in F1. rewrite G2 in F2.
assert (HC6 : rdn ASEGS M (Z_to_bv 64 u) (Z.to_nat (CAPk k)) = Some (firstn (Z.to_nat (CAPk k)) fdata)).
{ rewrite <- HC5. apply rdn_agree. intros j Hj. apply EQA. }
lazymatch goal with |- srealizes _ _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
set (valsR := relayV vals4 Rc (gr Rc 21) (gr Rc 9) (gr Rc 19) [gr Rc 12]);
apply (HRD (k + 1) len 65536 u valsR Rc M model A4 (adebit L cr (2 * CAPk k)))
end.
* lia.
* rewrite CAPk_S by lia. lia.
* lia.
* lia.
* rewrite CAPk_S by lia. lia.
* reflexivity.
* unfold valsR. apply hdr_relayA. exact WV.
* unfold valsR. rewrite relayV_38. unfold gr. regv1 HR. change (nth 21 srGd (ELit 0)) with cap2_xA.
rewrite CAPk_S by lia. apply (cap2_x_valA vals4 (CAPk k) W70); lia.
* unfold valsR. rewrite relayV_48. unfold gr. regv1 HR. exact W81.
* unfold valsR. rewrite relayV_70. unfold gr. regv1 HR. rewrite Heq. exact W70.
* unfold valsR. rewrite relayV_71. unfold gr. regv1 HR. reflexivity.
* unfold valsR, ENVA. relay_regs HR; try (relay2 HR; reflexivity).
* rewrite knLPA_split. apply Forall_app. split.
-- apply (kn_blkA_of_inv scfg L ar C IL HI HIok sp0 Hsp DL M0 valsR _ [(u, 2 * CAPk k)] LK0 (adebit L cr (2 * CAPk k)) A4 M model 48%nat u (2 * CAPk k) 65536 DI);
[left; reflexivity | lia | | unfold valsR; rewrite relayV_lo by lia; exact W0].
unfold valsR. rewrite relayV_48. unfold gr. regv1 HR. exact W81.
-- unfold valsR, ENVA. eapply relay_know6; [exact HK | vm_compute; reflexivity | vm_compute; reflexivity].
* rewrite Heq. exact HC6.
* rewrite CAPk_S by lia. exact DI.
* intros x Hx. apply HINC4. apply HINC'. apply HINC. exact Hx.
* split; [exact F1 | exact F2].
* destruct Hcr as [Hc1 Hc2]. unfold credA, adebit. cbn [fst snd]. rewrite CAPk_S by lia. split; nia.
Qed.
End SE.
Lemma loop_okA : ltac2:(TCodec.tc2 tcn__Jb0DrvG "7'<&R8&SBr1%211%411pY>61").
Proof.
induction n as [|n IH].
- apply loop_stepA. apply read_okA. unfold lp_atA. intros. exfalso. lia.
- apply loop_stepA. apply read_okA. replace (Z.of_nat (Datatypes.S n) - 1) with (Z.of_nat n) by lia. exact IH.
Qed.
Variable cr0 : credit.
Hypothesis Hcr0 : credA 0 (adebit L cr0 65536).
Theorem drv_fileA : ltac2:(TCodec.tc2 tcn__Jb0DrvG "C&R3vT7vTNvQ2vSGvOvTOvTKvT6vT5vTIvTJvSKvQEvQ5vSOv1vQ0%BAA@?>=<;:987654321").
Proof.
unfold file_kA.
intros vals R M model A A1 HL P0 P1 P2 P3 P48 HR HK DI HINC MF MS HBR.
pose proof Hsp as Hsp'. pose proof Hal as Hal'.
assert (HV : hdr_valsA vals) by (unfold hdr_valsA; repeat split; assumption).
change (Jb0DrvA.ENVA fdata vals) with (ENVG vals) in HR, HK.
drv_block0 HIok Hsp DL HR HK DI P0 scr0 70%nat.
pose proof (block_nolog _ _ _ _ _ EQM EQH) as EQA.
destruct (sbm_fds _ _ SBM) as (F1 & F2). rewrite MF in F1. rewrite MS in F2.
pose proof (read_okA (LEN + 1) ltac:(replace (LEN + 1 - 1) with (Z.of_nat (length fdata)) by (unfold LEN; lia); apply loop_okA)) as RD.
lazymatch goal with |- srealizes _ _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
set (valsR := relayV vals Rc (gr Rc 21) (gr Rc 9) (gr Rc 19) [gr Rc 12]);
apply (RD 0 0 65536 A1 valsR Rc M1 model0 A (adebit L cr0 65536))
end.
- lia.
- unfold CAPk. rewrite Z.pow_0_r. lia.
- unfold LEN. lia.
- unfold LEN. lia.
- unfold CAPk. rewrite Z.pow_0_r. reflexivity.
- reflexivity.
- unfold valsR. apply hdr_relayA. exact HV.
- unfold valsR. rewrite relayV_38. unfold gr. regv1 HR0. unfold CAPk. rewrite Z.pow_0_r. reflexivity.
- unfold valsR. rewrite relayV_48. unfold gr. regv1 HR0. exact P48.
- unfold valsR. rewrite relayV_70. unfold gr. regv1 HR0. reflexivity.
- unfold valsR. rewrite relayV_71. unfold gr. regv1 HR0. reflexivity.
- unfold valsR, ENVA. relay_regs HR0; try (relay2 HR0; reflexivity).
- rewrite knLPA_split. apply Forall_app. split.
+ apply (kn_blkA_of_inv scfg L ar C IL HI HIok sp0 Hsp DL M0 valsR _ [(A1, 65536)] LK0 (adebit L cr0 65536) A M1 model0 48%nat A1 65536 65536 DI0);
[left; reflexivity | lia | | unfold valsR; rewrite relayV_lo by lia; exact P0].
unfold valsR. rewrite relayV_48. unfold gr. regv1 HR0. exact P48.
+ unfold valsR, ENVA. eapply relay_know6; [exact HK1 | vm_compute; reflexivity | vm_compute; reflexivity].
- reflexivity.
- unfold CAPk. rewrite Z.pow_0_r. exact DI0.
- exact HINC.
- split; [exact F1 | exact F2].
- exact Hcr0.
Qed.
End DrvG.
End FPX_1.

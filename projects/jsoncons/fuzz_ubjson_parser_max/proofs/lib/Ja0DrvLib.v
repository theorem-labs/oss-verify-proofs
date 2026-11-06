(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import
PropExec CatExec CatSim StoreOk StreamSim ShapeAlg SpinAlg Hoare AsanAcctShape SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4
HeapIface HeapIfaceA IcptIfaceA DrvKitA DrvNodesLazyK As0DrvKitA Ja0DrvEntry Ja0Drv_defs.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Import SX2. Import SX2S.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Ja0DrvLib () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Decimal."; "Corelib.Init.Logic."; "Corelib.Init.Nat."; "Corelib.Init.Number."; "Corelib.Init.Peano."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.Fs."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.LinuxProcessSem.Run."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.As0DrvKitA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanAcct."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.DrvKitA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.DrvNodesLazyK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0DrvLib.FPX_1.DrvLayoutA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0Drv_defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StreamSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymDrive."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2Sound.SX2S."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymRun."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A"; "0A'"; "0Ad"; "0As"; "1None"; "1O"; "1Some"; "1app"; "1bool"; "1cons"; "1false"; "1length"; "1list"; "1nat"; "1nil"; "1option"]; ["1pair"; "1prod"; "1true"; "2D3"; "2D5"; "2D6"; "2Nil"; "3I"; "3True"; "3and"; "3eq"; "3ex"; "3not"; "3or"; "4add"; "4of_num_uint"]; ["5UIntDecimal"; "6le"; "6lt"; "7map"; "7nth"; "8Z"; "0E"; "0E'"; "0FF"; "0FF'"; "0H"; "0HI"; "0K"; "0L"; "0LB"; "0LB'"]; ["0LBc"; "0LK"; "0LK'"; "9Fs"; ":store_ok"; ";mkCfg"; "<FdEntry"; "<Model"; "<VmState"; "<event"; "<m_fds"; "<m_fs"; "<m_halted"; "<m_vm"; "<m_vm_lazy"; "<with_fds"]; ["=bvmap"; "0M"; "0M'"; "0MV"; "0Mx"; "0P"; "0R"; "0R'"; ">lzinv"; "?MInv"; "?mrestrict"; "?same_but_materialized"; "?segs_below_b"; "@find_nz"; "@log_in_b"; "@regions_ok"]; ["Anolazy_rng"; "Bblocks_apart"; "Bcredit"; "Bdefined"; "Bin_block"; "Blb_remove"; "Bregs_preserved"; "CS"; "Caacc"; "Cablock_range"; "Caclient"; "Cacredit_ok"; "Cadebit"; "Cahid"; "Capp_rng"; "Car_sptop"]; ["Car_stack_top"; "Cart_private"; "Castack_ok"; "Cblock_shadow"; "Cfframe"; "Cin_shadow_of"; "Cmodel_rt"; "Cri_inv"; "Cshadow_blk"; "Cvml"; "Cvml_of"; "DCPa"; "DCWA"; "DSCa"; "DSTKTOP"; "Ddinv"]; ["Dhas_window"; "DhzA"; "Dsub_blockA"; "EIMG_CLIENT_A"; "EIMG_RW_A"; "EIMG_W_A"; "Ec_kept"; "Ekeep_allocA"; "Ekn_blkA"; "Fgetr"; "Fmkst"; "Frdn"; "Fseg_rom"; "Gsrealizes"; "Hwseg_ok"; "Ijunk_vals"]; ["Isr_after_call_j"; "JEVar"; "JEnv"; "JKWr"; "JSA"; "Jenv"; "Jexpr"; "Jkentry"; "Jridx"; "Jsentry"; "Kknow_ok"; "Kmem_denot"; "Kregs_ok"; "Lkn_vars_lt"; "Lsr_vars_lt"; "Lvals_ev"]; ["Mloaded_segments"; "NIn"; "Nincl"; "Nnth_error"; "Oadd"; "Ole"; "Olt"; "Omodulo"; "Oof_nat"; "Oopp"; "Opow"; "Osub"; "Oto_nat"; "0V"; "0a"; "0ar"]; ["0b"; "0bls"; "0bs"; "0cap"; "0capd"; "0caps"; "0cr"; "0cr'"; "0dst"; "0ebs"; "0f"; "0fx"; "0hi"; "0hi'"; "0i"; "0j"]; ["0k"; "0kn"; "0lo"; "0lo'"; "0log"; "0m"; "0m'"; "0model"; "0model'"; "0n"; "0nb"; "0p"; "0r"; "0ra"; "0scfg"; "0scr"]; ["0scr'"; "0so"; "0sp"; "0sp0"; "0sr"; "0src"; "PBV"; "PZ_to_bv"; "Pbv"; "Pbv_unsigned"; "0u"; "0v"; "0vals"; "0vals'"; "0vbnd"; "0x"]; ["0z"]]).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Lemma no_bls : ltac2:(TCodec.tc2 tcn__Ja0DrvLib "J'='Q5!p021p041'J'?%116&R=r2(>'A%12<;%311%6251(6r1%22@1%=3;41r4r3%221<p041p[FF1pZNH1pT<E1").
Proof. intros P i nb H. discriminate H. Qed.
Section FPX_1. Context {fx : PropExec.FPState}.
Variable scfg : SpuriousCfg.
Section DrvLayoutA.
Variable L : asan_layout.
Variable ar : asan_run.
Variable C : asan_statics_cells.
Variable IL : icpt_layout.
Variable HI : asan_iface.
Hypothesis HIok : asan_iface_ok L ar C scfg HI.
Variable sp0 : word.
Hypothesis Hsp : 0x7fff80000000 <= bv_unsigned sp0 <= 2 ^ 47.
Hypothesis Hal : bv_unsigned sp0 mod 16 = 0.
Record drv_layoutA : Prop := DLA {
dla_segs : hl_segs L = ASEGS;
dla_malloc : hl_malloc L = 0x78ec0; dla_free : hl_free L = 0x78ebc; dla_memcpy : icl_memcpy IL = 0x77338;
dla_tp : hl_tp L = 0x66ed80;
dla_img_lo : hl_img_lo L = 0x10000; dla_img_hi : hl_img_hi L = 0x691000;
dla_sptop : ar_sptop ar = bv_unsigned sp0;
dla_scr : 0 <= hl_scr_malloc L <= 4096 /\ 0 <= hl_scr_free L <= 4096 /\ 0 <= hl_scr_mem L <= 4096;
dla_client : forall lo hi a, In (lo, hi) IMG_CLIENT_A -> lo <= a < hi -> ~ hl_rt_static L a;
dla_ro : forall lo hi a, In (lo, hi) IMG_W_A -> lo <= a < hi -> ~ hl_rt_ro L a;
dla_ro_img : forall a, hl_rt_ro L a -> 0x10000 <= a < 0x691000
}.
Hypothesis DL : drv_layoutA.
Lemma wseg_stage : ltac2:(TCodec.tc2 tcn__Ja0DrvLib "H'J'8&SN&T@&V7yR0+V[dj@%3221&O(Q0(E(D(C(F%411%311%511%611%811%:11%<11%C3B>1(B%G3F21").
Proof. vm_compute. reflexivity. Qed.
Lemma vis_of_inv : ltac2:(TCodec.tc2 tcn__Ja0DrvLib "R:'<'A'Q5%2211%411&S4%611&RB'V8yR0%211'?y8%511%311p051'QG&S7vQ;r8r7r6r5r4r3&S:r2%211%;8:9876541'I&TEz%2216&TF&TJ+2+R0%3221%52<1%:271'M+VbTP0%92B1&TK&V9vV3%22Q51+XPPP0%5221%C21I&RDr:%221L%=241%>2<1'J'8&RM&V7%12QBQ4%33Q8Q61(:%73621p091p0I1p0Q51pYNR01p[@QC1pT4QE1p2R11pZ>QO1pS4R11pRBR21pRNR51").
Proof.
intros LB FF LK cr A M model a HH Ha Hc.
destruct (ahid A model (Z_to_bv 64 a)) eqn:Hh; [exfalso | reflexivity].
unfold ahid, mkH in Hh. apply andb_prop in Hh as [Hl _].
destruct (aio_lazy _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & LZ).
specialize (LZ (Z_to_bv 64 a) Hl). cbv zeta in LZ. rewrite u_small in LZ by lia.
rewrite (dla_img_hi DL), (dla_sptop DL) in LZ. destruct LZ as (Z1 & Z2 & Z3 & _).
destruct Hc as [Hc|[Hc|Hc]]; [lia | lia | exact (Z3 Hc)].
Qed.
Lemma nolazy_of_inv : ltac2:(TCodec.tc2 tcn__Ja0DrvLib "RA'<'A'Q5%2211%411&S4%611&RB'V8yR0%211'?y8%511%311p051'QG&S7vQ;r9r8r7r6r5r4&S:r3%211%;8:9876541&TE&TD&V9%12G6r2%4221&TJ+2+R0%3221%:251'Izr1%>221&TF%123E%6231'M%A2Q7J%C21@+VbTP0%7221&TKvV3%G2Q=1+XPPP0%4221%L218&RDr=%221;%>241%?2;1p0A1p[2QN1&R@&QN%11Q=%331Q=Q<p051p0O1p0Q;1p[DR61pYNQO1p[@QJ1pT4QL1p2R81pZ>R61pS4R81pRBR91pRNR<1").
Proof.
intros LB FF LK cr A M model a n HH Hn Hc k Hk. pose proof (u64_range a) as Ua.
destruct (page_in_ranges (page_base_of (bv_unsigned a + k)) (m_vm_lazy model)) eqn:Hp; [exfalso | reflexivity].
destruct (aio_lazy _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & LZ).
specialize (LZ (Z_to_bv 64 (bv_unsigned a + k))). unfold page_base in LZ. rewrite u_small in LZ by lia.
specialize (LZ Hp). cbv zeta in LZ. rewrite (dla_img_hi DL), (dla_sptop DL) in LZ. destruct LZ as (Z1 & Z2 & Z3 & _).
destruct (Hc k Hk) as [H1|[H1|H1]]; [lia | lia | exact (Z3 H1)].
Qed.
Definition CPa (LB : list (Z * Z)) (FF : list fframe) (sp scr : Z) (H H' : word -> bool) (a : Z) : Prop :=
aclient L ar LB FF sp scr a /\ H (Z_to_bv 64 a) = false /\ H' (Z_to_bv 64 a) = false.
Definition SCa (sp scr : Z) (a : Z) : Prop := sp - scr <= a < sp.
Definition sub_blockA (LB : list (Z * Z)) (A nb : Z) : Prop :=
exists cap, 0 < nb <= cap /\ In (A, cap) LB /\ ablock_range L ar A cap.
Definition hzA (A n : Z) : Prop := 4096 <= A /\ (A + n <= 0x10000 \/ 0x691000 <= A) /\ A + n <= bv_unsigned sp0 - 8388608.
Lemma hzA_of_block_range : ltac2:(TCodec.tc2 tcn__Ja0DrvLib "='Q5&RIvQ=vTOr2r1%544321&SAr3%2215p041p[D;1p2<1").
Proof.
clear Hsp Hal. intros A n (B1 & B2 & B3 & B4 & B5 & B6). rewrite (dla_img_lo DL), (dla_img_hi DL) in B2. rewrite (dla_sptop DL) in B5.
unfold hzA. repeat split; lia.
Qed.
Lemma sub_blockA_hz : ltac2:(TCodec.tc2 tcn__Ja0DrvLib "@'<'A'Q5%2211%411&SBr3r2r1%43321&SA%1254p031p[F;1p2<1pRN;1").
Proof. clear Hsp Hal. intros LB A nb (cap & Hnb & _ & HB). apply hzA_of_block_range in HB. unfold hzA in *. lia. Qed.
Lemma regions_callA : ltac2:(TCodec.tc2 tcn__Ja0DrvLib "TI'<'V8yR0%211%411'=y8%611%811p041'Q5'A%1272%=11%3244%?11&S4%A11&RB'?%11=p0B1'QG'T5(T2&T?rE%211rD%5221'JrF(5%8221vV3%53Q021'I&TE&TI&TJ+2+F%3221%511%721Bz%92D1%;231%;23F+TP0%=2H1%?231&S7vQ;rBr@r>r<r:r8&S:r6%211%;8:9876541&RDr1%22Q31r2%42Q51p031pYNQL1rG%8217p015pYNR01%QH1R1&R=rK%22;1(6%12R6?%QC3631&SBrJ&V9rQ0r3%QN221%42RF1%7361Fp091p[FRA1pZNRG1rQ1%R5218%;2RM1%QK21Mp0@1pZ2RH1p\HRN1'R?&T@rMrL(>%11S4&SC&SD&S;rI&TD%K2S=R=%221:&RM%12QKQIr?r;%4221%:69RG6?41&S=%128A%E<DRICBQ<Q6@?>QO31p0G1p0O1p0QB1p0QG1p0QO1p0R01p0R=1p0RB1p0RO1tR>S<S61p[BS>1p[@S?1pT6SA1pT4SB1p4SI1p2SJ1pZ@SH1pZ>SI1pS6SK1pS4SL1pRDSM1pRBSN1pS0T11pRNT21pS2T31p\NT61pZ4T71p\0T;1p\4T<1pZDT>1p\JTD1").
Proof.
intros vals ebs so scr bls vbnd LBc LB LB' FF FF' LK LK' cr cr' A A' M M' model model' E P0 Hso Hscr HH HH' Hsub Hsub' Hbl Hvb.
pose proof Hsp as Hsp'.
assert (VIS : forall a, 0 <= a < 2 ^ 64 -> (a < 0x691000 \/ bv_unsigned sp0 - 8388608 <= a \/ in_block LBc a) ->
ahid A model (Z_to_bv 64 a) = false /\ ahid A' model' (Z_to_bv 64 a) = false).
{ intros a Ha Hc. split.
- apply (vis_of_inv _ _ _ _ _ _ _ a HH Ha). destruct Hc as [Hc|[Hc|Hc]]; auto.
- apply (vis_of_inv _ _ _ _ _ _ _ a HH' Ha). destruct Hc as [Hc|[Hc|Hc]]; auto. }
constructor; cbn [ev E]; rewrite ?P0.
- lia.
- lia.
- intros z Hz Hnot. unfold CPa. split; [|apply VIS; lia].
unfold aclient. right. left. rewrite (dla_sptop DL). lia.
- intros z Hz. right. unfold SCa. lia.
- intros i nb Hf. pose proof (sub_blockA_hz _ _ _ (Hbl i nb Hf)) as (Z1 & Z2 & Z3).
destruct (Hbl i nb Hf) as (cap & Hnb & Hin & HB). pose proof (hzA_of_block_range _ _ HB) as (Y1 & Y2 & Y3).
split; [lia|]. intros z Hz.
assert (IB : in_block LBc (bv_unsigned (vals_ev vals i) + z)).
{ exists (bv_unsigned (vals_ev vals i), cap). split; [exact Hin|]. cbn [fst snd]. lia. }
unfold CPa. split; [left; exact IB | apply VIS; [lia | right; right; exact IB]].
- exact Hvb.
- intros i [].
- intros lo hi Hin. pose proof (dla_client DL lo hi) as NS. destruct (img_client_rng lo hi Hin) as (I1 & I2 & I3).
split; [lia|]. split; [lia|]. intros a Ha. unfold CPa. split; [|apply VIS; lia]. unfold aclient. right. right. left.
rewrite (dla_img_lo DL), (dla_img_hi DL). split; [lia|]. exact (NS a Hin Ha).
- intros lo hi Hin. unfold IMG_RW_A in Hin. destruct Hin as [E1|[]]. injection E1 as <- <-. split; [lia|]. split; [lia|].
intros Mx d m Hd Hm.
apply (store_ok_window ASEGS Mx (Z_to_bv 64 0x65d350) (Z_to_bv 64 d) 65536%nat m 0x65d350 0x66d350);
first [exact wseg_stage | reflexivity | lia | (rewrite u_small by lia; lia)].
Qed.
Lemma regs_preserved_keptA : ltac2:(TCodec.tc2 tcn__Ja0DrvLib "J&R0y5'V8yR0%211%5241&RFr2r1%3221%819&TA&SF%23351'J&SIr4%221:r5%421<%63@31p081p[J<1p0>1pT@C1pT>D1").
Proof.
intros R R' HP r Hr. apply HP. unfold c_kept in Hr. unfold callee_saved_idx.
repeat (destruct Hr as [<-|Hr]; [cbn; tauto|]). destruct Hr.
Qed.
Lemma c_kept_no0A : ltac2:(TCodec.tc2 tcn__Ja0DrvLib "=&L&TA'V8y5%211(V6z(G%33521/015&SF%:3721%<11").
Proof. unfold c_kept. intros H. repeat (destruct H as [H|H]; [discriminate|]). exact H. Qed.
Lemma vals_ev_junkA : ltac2:(TCodec.tc2 tcn__Ja0DrvLib "Q6'<'V8yR0%211%411&R0y5%2214'=&Q2r1uQ0%3221'J&T?&7r4&SOr3%211%53A41&N&;%12D7r2%4221%<261&SI&V7&TH%116%32I1%52>1%D3N71p0F1pZNK1pT@M1p\JQ11").
Proof.
intros vals R' i Hi. rewrite vals_ev_app_r. unfold vals_ev, junk_vals. rewrite nth_map_seq by exact Hi. reflexivity.
Qed.
Lemma aclient_scr_mono : ltac2:(TCodec.tc2 tcn__Ja0DrvLib "Q1'<'A'Q5%2211%411&S4%611'I&TEzr2%3221r3%5231%7231&RJvQ=vTOr7r6r5r4%77654321<r8%97871653<p031p0<1pYNI1p\2J1p\0K1p\6L1pRBI1pRNL1").
Proof.
intros LB FF sp scr scr' a Hs Hc. unfold aclient, aclient_g in *.
destruct Hc as [Hc|[Hc|Hc]]; [left; exact Hc | right; left; split; [tauto | lia] | right; right; exact Hc].
Qed.
Definition has_window (kn : list kentry) : bool := existsb (kentry_eqb (KWr (SA (EVar 0) (-8388608)) 8388608)) kn.
Lemma has_window_nth : ltac2:(TCodec.tc2 tcn__Ja0DrvLib "Q1'<'T7%211'J'8&S@r1%211(B%63521'K'='?%11<&TCr3%23?1:(6(T3(T4(T1(5%211-XPPP0%5221+XPPP0%8221%:2J1%I3?<1qZNB1%D2C1p0F1p[4N1").
Proof.
intros kn H. unfold has_window in H. apply existsb_exists in H as (K & Hin & Heq). apply kentry_eqb_eq in Heq. subst K.
apply In_nth_error in Hin. exact Hin.
Qed.
Lemma window_store_ok : ltac2:(TCodec.tc2 tcn__Ja0DrvLib "R7'<'V8yR0%211%411'=y8%611%811p041'?%114p091'T7%>11'Q5'T5(T2&T?r6%211r5%5221&T:&T@r1r4%443261'J'8&S@%11:(B%53421r9(5%B221vV3%:3Q321&TE-XPPP0%221F&TDr7&TH%11J%4231z%9221&QDr:&V7&V9%12QC@r8%=221%52QF1%84Q171>%N3M1Jp0;1p0C1p0G1p0M1p0Q41tR>Q@Q:1p[<QL1p]2QC1p[4QE1pT8QH1pZDQL1p\JR21").
Proof.
intros vals ebs MV kn z m E HK Hw P0 Hz Hm. destruct (has_window_nth kn Hw) as [i Hn].
pose proof (kwr_store_ok ASEGS E MV kn i (EVar 0) (-8388608) 8388608 z m HK Hn ltac:(lia) ltac:(lia)) as W.
unfold adenot in W. cbn [a_base a_off edenot ev E] in W. rewrite P0 in W. unfold v_addi in W. exact W.
Qed.
Lemma segs_belowA : ltac2:(TCodec.tc2 tcn__Ja0DrvLib "8'J'8&R<&T@+VbTP0%3221(B%73621").
Proof. vm_compute. reflexivity. Qed.
Lemma store_ok_defined : ltac2:(TCodec.tc2 tcn__Ja0DrvLib "Q='V8yR0%211'?y8%511%311p051'Q5'I&TE+VbTP0r1%3221&TF&TJ+2+R0%3221%5271%;271'J'8&QD&T@r3&V7r2%22K1u1%746521(B%;3:21&Lr4%92Q2:%211(4%11Q1%B3Q131%711p091p0F1pYNQ31pT:Q51").
Proof.
intros Mx a Ha Hs. cbn [store_ok] in Hs. unfold wview in Hs.
destruct (Mx (Z_to_bv 64 a)) as [b|]; [discriminate|]. exfalso.
rewrite (find_segment1_none_above ASEGS 0x691000 (bv_unsigned (Z_to_bv 64 a)) segs_belowA) in Hs by (rewrite u_small by lia; lia). discriminate.
Qed.
Lemma window_defined : ltac2:(TCodec.tc2 tcn__Ja0DrvLib "R9'<'V8yR0%211%411'=y8%611%811p041'8p081'?%116p0;1'T7%@11'T5(T2&T?r5%211r4%5221&T:&T@r1&R:r3%2271r2%746521'J&S@%116(B%43J21r8(5%D221vV3%93Q621'Q5'I&TE&TK&V9%12Q=7+XPPP0%4221%621H&TF%12J5%:231&L&V7%12QFJ%D11(4%11QD%L3Q?31%711p091pYNE1p0G1p0M1p0Q31tR>QBQ<1p[4QD1pT4QG1pRFQK1pZDQN1p\JR41").
Proof.
intros vals ebs H M kn E HK Hw P0 a Ha. pose proof Hsp as Hsp'.
pose proof (window_store_ok vals ebs _ kn (a - bv_unsigned sp0) 1 HK Hw P0 ltac:(lia) ltac:(lia)) as W.
replace (bv_unsigned sp0 + (a - bv_unsigned sp0)) with a in W by ring.
apply (store_ok_of_mrestrict ASEGS) in W. apply store_ok_defined; [lia | exact W].
Qed.
Lemma astack_ok_of_window : ltac2:(TCodec.tc2 tcn__Ja0DrvLib "SB'<'V8yR0%211%411'=y8%611%811p041'8p081'?%116p0;1'T7%@11'Q5'A%1222%D11&S4%F11&RB&S9'T5(T2&T?r=%211r<%5221&T:&T@r1&R:r;%2271r:%746521'J&S@%116(B%43Q221r@(5%D221vV3%93Q>21'I&TE&TI&TJ+2+F%3221%511%721Lz%92N1%;231&TG+@%22Q41%I3Q@16%?27Q6+TP0%A2Q81%C231&S7vQ;r9rAr8%584Q?Q=Q7Q5321&RCrB&V9%12R=O&TK&S0vTO%211%4215%93861&S2vQ=rC&TD%12;A%55493Q>1p071p0B1p0I1p0N1p0Q31p0Q@1p0QF1p0QL1tR>R;R51pYLR=1p2RB1pZ>R@1pS4RB1pRBRC1pRNRF1p\0RJ1p\4RK1p[4RM1pT4S01pRFS41pZDS71p\JS=1").
Proof.
intros vals ebs H M kn so scr LB FF LK cr A V E HK Hw P0 Hso Hsoal Hscr HH Hdef. pose proof Hsp as Hsp'. pose proof Hal as Hal'.
unfold astack_ok. rewrite (dla_sptop DL), (dla_segs DL).
split; [rewrite Z.add_mod, Hal', Hsoal by lia; reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|]. split.
- intros d m Hd Hm. apply (store_ok_of_mrestrict ASEGS H).
replace (bv_unsigned sp0 + so - scr + d) with (bv_unsigned sp0 + (so - scr + d)) by ring.
apply (window_store_ok vals ebs _ kn _ m HK Hw P0); lia.
- intros i Hi. destruct (Z_lt_le_dec (bv_unsigned sp0 + so + i) (bv_unsigned sp0)) as [Hlt|Hge].
+ apply (window_defined vals ebs H M kn HK Hw P0). lia.
+ replace (bv_unsigned sp0 + so + i) with (bv_unsigned sp0 + (so + i)) by ring. apply Hdef. lia.
Qed.
Lemma kn_blkA_ok : ltac2:(TCodec.tc2 tcn__Ja0DrvLib "QI'<'V8yR0%211%411'=y8%611%811p041'?%114p091'Q5'T5(T2&T?r6%211r5%5221'Jr7r4%8221&V7r2%22I1%73I41r8(5%?221vV3%<3N21&RIvQ=vTO%3421>B&RC%13:DF&T:&T@r9&SH%12?F%544J31p071p0:1p0?1p0E1tR>Q4N1p\FQ61p[DQ71p\HQ@1pT:Q:1pZDQ>1p\JQD1").
Proof.
intros vals ebs Mx v n u E Pv P0 HBR Hdef. pose proof HBR as (_ & _ & B2 & B3 & _).
pose proof (hzA_of_block_range _ _ HBR) as (Z1 & Z2 & Z3). pose proof Hsp as Hsp'.
assert (EA : bv_unsigned (edenot E (EVar v)) = u) by (cbn [edenot ev E]; rewrite Pv; apply u_small; lia).
unfold kn_blkA, know_ok.
apply Forall_cons. { cbn [kentry_ok]. rewrite EA. lia. }
apply Forall_cons. { cbn [kentry_ok]. rewrite EA. split; [lia | exact B2]. }
apply Forall_cons.
{ cbn [kentry_ok]. split. { unfold flat, estart. cbn [a_base a_off]. rewrite EA. lia. }
intros d m Hd Hm. unfold estart. cbn [a_base a_off]. rewrite EA.
destruct m as [|m']; [reflexivity|]. set (m := Datatypes.S m') in *.
apply store_ok_of_all; [rewrite u_small by lia; lia|].
intros x Hx. rewrite u_small in Hx by lia.
specialize (Hdef (bv_unsigned x - u) ltac:(lia)). replace (u + (bv_unsigned x - u)) with (bv_unsigned x) in Hdef by lia.
rewrite Z_to_bv_bv_unsigned in Hdef. unfold wview. destruct (Mx x); [discriminate | exfalso; apply Hdef; reflexivity]. }
apply Forall_cons. { cbn [kentry_ok]. unfold estart. cbn [a_base a_off edenot ev E]. rewrite P0.
change (ev E v) with (vals_ev vals v). rewrite Pv, u_small by lia. right. lia. }
apply Forall_cons. { cbn [kentry_ok]. unfold estart. cbn [a_base a_off edenot ev E].
change (ev E v) with (vals_ev vals v). rewrite Pv, !u_small by lia. lia. }
apply Forall_nil.
Qed.
Lemma lzinv_of_inv : ltac2:(TCodec.tc2 tcn__Ja0DrvLib "QE'<'A'Q5%2211%411&S4%611&RB'V8yR0%211'?y8%511%311p051'QG&S7vQ;r7r6r5r4r3r2&S:r1%211%;8:9876541'R9%1286'J%E1F&QL%11;(4%11J%63531&R8&T@&RM%12EC%4431FDp061p0>1p0A1p[@N1pT4Q01p2Q<1pZ>Q:1pS4Q<1pRBQ=1pRNQ@1").
Proof.
intros LB FF LK cr A M model HH HM Hh.
destruct (aio_lazy _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (AWF & LZ).
unfold lzinv. split.
{ intros a Ha. unfold ahid, mkH in Ha. apply andb_prop in Ha as [Hl _].
apply (find_segment1_none_above ASEGS 0x691000 _ segs_belowA).
pose proof (LZ a Hl) as (Z1 & _). cbv zeta in Z1. rewrite (dla_img_hi DL) in Z1. exact Z1. }
split; [unfold ahid; apply lazy_cover_mkH; intros r Hr; exact Hr|].
split; [exact AWF|]. split; [exact HM | exact Hh].
Qed.
Lemma model_rt_halted : ltac2:(TCodec.tc2 tcn__Ja0DrvLib "C'QG&S6r2r1%3221'J'?'V8yR0%211%411&QL%11:r3%311%:3531p0<1p[>A1p[<B1").
Proof. intros m m' ->. destruct m; reflexivity. Qed.
Definition CWA (LB : list (Z * Z)) (a : Z) : Prop :=
in_block LB a \/ bv_unsigned sp0 - 8388608 <= a < bv_unsigned sp0 \/ (exists lo hi, In (lo, hi) IMG_W_A /\ lo <= a < hi).
Lemma img_w_client : ltac2:(TCodec.tc2 tcn__Ja0DrvLib "Q2'Q5&TA'A%1233(@r2r1%347721&SE%83621'K'I&SC%<3:61&TEr5%22;1r4%421<+RPP0%6215+VbTP0%8251%<231%=261%>291%?2=1qZLK1%B2L1q[8M1%D2N1p0F1pZJQ01p[6Q11").
Proof.
intros lo hi Hin. destruct (img_w_sub lo hi Hin) as (lo' & hi' & Hin' & H1 & H2). destruct (img_client_rng lo' hi' Hin') as (I1 & I2 & I3).
exists lo', hi'. split; [exact Hin'|]. split; [exact H1|]. split; [exact H2|].
unfold IMG_W_A in Hin. cbn [In] in Hin. repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-; lia|]). destruct Hin.
Qed.
Section SE.
Local Abbreviation SEC_T_cwa_not_bshadow := (ltac2:(TCodec.tc2 tcn__Ja0DrvLib "Q='<'A'Q5%2211%411&S4%611&RB'V8yR0%211'?y8%511%311p051&S9&S7vQ;r8r7r6r5r4r3r2%9887654321&S<r9%2214&L&S3r:%2219%411p061p0:1pYNQ31pYLF1pT4H1p2Q41pZ>Q21pS4Q41pRBQ51pRNQ81")) (only parsing).
Variable LB : ltac:(sec_ty2 constr:(SEC_T_cwa_not_bshadow) 0%nat 0%nat).
Variable FF : ltac:(sec_ty2 constr:(SEC_T_cwa_not_bshadow) 1%nat 0%nat).
Variable LK : ltac:(sec_ty2 constr:(SEC_T_cwa_not_bshadow) 2%nat 0%nat).
Variable cr : ltac:(sec_ty2 constr:(SEC_T_cwa_not_bshadow) 3%nat 0%nat).
Variable A : ltac:(sec_ty2 constr:(SEC_T_cwa_not_bshadow) 4%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_cwa_not_bshadow) 5%nat 0%nat).
Variable V : ltac:(sec_ty2 constr:(SEC_T_cwa_not_bshadow) 6%nat 0%nat).
Variable a : ltac:(sec_ty2 constr:(SEC_T_cwa_not_bshadow) 7%nat 0%nat).
Lemma cwa_not_bshadow : ltac:(sec_stmt2 constr:(SEC_T_cwa_not_bshadow) 8%nat 0%nat).
Proof.
intros HH HC (b' & Hb' & X').
pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & _).
destruct (WB b' Hb') as ((Q0 & _ & Q16 & Q3 & Q4 & Q5) & _). unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in Q5.
unfold in_shadow_of, S, SB in X'. rewrite (dla_sptop DL) in Q4. pose proof Hsp as HSP.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
destruct HC as [HB|[HS|(lo & hi & Hin & Hr)]].
- destruct HB as (b & Hb & X). pose proof (proj1 (WB b Hb)) as (Y0 & _ & _ & _ & Y & Y2). unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in Y2. lia.
- lia.
- destruct (img_w_client lo hi Hin) as (lo' & hi' & Hin' & H1 & H2 & H3 & H4). lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.
End SE.
Lemma cwa_not_private : ltac2:(TCodec.tc2 tcn__Ja0DrvLib "QK'<'A'Q5%2211%411&S4%611&RB'V8yR0%211'?y8%511%311p051&S9&S7vQ;r8r7r6r5r4r3r2%9887654321'I&TEz%2215&TF&TJ+2+R0%3221%52;1%:271&S<r:%221@&L&S1vQ=vTOr;%453217G%611p081p0<1p0H1pYNQA1pYLQ41pT4Q61p2QB1pZ>Q@1pS4QB1pRBQC1pRNQF1").
Proof.
intros LB FF LK cr A M V a HH Ha HC [NC|[RO|BS]]; [| |exact (cwa_not_bshadow _ _ _ _ _ _ _ a HH HC BS)].
- apply NC. unfold aclient. destruct HC as [HB|[HS|(lo & hi & Hin & Hr)]].
+ left. exact HB.
+ right. left. rewrite (dla_sptop DL). pose proof Hsp. lia.
+ right. right. left. destruct (img_w_client lo hi Hin) as (lo' & hi' & Hin' & H1 & H2 & H3 & H4).
rewrite (dla_img_lo DL), (dla_img_hi DL). split; [lia|]. apply (dla_client DL lo' hi' a Hin'). lia.
- pose proof (dla_ro_img DL a RO) as RI. destruct HC as [HB|[HS|(lo & hi & Hin & Hr)]].
+ destruct HB as (b & Hb & Hr). destruct (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WF & _).
destruct (WF b Hb) as (HBR & _). apply hzA_of_block_range in HBR. unfold hzA in HBR. lia.
+ pose proof Hsp. lia.
+ exact (dla_ro DL lo hi a Hin Hr RO).
Qed.
Lemma ainv_frame : ltac2:(TCodec.tc2 tcn__Ja0DrvLib "RH'<'A'Q5%2211%411&S4%611&RB'V8yR0%211'?y8%511%311p051p]062'QG&S7vQ;r9r8r7r6r5r4&S:r2%211%;8:9876541'I&TEzr1%3221&TF&TJ+2+R0%3221%5271%;271&L&S<r<%221B%411'J&V7r3%22Q91%M11%O12%63Q721p081p0>1pYNQF1%Q31H(4%11Q>%=3Q>31%C11%Q81Q3%@3QA14%F11p041pYNQH1&S9%Q:1Q;%Q;1Q=%G3321r=r;r:%QH8QG3N21QFQD5p051p0:1p0E1p0QA1p[BQN1p[@QO1pT6R11pT4R31p2R?1pZ>R=1pS4R?1pRBR@1pRNRC1").
Proof.
intros LB FF LK cr A M M' model model' HH FR GR EV. rewrite EV.
apply (aio_frame _ _ _ _ _ HIok LB FF LK cr A M M' _ HH); [|exact GR].
intros a Ha HP. apply FR; [exact Ha|]. intros HC. exact (cwa_not_private _ _ _ _ _ _ _ a HH Ha HC HP).
Qed.
Lemma sbm_vml : ltac2:(TCodec.tc2 tcn__Ja0DrvLib "?'QG&R;r2r1%3221'J&S9&S:%116r3%311%63531p081p[>=1p[<>1").
Proof. intros m m' ->. destruct m as [fd [maps lazy mat] io fsy pr lim tm]. reflexivity. Qed.
Lemma sbm_fds : ltac2:(TCodec.tc2 tcn__Ja0DrvLib "M'QG&R;r2r1%3221'I'J'<'A'V8yR0%211'QF%5221%711&QJ%11>r3%311%=3531&QC&QK%11D%216%B3421%D261p0F1p[>K1p[<L1").
Proof. intros m m' ->. destruct m as [fd [maps lazy mat] io fsy pr lim tm]. split; reflexivity. Qed.
Lemma model_rt_fds : ltac2:(TCodec.tc2 tcn__Ja0DrvLib "M'QG&S6r2r1%3221'I'J'<'A'V8yR0%211'QF%5221%711&QJ%11>r3%311%=3531&QC&QK%11D%216%B3421%D261p0F1p[>K1p[<L1").
Proof. intros m m' ->. destruct m; split; reflexivity. Qed.
Lemma regions_writeA : ltac2:(TCodec.tc2 tcn__Ja0DrvLib "RN'<'V8yR0%211%411'=y8%611%811p041'A'Q5%2271%=11%4233%?11&S4%A11&RB'?%11=p0B1&S9'T5(T2&T?r:%211r9%5221'Jr;(5%8221vV3%53Q021&S7vQ;r8r7r6r5r4r3%887@654321%J1Q2&R=r2r=%3221(6r1%22Q91%G3841&SB&V9r@%Q021>%32QH1%53;1<p071p[FQB1pZNQI1'R?&T@&TJ+2+Q8%3221r<(>%11QK%21R3&SE%41QL&S<%11Q='Hq0R31%@<?Q?;;:8765Q531p0B1p0Q51p0Q?1tR>QLQF1pYLQN1pT4R01p2R71pZ>R51pS4R71pRBR81pRNR;1pZ4R>1pZDRC1p\JRI1").
Proof.
intros vals ebs bls LB FF LK cr A M V E P0 HH Hbl. pose proof Hsp as Hsp'.
constructor; cbn [ev E]; rewrite ?P0.
- lia.
- lia.
- intros z Hz Hnot. unfold CWA. right. left. lia.
- intros z Hz. right. exact I.
- intros i nb Hf. pose proof (sub_blockA_hz _ _ _ (Hbl i nb Hf)) as (Z1 & Z2 & Z3).
destruct (Hbl i nb Hf) as (cap & Hnb & Hin & HB). split; [lia|]. intros z Hz. unfold CWA. left.
exists (bv_unsigned (vals_ev vals i), cap). split; [exact Hin|]. cbn [fst snd]. lia.
- intros v b Hf. discriminate.
- intros i [].
- intros lo hi Hin. destruct (img_w_client lo hi Hin) as (_ & _ & _ & _ & _ & H3 & H4).
split; [lia|]. split; [lia|]. intros a Ha. unfold CWA. right. right. exists lo, hi. auto.
- intros lo hi [].
Qed.
Lemma block_frame : ltac2:(TCodec.tc2 tcn__Ja0DrvLib "TC'<'V8yR0%211%411'=y8%611%811p041'A'Q5%2271%=11%4233%?11&S4%A11&RB'?%11=p0B1'QG'T9%H11'T5(T2&T?r<%211r;%5221'Jr=(5%8221vV3%53Q221&S7vQ;r:r9r8r7r6&S:r4%211%:89B876541%N1Q6&R=r2r?%3221(6r1%22Q=1%I3841&SB&V9rBr3%Q3221%42QM1%63<1=p081p[FQG1pZNQN1'8&R>&TJ+2+Q8%3221r>(>%11R7&SEr5%:7Q=665321(B%QA3=21&R:&RM%12Q<Q9%321Q;&T;%523Q>%23:1Q<%QI3R441%73QNQAQ3%QK3G1;%QN1Q9%R11Q:%QN3R:21p041pYNRM1'I&TEz%221Q=&TF+R0%Q12Q01%32QA1%8251&L&S<%12Q@QI%311&V7%12S=QB%R?11%Q712%RB3RN21p061p0;1pYNS:1%RJ1QO(4%11SA%RI3S531%@11%RK3S7N3%B11p031pYNSK1%N2:1p0Q01p0Q81p0QA1p0R01p0RD1p0S01tR>S=S71p[:S?1p[@SB1pT6SD1pT4SE1p2SL1pZ>SJ1pS4SL1pRBSM1pRNT01pZ4T31pZDT81p\JT>1").
Proof.
intros vals ebs bls LB FF LK cr A M M' model log E P0 HH Hbl Hlog EQM EQH.
pose proof (regions_writeA vals ebs bls LB FF LK cr A M _ P0 HH Hbl) as RG.
split.
- intros a Ha HC. destruct (ahid A model (Z_to_bv 64 a)) eqn:Hh; [apply EQH; exact Hh|].
assert (E1 : M' (Z_to_bv 64 a) = mrestrict (ahid A model) M' (Z_to_bv 64 a)) by (unfold mrestrict; rewrite Hh; reflexivity).
rewrite E1, EQM.
rewrite (mem_denot_frame_Z ASEGS 0 (2 ^ 40) (2 ^ 40) bls [] [] IMG_W_A _ (CWA LB) (fun _ => True) [] RG _ log a Hlog Ha HC).
unfold mrestrict. rewrite Hh. reflexivity.
- intros a Hd. destruct (ahid A model a) eqn:Hh; [rewrite (EQH a Hh); exact Hd|].
assert (E1 : M' a = mrestrict (ahid A model) M' a) by (unfold mrestrict; rewrite Hh; reflexivity).
rewrite E1, EQM. apply (mem_denot_grows E (mrestrict (ahid A model) M) log a). unfold mrestrict. rewrite Hh. exact Hd.
Qed.
Variable M0 : word -> option byte.
Definition STKTOP : Z := Z.max (ar_sptop ar) (ar_stack_top ar).
Lemma stksh_rng : ltac2:(TCodec.tc2 tcn__Ja0DrvLib "R1'<'A'Q5%2211%411&S4%611&RB'V8yR0%211'?y8%511%311p051&S9&S7vQ;r8r7r6r5r4r3r2%9887654321&S5&TK&ROvTO%211+XPPP0%5221&S>%7212%9331;'I&TE&TD+QoooPP0+_oogoPPP0%3221%521C+_oooooooO%6251%82F1%:241&TJ+2+Q?%3221%H21C%J3D1M%A271p0C1p0N1p]0QG1pYLQ:1pT4Q<1p2QH1pZ>QF1pS4QH1pRBQI1pRNQL1").
Proof.
intros LB FF LK cr A M V x HH HS. pose proof Hsp as Hsp'.
destruct (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & TOP & _).
unfold in_shadow_of, S, SB, STKTOP in *. rewrite (dla_sptop DL) in *.
assert (X2 : x <= 0x7fff8000 + (Z.max (bv_unsigned sp0) (ar_stack_top ar) - 1) / 8).
{ destruct HS as [_ HS]. replace (bv_unsigned sp0 - 8388608 + (Z.max (bv_unsigned sp0) (ar_stack_top ar) - (bv_unsigned sp0 - 8388608)) - 1)
with (Z.max (bv_unsigned sp0) (ar_stack_top ar) - 1) in HS by ring. lia. }
assert (D1 : (0x7fff80000000 - 8388608) / 8 <= (bv_unsigned sp0 - 8388608) / 8) by (apply Z.div_le_mono; lia).
assert (D2 : (Z.max (bv_unsigned sp0) (ar_stack_top ar) - 1) / 8 <= (2 ^ 47 - 1) / 8) by (apply Z.div_le_mono; lia).
replace (bv_unsigned sp0 - 8388608 + (2 ^ 47 - (bv_unsigned sp0 - 8388608)) - 1) with (2 ^ 47 - 1) by ring.
change ((0x7fff80000000 - 8388608) / 8) with 0xfffeff00000 in D1. change ((2 ^ 47 - 1) / 8) with 0xfffffffffff in D2 |- *. lia.
Qed.
Record dinv (LB : list (Z * Z)) (LK : list fframe) (cr : credit) (A : list (Z * Z)) (M : word -> option byte) (model : Model) : Prop := DINV {
di_inv : ri_inv HI LB [] LK cr A M (vml_of model);
di_minv : MInv A model;
di_halt : m_halted model = None;
di_above : forall a, bv_unsigned sp0 <= a < 2 ^ 47 -> M (Z_to_bv 64 a) = M0 (Z_to_bv 64 a);
di_stksh : forall x, in_shadow_of (ahl_ceil ar) (STKTOP - ahl_ceil ar) x -> byte_at M x 0;
di_hish : forall x, in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) x -> byte_at M x 0
}.
Lemma dinv_lzinv : ltac2:(TCodec.tc2 tcn__Ja0DrvLib "Q5'<'A'Q5%2211%411&S4%611&RB'V8yR0%211'?y8%511%311p051'QG'S?r6r5r4r3r2r1%76654321&R8&T@&RM%1286%443197p061p[@?1pT4A1p2M1pZ>K1pS4M1pRNQ01").
Proof. intros LB LK cr A M model D. exact (lzinv_of_inv _ _ _ _ _ _ _ (di_inv _ _ _ _ _ _ D) (di_minv _ _ _ _ _ _ D) (di_halt _ _ _ _ _ _ D)). Qed.
Lemma stksh_not_cwa : ltac2:(TCodec.tc2 tcn__Ja0DrvLib "QD'<'A'Q5%2211%411&S4%611&RB'V8yR0%211'?y8%511%311p051&S9&S7vQ;r8r7r6r5r4r3r2%9887654321&S5&TK&ROvTO%211+XPPP0%5221&S>%7212%9331;&L&S<r:%221@%411p061p0A1p]0Q:1pYLM1pT4O1p2Q;1pZ>Q91pS4Q;1pRBQ<1pRNQ?1").
Proof.
intros LB FF LK cr A M V x HH HS HC. pose proof Hsp as Hsp'. destruct (stksh_rng _ _ _ _ _ _ _ x HH HS) as ((X1 & X2) & _).
destruct HC as [HB|[HSt|(lo & hi & Hin & Hr)]].
- destruct HB as (b & Hb & Hr). destruct (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WF & _).
destruct (WF b Hb) as (HBR & _). destruct HBR as (_ & _ & _ & _ & _ & (_ & AM & _)). unfold BIGSHADOW_LO, BIGSHADOW_HI in AM. lia.
- lia.
- destruct (img_w_client lo hi Hin) as (_ & _ & _ & _ & _ & H3 & H4). lia.
Qed.
Lemma hish_rng : ltac2:(TCodec.tc2 tcn__Ja0DrvLib "M'Q5&S5&TK&ROvTO%211+XPPP0%5221&TJ+2+Q?%3221%:215r1%=3721'I&TE&TD+QoooPP0+_oogoPPP0%3221r2%6221+_oooooooO%7261%9241%;241p0=1p]0L1").
Proof.
intros x HS. pose proof Hsp as Hsp'. unfold in_shadow_of, S, SB, ahl_ceil in *. rewrite (dla_sptop DL) in *.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
clear - HS Hsp'. lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Lemma hish_not_cwa : ltac2:(TCodec.tc2 tcn__Ja0DrvLib "QG'<'A'Q5%2211%411&S4%611&RB'V8yR0%211'?y8%511%311p051&S9&S7vQ;r8r7r6r5r4r3r2%9887654321&S5&TK&ROvTO%211+XPPP0%5221&TJ+2+Q?%3221%:215%<361>&L&S<r:%221C%411p061p0D1p]0Q=1pYLQ01pT4Q21p2Q>1pZ>Q<1pS4Q>1pRBQ?1pRNQB1").
Proof.
intros LB FF LK cr A M V x HH HS HC. pose proof Hsp as Hsp'. destruct (hish_rng x HS) as (X1 & X2).
destruct HC as [HB|[HSt|(lo & hi & Hin & Hr)]].
- destruct HB as (b & Hb & Hr). destruct (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WF & _).
destruct (WF b Hb) as (HBR & _). destruct HBR as (_ & _ & _ & _ & _ & (_ & AM & _)). unfold BIGSHADOW_LO, BIGSHADOW_HI in AM. lia.
- lia.
- destruct (img_w_client lo hi Hin) as (_ & _ & _ & _ & _ & H3 & H4). lia.
Qed.
Lemma dinv_frame : ltac2:(TCodec.tc2 tcn__Ja0DrvLib "RN'<'A'Q5%2211%411&S4%611&RB'V8yR0%211'?y8%511%311p051p]062'QG'S?r8r7r6r5r4r2%76654321'I&TEzr1%3221&TF&TJ+2+R0%3221%5271%;271&L&S<r;%221A%411'J&V7r3%22Q51%K11%M12%63Q321p081p0>1pYNQB1%Q11H(4%11Q:%=3Q:31%C11%Q61Q2%@3Q=14%F11p041pYNQD1&S9&S:%11Q:%21Q<%H3421'R9r9%221Q@%QL1QM&QL%11QD%D1R0%Q03421r>r=r<%QM6321Q7:QKp051p0;1p0?1p0E1p0Q01p0QL1p[BR51p[@R61pT6R81pT4R:1p2RF1pZ>RD1pS4RF1pRNRI1").
Proof.
intros LB LK cr A M M' model model' D FR GR EV MI HL. pose proof Hsp as Hsp'. constructor.
- exact (ainv_frame _ _ _ _ _ _ _ _ _ (di_inv _ _ _ _ _ _ D) FR GR EV).
- exact MI.
- exact HL.
- intros a Ha. rewrite <- (di_above _ _ _ _ _ _ D a Ha). apply FR; [lia|].
intros [HB|[HSt|(lo & hi & Hin & Hr)]].
+ destruct HB as (b & Hb & Hr). destruct (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ (di_inv _ _ _ _ _ _ D)) as (WF & _).
destruct (WF b Hb) as (HBR & _). apply hzA_of_block_range in HBR. unfold hzA in HBR. lia.
+ lia.
+ destruct (img_w_client lo hi Hin) as (_ & _ & _ & _ & _ & H3 & H4). lia.
- intros x Hx. unfold byte_at. rewrite FR; [exact (di_stksh _ _ _ _ _ _ D x Hx) | | exact (stksh_not_cwa _ _ _ _ _ _ _ x (di_inv _ _ _ _ _ _ D) Hx)].
destruct (stksh_rng _ _ _ _ _ _ _ x (di_inv _ _ _ _ _ _ D) Hx) as (X & _). lia.
- intros x Hx. unfold byte_at. rewrite FR; [exact (di_hish _ _ _ _ _ _ D x Hx) | | exact (hish_not_cwa _ _ _ _ _ _ _ x (di_inv _ _ _ _ _ _ D) Hx)].
pose proof (hish_rng x Hx). lia.
Qed.
Lemma dinv_block : ltac2:(TCodec.tc2 tcn__Ja0DrvLib "SK'<'V8yR0%211%411'=y8%611%811p041'A'Q5%2271%=11%4233%?11&S4%A11&RB'?%11=p0B1'QG'T9%H11'T5(T2&T?r<%211r;%5221'Jr=(5%8221vV3%53Q221'S?r:r9r8r7r5%66>54321%J1Q2&R=r2r?%3221(6r1%22Q91%E3841&SB&V9rBr3%O221%42QI1%63<1=p081p[FQC1pZNQJ1'8&R>&TJ+2+Q8%3221r>(>%11R3&SE%97Q855421O(B%Q<3<21&R:&RM%12QAQ6%321Q8&T;%523Q;r6%33Q921%QE3R051%83QEQ?Q3%QG3G1<%QL1Q9%QH1Q:%QJ3R621p041pYNRI1&R8&T@%A2QNQH%3421QOQH&R;%12R4QKrAr@%QO6Q=21QER4R7p041p071p0<1p0D1p0N1p0Q<1p0R01p0R81tR>RER?1p[:RG1p[BRJ1p[@RK1pT6RM1pT4RN1p2S51pZ>S31pS4S51pRNS81pZ4S;1pZDS@1p\JSF1").
Proof.
intros vals ebs bls LB LK cr A M M' model model' log E P0 D Hbl Hlog EQM EQH HZ SBM.
destruct (block_frame vals ebs bls LB [] LK cr A M M' model log P0 (di_inv _ _ _ _ _ _ D) Hbl Hlog EQM EQH) as (FR & GR).
destruct HZ as (_ & _ & _ & MI & HL).
exact (dinv_frame _ _ _ _ _ _ _ _ D FR GR (sbm_vml _ _ SBM) MI HL).
Qed.
Lemma minv_same_vm : ltac2:(TCodec.tc2 tcn__Ja0DrvLib "I'<'A'Q5%2211%411'QG'J'QH&QMr1%211r2%411%73631'R9r4r3%3221r5%5213p031p081p[>A1p[<B1p2D1").
Proof.
intros A m m' EV [I1 I2 I3 I4 I5].
constructor; unfold m_vm_materialized, m_vm_lazy, m_vmmaps, eager_used, m_vmmaps, m_vm_lazy in *; rewrite EV; assumption.
Qed.
Lemma vml_same_vm : ltac2:(TCodec.tc2 tcn__Ja0DrvLib "B'QG'J'QH&QMr1%211r2%411%73631&S9&S:%115r3%311%=3531p071p[>@1p[<A1").
Proof. intros m m' EV. unfold vml_of, m_vmmaps, m_vm_lazy. rewrite EV. reflexivity. Qed.
Lemma with_fds_vm : ltac2:(TCodec.tc2 tcn__Ja0DrvLib "E'<'A'V8yR0%211'QF%5221%711'QG'J'QH&QM&QOr2r1%3221%511%613%93821p[<;1pZF=1").
Proof. intros f m. destruct m. reflexivity. Qed.
Lemma with_fds_fs : ltac2:(TCodec.tc2 tcn__Ja0DrvLib "E'<'A'V8yR0%211'QF%5221%711'QG'J&QC&QK&QOr2r1%3221%511%613%93821p[<;1pZF=1").
Proof. intros f m. destruct m. reflexivity. Qed.
Lemma with_fds_fds : ltac2:(TCodec.tc2 tcn__Ja0DrvLib "C'<'A'V8yR0%211'QF%5221%711'QG'J&QJ&QOr2r1%3221%511%73914p[<91pZF;1").
Proof. intros f m. destruct m as [[t p] v i fsy pr l tm]. reflexivity. Qed.
Lemma ahid_same_lazy : ltac2:(TCodec.tc2 tcn__Ja0DrvLib "N'<'A'Q5%2211%411'QG'J'V8yR0%211%9211%;11&QNr1%211r2%411%;3631'8p0:1&RMr4%2217r3%4231%C3631p091p[>F1p[<G1p2I1").
Proof. intros A m m' EL. unfold ahid. rewrite EL. reflexivity. Qed.
Lemma ahid_sbm : ltac2:(TCodec.tc2 tcn__Ja0DrvLib "J'<'A'Q5%2211%411'QG&R;r2r1%3221'J'V8yR0%211'8p021&RMr4%221;r3%4231%;3631p0=1p[>B1p[<C1p2E1").
Proof. intros A m m' SB. apply ahid_same_lazy. exact (sbm_lazy_eq _ _ SB). Qed.
Lemma dinv_model : ltac2:(TCodec.tc2 tcn__Ja0DrvLib "QC'<'A'Q5%2211%411&S4%611&RB'V8yR0%211'?y8%511%311p051'QG'S?r7r6r5r4r3r2%76654321'J'QH&QM%115%217%53421%D1E&QL%11;(4%11I%;3531r:r9r8%G6321FECp051p0<1p0C1p[BL1p[@M1pT4O1p2Q;1pZ>Q91pS4Q;1pRNQ>1").
Proof.
intros LB LK cr A M model model' D EV HL.
apply (dinv_frame LB LK cr A M M model model' D); [reflexivity | auto | exact (vml_same_vm _ _ EV) | exact (minv_same_vm _ _ _ EV (di_minv _ _ _ _ _ _ D)) | exact HL].
Qed.
Hypothesis M0_def : defined M0 (bv_unsigned sp0) (ar_stack_top ar - bv_unsigned sp0).
Lemma dinv_stack_defined : ltac2:(TCodec.tc2 tcn__Ja0DrvLib "Q:'<'A'Q5%2211%411&S4%611&RB'V8yR0%211'?y8%511%311p051'QG'S?r6r5r4r3r2r1%76654321&RC&V9vV3%22C1&TK&S0vTO%211%4215%93=61p0;1p[@D1pT4F1p2Q21pZ>Q01pS4Q21pRNQ51").
Proof.
intros LB LK cr A M model D i Hi.
destruct (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ (di_inv _ _ _ _ _ _ D)) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & TOP & _).
rewrite (di_above _ _ _ _ _ _ D) by lia. apply M0_def. exact Hi.
Qed.
Lemma dinv_call : ltac2:(TCodec.tc2 tcn__Ja0DrvLib "S4'<'A'Q5%2211%411&S4%611&RB'V8yR0%211'?y8%511%311p051p]062'QG'S?r?r<r:r8r6r4%76654321&TEr3&V9vV3%22E1%5241'Izr1%9221&TF&TJ+2+R0%3221%5271%:271&RJvQ=vTOrB(>%11Q;r5r2%877653L21'J&V7%12Q=K%Q211r;%113%63Q<31p081p0B1pYNQK1&S7vQ;r@r>&S:%11Q<%6854D3Q@Q?Q>1'R9r7%22?1&S6r9%221QDrCrAr=%QL632QK1F5p051p091p0=1p0E1p0QD1p0QK1p\0RC1p\6RD1p[BR61p[@R71pT6R91pT4R;1p4RG1p2RH1pZ@RF1pZ>RG1pS6RI1pS4RJ1pS0RM1pS2RN1pRNRO1").
Proof.
intros LB LBc LB' LK LK' cr cr' A A' M M' model model' sp scr D Hsp1 PR HH' MI RT. pose proof Hsp as Hsp'. constructor.
- exact HH'.
- exact MI.
- rewrite (model_rt_halted _ _ RT). exact (di_halt _ _ _ _ _ _ D).
- intros a Ha. rewrite <- (di_above _ _ _ _ _ _ D a Ha). apply PR; [lia|]. unfold aclient. right. left. rewrite (dla_sptop DL). lia.
- intros x Hx. destruct (stksh_rng _ _ _ _ _ _ _ x (di_inv _ _ _ _ _ _ D) Hx) as (X & XC).
unfold byte_at. rewrite PR; [exact (di_stksh _ _ _ _ _ _ D x Hx) | lia | unfold aclient; right; right; right; right; left; exact XC].
- intros x Hx. pose proof (hish_rng x Hx) as X.
unfold byte_at. rewrite PR; [exact (di_hish _ _ _ _ _ _ D x Hx) | lia | unfold aclient; right; right; right; right; left; exact Hx].
Qed.
Lemma amalloc_site : ltac2:(TCodec.tc2 tcn__Ja0DrvLib "[M'<'V8yR0%211%411'=y8%611%811p041'T6%;11'T7%=11&R0y5%221='?%11;p0@1'QG'A'Q5%2211%H11&S4%J11&RB%72G6%M11'QI%O11!p]021'T5(T2&T?rA%211r@%5221&T<r1r>%33251&T:&T@r2&R:&RMr9r=%3221%521:%94871?'J'8&T>&;rD%22QI1rB%5221(B%93821&T=rE%92R01%3217%>3=16'Q1u1rF%?2R61%4231rG(5%Q9221vV3%H3R<21&S@%11?%K3J1C&SI(V6+2(G%33R821%52F1&V7&TD&V9%12RJ>%321Q:%52RL1%Q83RL71'I&TE&TI&TJ+F%22@1%411%621QLz%82QN1%:231&TGr?+@%3221%QH3RI17rH+:%N3S31L%Q0231%K2SBR?%QN3SB21&TF%12?QJ+K%F2Q41%I2QM1%K241&RKvQ=rC%332QM1rK+4%Q>3SC1Q<%Q@231+V]k\0%Q<2T31%R?3T331rL+1%QE3SJ1QC%QG231%RD3T81G%Q;2Q4R?+R0%Q;2QI1%I2RB1%Q@241%Q62CQL%RK3SL1Q:'S?rJrIrNrM%56AH4321%T81T3&R=%12S<6(6%12T7SC%S73531&Q2r3rQ7%S82TO1%4231&SBrQ0%T2256%R<2U51%4331SI%R9261p0<1p[FTE1pZNU71rQ8%SD2U;1%@2?1%T<23@%RF2U?1%RA21T3%RC241p0F1pZ2TO1p\HUA1(>%11TJ%SA11&7rQ<&SOr5%211%53UL41%TL1TF%TN216%T82UOTC&NrQ>%T;2V21uQ0%4221%TA3V361rQ?%T@2V71u:%9221%U92Q=1r4%SF2V=1%TI3V=31&T0&Q3%VB1V4&T8&SF%443VA21rQ@%TN2VE1%83E31%UA3QJ1U8r7r8%U<221%U>21U<&SHrQA%U72VN1%O21GrQ6%5221&SGrQ5+TP0rQ4rQ3%554321Q6%QA3VO71%UO4UNN>1(9(@%14VIVIDR>rQ;%43VJ21rQ:&RLrQ9%23SH1RDr:%S46652K1V5&S6rQ=%2214&TB%13W5:6&RIvTO%24T219=&RAr;%231BQI&S8r<%23TI1R:%U52U:VL+Q?%U52UC1%TC2VO1%U:241%UB2X9VL%V?11rQE%113%VH3WM31p061pYNWK1%UA2U:W8%TM2W9T5%UD221&RDrQD%221W8%UO2XFSH%VN11rQG%113%W53X:31p061p0:1pYNX91&TA%QC4X;X;T1WB&SC%33X<21%V32RFWE%U?2WFT5%V6221%VL1?rQJ%11A%WC3XH31p051p091pYNXG1pZJXH1p[6XI1'SMvUN(QE&SJvU;%VL2YCSJ&SL%11X9%554WM3UJ1%721WL%:4X<91R:p0<1p0M1p0Q<1p0QI1p0QM1p0R11p0R51p0R81p0R<1p0RH1p0S;1p0SF1p0SO1tR@Y6T71t\LZ5T:1p\FYD1p4YC1p[BYH1pT6YJ1pT@YN1+_Sf0%WG2Z>1%N5MS91S8JrQ2%Q1221%Q44Y6Q31W4p071p0TM1p0U11p0U<1p0V11p0V81p0V;1p0VA1p0VG1p0VO1p0W41p0W;1p0WB1p0WH1p0X41p0XB1p0XF1p0XL1p0Y21p0Y81p0YC1p0YN1tR>Z9Z31pRJZ;1p[LZG1p\NZA1pZ4ZB1p\4ZJ1p[DZK1p2ZJ1pZ>ZH1pS4ZJ1pRNZM1p[@[21pT4[41pT>[81p[4[<1p\:[?1pZD[B1p\J[H1").
Proof.
intros vals ebs sr kn R M model LB LK cr A n so bls vbnd ra K E HR HK Hsv Hkv HL1 P0 Hiw
R2 Hso Hsoal R10 Hn Hcr R4 R1 Hra Hra2 DI Hbl Hvb HK0 CONT.
set (FF := @nil fframe) in *.
pose proof (di_inv _ _ _ _ _ _ DI) as HH. pose proof (di_halt _ _ _ _ _ _ DI) as Hh. pose proof (di_minv _ _ _ _ _ _ DI) as HMI.
pose proof (dinv_stack_defined _ _ _ _ _ _ DI) as Hdef.
pose proof Hsp as Hsp'. pose proof (dla_scr DL) as (SC1 & SC2 & SC3).
pose proof (aio_malloc _ _ _ _ _ HIok fx R M model LB FF LK cr A n K) as MS.
cbv zeta in MS. rewrite (dla_segs DL), (dla_malloc DL), (dla_tp DL) in MS. rewrite R1 in MS.
apply MS; clear MS; try assumption.
- apply ret_ok_even. rewrite u_small by lia. exact Hra2.
- rewrite R2, u_small by lia.
eapply (astack_ok_of_window vals ebs (ahid A model) M kn so); eauto; lia.
- unfold amalloc_post. intros R' M' model' A' u HA HP HBR HAP HFA HDEF HSHB HPRES HRT HINC HMI' HH'.
rewrite (dla_segs DL), R1. rewrite R2, u_small in HPRES by lia. destruct HPRES as (PR1 & PR2).
assert (Hh' : m_halted model' = None) by (rewrite (model_rt_halted _ _ HRT); exact Hh).
assert (HL' : length (vals ++ junk_vals R') = (length vals + 32)%nat) by (rewrite length_app, junk_vals_length; reflexivity).
assert (HA' : vals_ev (vals ++ junk_vals R') (length vals + 10) = Z_to_bv 64 u) by (rewrite vals_ev_junkA by lia; exact HA).
assert (P0' : vals_ev (vals ++ junk_vals R') 0 = sp0) by (rewrite vals_ev_app_l by lia; exact P0).
assert (CLI : forall a, aclient L ar LB FF (bv_unsigned sp0 + so) 4096 a -> aclient L ar LB FF (bv_unsigned sp0 + so) (hl_scr_malloc L) a)
by (intros a; apply aclient_scr_mono; lia).
apply (CONT R' M' model' A' u HL' HA'); try assumption.
+ apply (regs_after_keeps vals ebs sr R R' c_kept Hsv HR (regs_preserved_keptA R R' HP) c_kept_no0A).
+ apply Forall_app. split.
* eapply kn_blkA_ok; [exact HA' | exact P0' | exact HBR |].
intros i Hi. unfold mrestrict.
rewrite (vis_of_inv _ _ _ _ _ _ _ (u + i) HH'); [apply HDEF; exact Hi | destruct HBR as (B1 & _ & _ & _ & B5 & _); rewrite (dla_sptop DL) in B5; lia |].
right. right. exists (u, n). split; [left; reflexivity | cbn [fst snd]; lia].
* unfold keep_allocA.
pose proof (env_app_know ASEGS vals (junk_vals R') ebs _ kn Hkv HK) as HK1.
refine (know_keep_sound ASEGS 0 so 4096 bls vbnd [] IMG_CLIENT_A IMG_RW_A
(Env (vals_ev (vals ++ junk_vals R')) ebs)
(CPa LB FF (bv_unsigned sp0 + so) 4096 (ahid A model) (ahid A' model')) (SCa (bv_unsigned sp0 + so) 4096)
_ (mrestrict (ahid A model) M) (mrestrict (ahid A' model') M') _ _ kn HK1).
-- eapply (regions_callA (vals ++ junk_vals R') ebs so 4096 bls vbnd LB LB ((u, n) :: LB) FF FF LK LK cr (adebit L cr n) A A' M M' model model');
[exact P0' | exact Hso | lia | exact HH | exact HH' | | | | ].
++ intros a Ha; exact Ha.
++ intros a (b & Hb & Hr). exists b. split; [right; exact Hb | exact Hr].
++ intros i nb Hf. destruct (Hbl i nb Hf) as (Hi32 & H1). rewrite vals_ev_app_l by exact Hi32. exact H1.
++ intros v b Hf. destruct (Hvb v b Hf) as [Hv H1]. rewrite vals_ev_app_l by exact Hv. exact H1.
-- intros a Ha (HC & V1 & V2). unfold mrestrict. rewrite V1, V2. apply PR1; [exact Ha | apply CLI; exact HC].
-- intros a HS. unfold SCa in HS. unfold mrestrict.
rewrite (vis_of_inv _ _ _ _ _ _ _ a HH') by lia.
destruct (Z_lt_le_dec a (bv_unsigned sp0 + so - hl_scr_malloc L)) as [Hlo|Hhi].
++ rewrite PR1; [apply (window_defined vals ebs (ahid A model) M kn HK Hiw P0); lia | lia |].
unfold aclient. right. left. rewrite (dla_sptop DL). lia.
++ apply PR2. lia.
+
apply (dinv_call LB LB ((u, n) :: LB) LK LK cr (adebit L cr n) A A' M M' model model' (bv_unsigned sp0 + so) (hl_scr_malloc L) DI ltac:(lia)); assumption.
+ intros a Ha. apply PR1; [lia|]. unfold aclient. right. left. rewrite (dla_sptop DL). lia.
+ intros a Ha Hb. apply PR1; [exact Ha | left; exact Hb].
+ intros lo hi a Hin Ha. assert (0 <= a < 2 ^ 64).
{ destruct (img_client_rng lo hi Hin) as (I1 & I2 & I3). lia. }
apply PR1; [assumption|]. unfold aclient. right. right. left. rewrite (dla_img_lo DL), (dla_img_hi DL).
split; [destruct (img_client_rng lo hi Hin) as (I1 & I2 & I3); lia | exact (dla_client DL lo hi a Hin Ha)].
Qed.
Lemma in_lb_remove_in : ltac2:(TCodec.tc2 tcn__Ja0DrvLib "A'Q5'<'A%1233%311&TAr1&REr3r2%3221%63851%73934p021pZ2;1pRN;1p\F@1").
Proof.
intros u LB b. induction LB as [|c LB' IH]; [intros []|]. cbn [lb_remove].
destruct (Z.eqb (fst c) u); [intros H; right; exact H|]. intros [<-|H]; [left; reflexivity | right; apply IH; exact H].
Qed.
Lemma in_block_remove : ltac2:(TCodec.tc2 tcn__Ja0DrvLib "A'Q5'<'A%1233%311&RD&REr3r2%3221r1%6221%7254p021pYN>1pRN;1p\F@1").
Proof. intros u LB a (b & Hb & Hr). exists b. split; [exact (in_lb_remove_in u LB b Hb) | exact Hr]. Qed.
Lemma afree_site : ltac2:(TCodec.tc2 tcn__Ja0DrvLib "ZJ'<'V8yR0%211%411'=y8%611%811p041'T6%;11'T7%=11&R0y5%221='?%11;p0@1'QG'A'Q5%2211%H11&S4%J11&RB%72G6%M11'QI%O11!p]021'T5(T2&T?rB%211rA%5221&T<r1r?%33251&T:&T@r2&R:&RMr:r>%3221%521:%94871?'J'8&T>&;rE%22QI1rC%5221(B%93821&T=rF%92R01%3217%>3=16'Q1u1rG%?2R61%4231rH(5%Q9221vV3%H3R<21&S@%11?%K3J1C&SI(V6+2(G%33R821%52F1&V7&TD&V9%12RJ>r=%4221%62RM1%Q93RM81'I&TE&TI&TJ+F%22A1%411%621QEz%82QG1%:231&TG+@%22R31%QH3RI16&TA(@%14RLRLR=R;%33RL1QArJ+:%Q23S71Q0%Q4231%O2SFQK%R23SF21rK+4%Q83S=1Q6%Q:231+V]k\0%Q62SM1%R93SM31rL+1%Q?3SD1Q=%QA231r@%Q=2T41%R@3T431%Q62OS1&TF+R0%Q72QF1%32S51%Q<251%Q22S9QI%RH3SI1Q6'S?rIrNrM%46CJQ0321%T41SO&R=%12S8R<(6%12T3S?%S33531&Q2r3rQ7%S42TK1%4231&SB&RErQ0%22Q21%T0278%R:2U31%6331SG%R6281p0>1p[FTC1pZNU51rQ8%SB2U91%B2A1%T:23B%RD2U=1%R>21T1%R@241p0H1pZ2TM1p\HU?1(>%11TH%SL11&7rQ;&SOr4%211%53UJ41%TJ1TD%TL216%T62UMTA&NrQ=%T92V01uQ0%4221%T?3V161&T0rQ<&Q3%V91UK&T8&SF%443V821rQ>%TE2V<1%93831r7%U93U321r5r6%U4221%U6215&SGrQ2+TP0rQ1%45321QIC%U?4U>R061rQ5rQ9%QN221r8%RA62QFR4=1@&S6%12Q:3&TB%13V>QJ5%T42T:UL+Q?%T42TC1%S02UO1%T9241%TB2W9UL%T?11rQ@%113%UH3VM31p061pYNVK1%T@2T9V8%S:2V9S8%TC221&RDrQ?%RF2QN1%321V9%U02WGRM%V?11rQB%113%V63W;31p061p0;1pYNW:1%T@4W;W;S5VB&SC%TC3W<21%U22R9VE%SL2VFS9%U5221%W21>rQE%11@%VC3WH31p051p091pYNWG1pZJWH1p[6WI1'SMvUN(QE&SJvU;rQ6%UM2XD1&SL%11W:%655W>3W61%821UM%;4W=:1QNp0=1p0M1p0Q=1p0QJ1p0QM1p0R01p0R61p0RA1p0RN1tR@X3S61t\LY2S91p4X?1p[BXD1pT6XF1pT@XJ1rQ4+_SeL%VD2Y;1rQ3%L5K421G%N21RH%Q14X3Q01W9p081p0SL1p0T01p0T;1p0U21p0U81p0U;1p0UB1p0UJ1p0V21p0V91p0V>1p0VC1p0VO1p0W>1p0WB1p0WH1p0WN1p0X41p0X?1p0XJ1tR>Y5XO1pRJY71p[LYC1p\NY=1pZ4Y>1p\4YF1p[DYG1p\FYH1p2YG1pZ>YE1pS4YG1pRNYJ1p[@YO1pT4Z11pT>Z51p[4Z91p\:Z<1pZDZ?1p\JZE1").
Proof.
intros vals ebs sr kn R M model LB LK cr A u n so bls vbnd ra K E HR HK Hsv Hkv HL1 P0 Hiw
R2 Hso Hsoal Hin R10 R4 R1 Hra Hra2 DI Hbl Hvb HK0 CONT.
set (FF := @nil fframe) in *.
pose proof (di_inv _ _ _ _ _ _ DI) as HH. pose proof (di_halt _ _ _ _ _ _ DI) as Hh. pose proof (di_minv _ _ _ _ _ _ DI) as HMI.
pose proof (dinv_stack_defined _ _ _ _ _ _ DI) as Hdef.
pose proof Hsp as Hsp'. pose proof (dla_scr DL) as (SC1 & SC2 & SC3).
pose proof (aio_free _ _ _ _ _ HIok fx R M model LB FF LK cr A u n K) as MS.
cbv zeta in MS. rewrite (dla_segs DL), (dla_free DL), (dla_tp DL) in MS. rewrite R1 in MS.
apply MS; clear MS; try assumption.
- apply ret_ok_even. rewrite u_small by lia. exact Hra2.
- rewrite R2, u_small by lia.
eapply (astack_ok_of_window vals ebs (ahid A model) M kn so); eauto; lia.
- intros R' M' model' A' HP HPRES HRT HINC HMI' HH'.
rewrite R2, u_small in HPRES by lia. destruct HPRES as (PR1 & PR2).
assert (Hh' : m_halted model' = None) by (rewrite (model_rt_halted _ _ HRT); exact Hh).
assert (HL' : length (vals ++ junk_vals R') = (length vals + 32)%nat) by (rewrite length_app, junk_vals_length; reflexivity).
assert (P0' : vals_ev (vals ++ junk_vals R') 0 = sp0) by (rewrite vals_ev_app_l by lia; exact P0).
assert (CLI : forall a, aclient L ar (lb_remove u LB) FF (bv_unsigned sp0 + so) 4096 a ->
aclient L ar (lb_remove u LB) FF (bv_unsigned sp0 + so) (hl_scr_free L) a)
by (intros a; apply aclient_scr_mono; lia).
apply (CONT R' M' model' A' HL'); try assumption.
+ apply (regs_after_keeps vals ebs sr R R' c_kept Hsv HR (regs_preserved_keptA R R' HP) c_kept_no0A).
+ unfold keep_allocA.
pose proof (env_app_know ASEGS vals (junk_vals R') ebs _ kn Hkv HK) as HK1.
refine (know_keep_sound ASEGS 0 so 4096 bls vbnd [] IMG_CLIENT_A IMG_RW_A
(Env (vals_ev (vals ++ junk_vals R')) ebs)
(CPa (lb_remove u LB) FF (bv_unsigned sp0 + so) 4096 (ahid A model) (ahid A' model')) (SCa (bv_unsigned sp0 + so) 4096)
_ (mrestrict (ahid A model) M) (mrestrict (ahid A' model') M') _ _ kn HK1).
* eapply (regions_callA (vals ++ junk_vals R') ebs so 4096 bls vbnd (lb_remove u LB) LB (lb_remove u LB) FF FF LK LK cr cr A A' M M' model model');
[exact P0' | exact Hso | lia | exact HH | exact HH' | | | | ].
-- intros a Ha. exact (in_block_remove u LB a Ha).
-- intros a Ha; exact Ha.
-- intros i nb Hf. destruct (Hbl i nb Hf) as (Hi32 & H1). rewrite vals_ev_app_l by exact Hi32. exact H1.
-- intros v b Hf. destruct (Hvb v b Hf) as [Hv H1]. rewrite vals_ev_app_l by exact Hv. exact H1.
* intros a Ha (HC & V1 & V2). unfold mrestrict. rewrite V1, V2. apply PR1; [exact Ha | apply CLI; exact HC].
* intros a HS. unfold SCa in HS. unfold mrestrict.
rewrite (vis_of_inv _ _ _ _ _ _ _ a HH') by lia.
destruct (Z_lt_le_dec a (bv_unsigned sp0 + so - hl_scr_free L)) as [Hlo|Hhi].
-- rewrite PR1; [apply (window_defined vals ebs (ahid A model) M kn HK Hiw P0); lia | lia |].
unfold aclient. right. left. rewrite (dla_sptop DL). lia.
-- apply PR2. lia.
+
apply (dinv_call LB (lb_remove u LB) (lb_remove u LB) LK LK cr cr A A' M M' model model' (bv_unsigned sp0 + so) (hl_scr_free L) DI ltac:(lia)); assumption.
+ intros a Ha. apply PR1; [lia|]. unfold aclient. right. left. rewrite (dla_sptop DL). lia.
+ intros a Ha Hb. apply PR1; [exact Ha | left; exact Hb].
+ intros lo hi a Hin' Ha. assert (0 <= a < 2 ^ 64).
{ destruct (img_client_rng lo hi Hin') as (I1 & I2 & I3). lia. }
apply PR1; [assumption|]. unfold aclient. right. right. left. rewrite (dla_img_lo DL), (dla_img_hi DL).
split; [destruct (img_client_rng lo hi Hin') as (I1 & I2 & I3); lia | exact (dla_client DL lo hi a Hin' Ha)].
Qed.
Hypothesis ICok : aicpt_ok L ar IL scfg HI.
Hypothesis ILY : as0_icpt_layout IL.
Section SE.
Variables (Mx : word -> option byte).
Lemma rdn_of_bytes_at : forall n (a : word) bs, length bs = n -> bv_unsigned a + Z.of_nat n <= 2 ^ 64 ->
(forall j, (j < n)%nat -> Mx (Z_to_bv 64 (bv_unsigned a + Z.of_nat j)) = Some (nth j bs (Z_to_bv 8 0))) ->
rdn ASEGS Mx a n = Some bs.
Proof.
intros n.
induction n as [|n IH]; intros a bs Hlen Hnw Hpt.
- destruct bs; [reflexivity | cbn in Hlen; lia].
- destruct bs as [|b bs']; [cbn in Hlen; lia|]. cbn in Hlen. cbn [rdn].
pose proof (Hpt 0%nat ltac:(lia)) as H0. change (Z.of_nat 0) with 0 in H0. rewrite Z.add_0_r, Z_to_bv_bv_unsigned in H0. cbn [nth] in H0.
rewrite H0.
destruct n as [|n']; [destruct bs'; [reflexivity | cbn in Hlen; lia]|].
assert (Hu1 : bv_unsigned (a + 1)%bv = bv_unsigned a + 1) by (apply u_add1; lia).
rewrite (IH (a + 1)%bv bs'); [reflexivity | lia | rewrite Hu1; lia |].
intros j Hj. rewrite Hu1. replace (bv_unsigned a + 1 + Z.of_nat j) with (bv_unsigned a + Z.of_nat (Datatypes.S j)) by lia.
exact (Hpt (Datatypes.S j) ltac:(lia)).
Qed.
End SE.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Section SE.
Local Abbreviation SEC_T_aacc_of_blkA := (ltac2:(TCodec.tc2 tcn__Ja0DrvLib "Q;'V8yR0%211'?y8%511%311p051'Q5&S8r5r4r3%43321'J&TG+8%2271z%53;21&TEr6%2241r7%421>&TD%125@r8%3215%9231&RHr:%2319;p041p0:1p0=1p0A1p0H1p[<N1p[HO1p[DQ01p\FQ11pT4Q31")) (only parsing).
Variable M : ltac:(sec_ty2 constr:(SEC_T_aacc_of_blkA) 0%nat 0%nat).
Variable u : ltac:(sec_ty2 constr:(SEC_T_aacc_of_blkA) 1%nat 0%nat).
Variable n : ltac:(sec_ty2 constr:(SEC_T_aacc_of_blkA) 2%nat 0%nat).
Variable p : ltac:(sec_ty2 constr:(SEC_T_aacc_of_blkA) 3%nat 0%nat).
Variable m : ltac:(sec_ty2 constr:(SEC_T_aacc_of_blkA) 4%nat 0%nat).
Lemma aacc_of_blkA : ltac:(sec_stmt2 constr:(SEC_T_aacc_of_blkA) 5%nat 0%nat).
Proof.
intros [SZ SP] U8 U0 H1 H2 a Ha.
unfold shadow_zero, byte_at in SZ, SP |- *.
assert (E : S a = S u + (a / 8 - u / 8)) by (unfold S; lia).
destruct (Z_lt_le_dec (a / 8 - u / 8) (n / 8)) as [LT|GE].
- left. rewrite E. apply SZ. lia.
- right. exists (n mod 8). assert (NZ : n mod 8 <> 0) by lia. assert (G : a / 8 - u / 8 = n / 8) by lia.
split; [rewrite E, G; apply SP; exact NZ | lia].
Qed.
End SE.
Lemma u16_u8 : ltac2:(TCodec.tc2 tcn__Ja0DrvLib ">'Q5'J&TGr1+@%3221z%63721r2+8%8221%:3;15p051p\F=1").
Proof. intros u H. lia. Qed.
Lemma S_mono : ltac2:(TCodec.tc2 tcn__Ja0DrvLib "='Q5&TEr2r1%3221&RGr3%211%316%8221p061pZ2;1pYN<1").
Proof. intros a b H. unfold S. lia. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Lemma src_blk_aacc : ltac2:(TCodec.tc2 tcn__Ja0DrvLib "QH'<'A'Q5%2211%411&S4%611&RB'V8yR0%211'?y8%511%311p051&S9&S7vQ;r;r:r9r8r7r6r5%9887654321&TA(@r4%24LL51r<%53M21&TE%12:5&TD%12;7%22>=%5221&RH%13D@?p031p081p0;1p0B1p[DQ;1p\<Q<1pZ<Q=1p8Q>1pYLQ11pT4Q31p2Q?1pZ>Q=1pS4Q?1pRBQ@1pRNQC1").
Proof.
intros LB FF LK cr A M V As caps src n HH Hin H1 H2.
destruct (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WF & _).
destruct (WF (As, caps) Hin) as (HBR & _ & HSB & _). cbn [fst snd] in HBR, HSB. destruct HBR as (B1 & _ & B3 & _).
apply (aacc_of_blkA M As caps src n HSB (u16_u8 _ B3)); lia.
Qed.
Lemma src_blk_app_rng : ltac2:(TCodec.tc2 tcn__Ja0DrvLib "QI'<'A'Q5%2211%411&S4%611&RB'V8yR0%211'?y8%511%311p051&S9&S7vQ;r;r:r9r8r7r6r5%9887654321&TA(@r4%24LL51r<%53M21&TE%12:5&TD%12;7%22>=%5221&RNvTO%231A@p041p091p0<1p0C1p[DQ<1p\<Q=1pZ<Q>1p8Q?1pYLQ21pT4Q41p2Q@1pZ>Q>1pS4Q@1pRBQA1pRNQD1").
Proof.
intros LB FF LK cr A M V As caps src n HH Hin H1 H2.
destruct (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WF & _).
destruct (WF (As, caps) Hin) as (HBR & _). cbn [fst snd] in HBR. destruct HBR as (B1 & _ & _ & _ & B5 & (_ & BAM & _)).
unfold app_rng. unfold BIGSHADOW_LO, BIGSHADOW_HI in *. lia.
Qed.
Lemma src_stage_app_rng : ltac2:(TCodec.tc2 tcn__Ja0DrvLib "B'Q5&TE+V[dj@r2%3221&TDr3%2214+V]dj@%8221&RNvTOr4%33217p051p0;1p[D@1p\<A1").
Proof. intros src n H1 H2. pose proof Hsp. unfold app_rng, BIGSHADOW_LO, BIGSHADOW_HI. rewrite (dla_sptop DL). lia. Qed.
Lemma src_stage_aacc : ltac2:(TCodec.tc2 tcn__Ja0DrvLib "Q@'<'A'Q5%2211%411&S4%611&RB'V8yR0%211'?y8%511%311p051&S9&S7vQ;r9r8r7r6r5r4r3%9887654321&TE+V[dj@%2214&TD%1276+V]dj@%6221&RH%13><;p031p081p0<1p[DQ51p\<Q61pYLI1pT4K1p2Q71pZ>Q51pS4Q71pRBQ81pRNQ;1").
Proof.
intros LB FF LK cr A M V src n HH H1 H2 a Ha. left.
destruct (aic_img_shadow _ _ _ _ _ ICok _ _ _ _ _ _ _ HH src n) as (Z0 & _).
- rewrite (dla_img_lo DL). lia.
- rewrite (dla_img_hi DL). lia.
- lia.
- rewrite (aicl_poison IL ILY). repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil.
- apply Z0. unfold in_shadow_of. split; apply S_mono; lia.
Qed.
Lemma aclient_remove : ltac2:(TCodec.tc2 tcn__Ja0DrvLib "K'Q5'<'A%1233%311&S4%511&RJvQ=vTO&REr6r5%3221r4r3r2r1%;7:954321%<7;:87543p021pYNE1p\0F1p\6G1pRBB1pRNE1p\FJ1").
Proof.
intros u LB FF sp scr a Hc. unfold aclient, aclient_g in *.
destruct Hc as [Hc|[Hc|[Hc|[Hc|[Hc|[Hc|Hc]]]]]]; [left; exact (in_block_remove u LB a Hc) | tauto | tauto | tauto | tauto | tauto |].
right. right. right. right. right. right. destruct Hc as (b & Hb & Hr). exists b. split; [exact (in_lb_remove_in u LB b Hb) | exact Hr].
Qed.
Lemma ablock_range_prefix : ltac2:(TCodec.tc2 tcn__Ja0DrvLib "E'Q5&RIvQ=vTOr3r2%544321'I&TFz%2215&TE%1278%6231r5%>4=<1;p031p0;1p[FB1p[DC1p\FD1").
Proof. intros u n nb (B1 & B2 & B3 & B4 & B5 & (B6 & B7 & B8)) Hnb. unfold ablock_range, app_mem. repeat split; lia. Qed.
Lemma kn_blkA_of_inv : ltac2:(TCodec.tc2 tcn__Ja0DrvLib "RG'<'V8yR0%211%411'=y8%611%811p041'A'Q5%2211%=11&S4%?11&RB'?%11;p0@1'QG'T5(T2&T?r<%211r;%5221'S?r:r9r8r7r6%66854321&TA(@r5r4%34LL21%53L1@'I&TFz%2216&TE%1289%6231'Jr@%K21C&V7%12QBD%53QB31rA(5%Q1221vV3%:3QG21&T:&T@&R:&RMr=%221Q6%421Q9&SH%12Q6Q3%948Q331p0;1p0A1p0H1p0Q01p0Q71tR>QEQ?1p[FR01pZ8R11p\FR21p\HR91p[@QK1pT4QM1p2R41pZ>R21pS4R41pRNR71pZDR<1p\JRB1").
Proof.
intros vals ebs LB LK cr A M model v u cap nb E D Hin Hnb Pv P0.
pose proof (di_inv _ _ _ _ _ _ D) as HH.
destruct (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WF & _).
destruct (WF (u, cap) Hin) as (HBR & HDEF & _). cbn [fst snd] in HBR, HDEF.
eapply kn_blkA_ok; [exact Pv | exact P0 | exact (ablock_range_prefix _ _ _ HBR Hnb) |].
intros i Hi. unfold mrestrict.
rewrite (vis_of_inv _ _ _ _ _ _ _ (u + i) HH); [apply HDEF; lia | destruct HBR as (B1 & _ & _ & _ & B5 & _); rewrite (dla_sptop DL) in B5; pose proof Hsp; lia |].
right. right. exists (u, cap). split; [exact Hin | cbn [fst snd]; lia].
Qed.
Lemma amemcpy_site : ltac2:(TCodec.tc2 tcn__Ja0DrvLib "]4'<'V8yR0%211%411'=y8%611%811p041'T6%;11'T7%=11&R0y5%221='?%11;p0@1'QG'A'Q5%2211%H11&S4%J11&RB%72G6%M11'QI%O11!p]021'T5(T2&T?rF%211rE%5221&T<r1rC%33251&T:&T@r2&R:&RMr>rB%3221%521:%94871?'J'8&T>&;rI%22QI1rG%5221(B%93821&T=rJ%92R01%3217%>3=16'Q1u1rK%?2R61%4231rL(5%Q9221vV3%H3R<21&S@%11?%K3J1C&SI(V6+2(G%33R821%52F1&V7&TD&V9%12RJ>r=%4221%62RM1%Q93RM81'I&TE&TI&TJ+F%22A1%411%621QFz%82QH1%:231&TGr?+@%3221%QI3RJ17rM+:%O3S41M%Q1231rD%M2SD1%R03SD31rN+;%Q63S;1Q4%Q8231%R53SI16rO+<%Q;3S@1Q9%Q=231%R:3SN1;&TF%12JRL+K%Q12Q@1%Q42RO1%Q6241rQ1+4%QF3SK1QD%QH231+V]k\0%QD2T;1%RG3T;31rQ2+1%QM3T21QK%QO231%QJ2TAS0%RM3TA21%QC2Q<S:+R0%QC2R21%F2S=1%QH241%Q>2Q5R5%S43T51QB'S?rQ0rQ4rQ3%46AH3Q321&TA(@%14T=T=Q6Q;%33T=15%R328Q=%R<2Q9QE%R=2O:%R6221&RHrQ8%231Q>QC%R:2R3?+Q?%R:2RI1%R=281&RNvTO%231Q3Q:%RA2R:T9%QB2T:E%RD221'M+RPP0rQ5%RO21T:%RH231+VbTP0%QJ231%RL231&RDrQ<%2217%;241p0=1pZNU=1%UC1UL&SKrQ=%S>2V5Q9&TL%11Q:%54TL431(6%12V4QM%TF3931rQ6%SE21QA%S>21H%SG2IQC%S@214%M231%V31UN&R=%12U7QH%<2V1U=%U13421&Q2r3rQG%U22VI1%4231&SB&RErQ@%22Q21%UN278%T82W11%6331UE%T4281p0>1p[FVA1pZNW31rQH%U@2W71%B2A1%V823B%TB2W;1%T<21UO%T>241p0H1pZ2VK1p\HW=1(>%11VF%S=11&7rQJ&SO%11O%43WG31%VG1VA%VI215%V32WJV>&NrQL%V62WM1uQ0%4221%V<3WN61&T0rQK&Q3%X61WH&T8&SF%443X521rQM%VB2X91%93831r6%W63W021rQDr5%W1221%W3215&SG+TP0rQ;%35RA2RH1B%W;4W:QN51rQFrQEr7%T06QCR1321>&S6%12Q73r9%V72XN@rQB%RJ11%RN4WE431rQA%RJ2XM1%W?3S231%U52WMT@%V72SE1%S;2NWJ&L%V92R2RA%VB2R3C%U;2RC1%V=231%511r4%VH2Y?1%X011rR1%113%WN3Y331p071p0>1p0@1pYNY31%TH4Y4Y4S0X;&SC%TK3Y521%VK2=X>%UL2X?S4%VN221r@%W82YOS7%211rR3%113%X>3YC31p071p0;1pYNYB1pZJYC1p[6YD1'SMvUN(QE&SJvU;%WG2Z>S@r<&SL%11Y5%655WG431r;%9221rQ?%=4Y:<21p0?1p0Q11p0QE1p0QN1p0R11p0R61p0R@1p0RM1tR@YOS51t\LZNS81p[BZ?1pT6ZA1pT@ZE1+^liH%X>2[51rQC%K5JRI21F%M21R9%Q04YMO1V<p071p0SH1p0SL1p0T71p0TM1p0U41p0U?1p0V11p0V51p0V91p0V;1p0V?1p0VC1p0VE1p0VJ1p0W01p0W31p0W91p0W@1p0WH1p0WO1p0X51p0X;1p0XC1p0XI1p0Y51p0YD1p0YH1p0YN1p0Z41p0Z:1p0ZE1p0[01tR>[;[51pRJ[=1p[L[I1p\N[C1pZ4[D1p\4[L1pZ6\;1p[D[N1p\<[O1pZB\01pZ:\11p6\21p2\11pZ>[O1pS4\11pRN\41p[@\91pT4\;1pT>\?1p[4\C1p\:\F1pZD\I1p\J\O1").
Proof.
intros vals ebs sr kn R M model LB LK cr A Ad capd dst src n bs so bls vbnd ra K E HR HK Hsv Hkv HL1 P0 Hiw
R2 Hso Hsoal R10 R11 R12 Hn R4 R1 Hra Hra2 DI Hin Hd1 Hd2 Hacc Hs0 Hs1 Happ Hsrc Hrd Hdj Hbl Hvb HK0 CONT.
set (FF := @nil fframe) in *.
pose proof (di_inv _ _ _ _ _ _ DI) as HH. pose proof (di_halt _ _ _ _ _ _ DI) as Hh. pose proof (di_minv _ _ _ _ _ _ DI) as HMI.
pose proof (dinv_stack_defined _ _ _ _ _ _ DI) as Hdef.
pose proof Hsp as Hsp'. pose proof (dla_scr DL) as (SC1 & SC2 & SC3).
destruct (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WF & _).
destruct (WF (Ad, capd) Hin) as (HBR & HDEF & HSB & _ & HAP & _). cbn [fst snd] in HBR, HDEF, HSB, HAP.
pose proof (hzA_of_block_range _ _ HBR) as (Y1 & Y2 & Y3). pose proof HBR as (_ & _ & B3 & _ & _ & (_ & BAM & _)).
assert (INB : forall i, 0 <= i < n -> in_block LB (dst + i)).
{ intros i Hi. exists (Ad, capd). split; [exact Hin | cbn [fst snd]; lia]. }
pose proof (aic_memcpy_libc _ _ _ _ _ ICok fx R M model LB FF LK cr A dst src n bs K) as MS.
unfold amemcpy_libc_spec, amemcpy_spec_at in MS. rewrite (dla_segs DL), (dla_memcpy DL) in MS.
apply MS; clear MS; try assumption.
- unfold amem_pre. rewrite (dla_tp DL), (dla_segs DL), R1, R2, u_small by lia.
split; [exact HH|]. split; [exact Hh|]. split; [exact HMI|]. split; [exact R10|]. split; [exact R12|]. split; [lia|].
split; [exact R4|]. split; [apply ret_ok_even; rewrite u_small by lia; exact Hra2|].
split; [eapply (astack_ok_of_window vals ebs (ahid A model) M kn so); eauto; lia|].
split; [apply (aacc_of_blkA M Ad capd dst n HSB (u16_u8 _ B3)); lia|].
split; [intros i Hi; left; exact (INB i Hi)|].
split; [|split; [exact HK0 | unfold app_rng; rewrite (dla_sptop DL); lia]].
intros i m Hi Hm. destruct m as [|m']; [reflexivity|]. set (m := Datatypes.S m') in *.
apply store_ok_of_all; [rewrite u_small by lia; lia|].
intros x Hx. rewrite u_small in Hx by lia.
specialize (HDEF (bv_unsigned x - Ad) ltac:(lia)). replace (Ad + (bv_unsigned x - Ad)) with (bv_unsigned x) in HDEF by lia.
rewrite Z_to_bv_bv_unsigned in HDEF. unfold wview. destruct (M x); [discriminate | exfalso; apply HDEF; reflexivity].
- split; assumption.
- intros i Hi. destruct (Hsrc i Hi) as [X|X]; [left; rewrite (dla_img_lo DL), (dla_img_hi DL); exact X | right; left; exact X].
- intros _. exact Hdj.
- unfold amem_post. cbv zeta. intros R' M' model' HA HP HNEW HPRES HSCR HRT HMI' HH'.
rewrite (dla_segs DL), R1. rewrite R2, u_small in HPRES, HSCR by lia.
assert (Hh' : m_halted model' = None) by (rewrite (model_rt_halted _ _ HRT); exact Hh).
assert (HL' : length (vals ++ junk_vals R') = (length vals + 32)%nat) by (rewrite length_app, junk_vals_length; reflexivity).
assert (P0' : vals_ev (vals ++ junk_vals R') 0 = sp0) by (rewrite vals_ev_app_l by lia; exact P0).
assert (NDST : forall a, aclient L ar (lb_remove Ad LB) FF (bv_unsigned sp0 + so) 4096 a -> ~ (dst <= a < dst + n)).
{ intros a Hc Hr. unfold aclient, aclient_g in Hc. rewrite (dla_img_lo DL), (dla_img_hi DL), (dla_sptop DL) in Hc.
destruct Hc as [Hc|[Hc|[Hc|[Hc|[Hc|[Hc|Hc]]]]]].
- destruct Hc as (b & Hb & Hbr). destruct (HAP b Hb) as [Q|Q]; lia.
- lia.
- lia.
- destruct Hc as (f & [] & _).
- unfold in_shadow_of, S, SB in Hc. unfold BIGSHADOW_LO, BIGSHADOW_HI in BAM.
assert (D0 : 0 <= (bv_unsigned sp0 - 8388608) / 8) by (apply Z.div_pos; lia).
replace (bv_unsigned sp0 - 8388608 + (2 ^ 47 - (bv_unsigned sp0 - 8388608)) - 1) with (2 ^ 47 - 1) in Hc by ring.
change ((2 ^ 47 - 1) / 8) with 0xfffffffffff in Hc. lia.
- destruct Hc as (f & [] & _).
- destruct Hc as (b & Hb & Hbr). pose proof (in_lb_remove_in _ _ _ Hb) as Hb'.
destruct (WF b Hb') as ((C1 & _ & _ & C4 & C5 & (_ & _ & C8)) & _).
unfold in_shadow_of, S, SB in Hbr. unfold BIGSHADOW_LO, BIGSHADOW_HI in BAM.
assert (D0 : 0 <= fst b / 8) by (apply Z.div_pos; lia).
assert (D2 : (fst b + snd b - 1) / 8 <= (2 ^ 47 - 1) / 8) by (apply Z.div_le_mono; lia).
change ((2 ^ 47 - 1) / 8) with 0xfffffffffff in D2. lia. }
assert (PR1 : forall a, 0 <= a < 2 ^ 64 -> aclient L ar (lb_remove Ad LB) FF (bv_unsigned sp0 + so) 4096 a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
{ intros a Ha Hc. apply HPRES; [exact Ha | | exact (NDST a Hc)].
apply (aclient_scr_mono _ _ _ 4096 (hl_scr_mem L)); [lia|]. exact (aclient_remove Ad LB FF _ _ a Hc). }
apply (CONT R' M' model' HL'); try assumption.
+ apply (regs_after_keeps vals ebs sr R R' c_kept Hsv HR (regs_preserved_keptA R R' HP) c_kept_no0A).
+ unfold keep_allocA.
pose proof (env_app_know ASEGS vals (junk_vals R') ebs _ kn Hkv HK) as HK1.
refine (know_keep_sound ASEGS 0 so 4096 bls vbnd [] IMG_CLIENT_A IMG_RW_A
(Env (vals_ev (vals ++ junk_vals R')) ebs)
(CPa (lb_remove Ad LB) FF (bv_unsigned sp0 + so) 4096 (ahid A model) (ahid A model')) (SCa (bv_unsigned sp0 + so) 4096)
_ (mrestrict (ahid A model) M) (mrestrict (ahid A model') M') _ _ kn HK1).
* eapply (regions_callA (vals ++ junk_vals R') ebs so 4096 bls vbnd (lb_remove Ad LB) LB LB FF FF LK LK cr cr A A M M' model model');
[exact P0' | exact Hso | lia | exact HH | exact HH' | | | | ].
-- intros a Ha. exact (in_block_remove Ad LB a Ha).
-- intros a Ha. exact (in_block_remove Ad LB a Ha).
-- intros i nb Hf. destruct (Hbl i nb Hf) as (Hi32 & H1). rewrite vals_ev_app_l by exact Hi32. exact H1.
-- intros v b Hf. destruct (Hvb v b Hf) as [Hv H1]. rewrite vals_ev_app_l by exact Hv. exact H1.
* intros a Ha (HC & V1 & V2). unfold mrestrict. rewrite V1, V2. apply PR1; assumption.
* intros a HS. unfold SCa in HS. unfold mrestrict.
rewrite (vis_of_inv _ _ _ _ _ _ _ a HH') by lia.
destruct (Z_lt_le_dec a (bv_unsigned sp0 + so - hl_scr_mem L)) as [Hlo|Hhi].
-- rewrite HPRES; [apply (window_defined vals ebs (ahid A model) M kn HK Hiw P0); lia | lia | | lia].
unfold aclient. right. left. rewrite (dla_sptop DL). lia.
-- apply HSCR. lia.
+
apply (dinv_call LB (lb_remove Ad LB) LB LK LK cr cr A A M M' model model' (bv_unsigned sp0 + so) 4096 DI ltac:(lia)); assumption.
+
pose proof (rdn_length _ _ _ _ _ Hrd) as Hlen.
apply rdn_of_bytes_at; [exact Hlen | rewrite u_small by lia; lia |].
intros j Hj. rewrite u_small by lia.
destruct (HNEW (Z.of_nat j) ltac:(lia)) as (v & (Hnth & Hv) & Hb). rewrite Nat2Z.id in Hnth.
unfold byte_at in Hb. rewrite Hb. f_equal. symmetry. apply nth_error_nth. exact Hnth.
+ intros a Ha Hb Hnd. apply HPRES; [exact Ha | left; exact Hb | exact Hnd].
+ intros lo hi a Hin' Ha. assert (0 <= a < 2 ^ 64).
{ destruct (img_client_rng lo hi Hin') as (I1 & I2 & I3). lia. }
apply PR1; [assumption|]. unfold aclient. right. right. left. rewrite (dla_img_lo DL), (dla_img_hi DL).
split; [destruct (img_client_rng lo hi Hin') as (I1 & I2 & I3); lia | exact (dla_client DL lo hi a Hin' Ha)].
Qed.
End DrvLayoutA.
End FPX_1.

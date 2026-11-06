(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import
PropExec CatExec CatSim SeqExec StoreOk StreamSim ShapeAlg ShapeLaws SpinAlg Hoare AgentLib Spec AsanAcctShape SymExec2 SymExec2Sound SymRun SymDrive SymDriveX
HeapIface HeapIfaceA IcptIfaceA DrvKitA DrvNodesLazyK As0DrvKitA Ja0DrvEntry Ja0Drv_defs Ja0DrvLib Ja0DrvRead Ja0DrvPiece Ja0DiagLoopK Ja0DrvStdio Ja0DrvPrintfK Ja0DrvPrintf1 Ja0DrvExit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require L5Defs L5KnA Ja0DiagKit Ja0DiagGlue.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Ja0DiagChainK () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.Fs."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.LinuxProcessSem.Run."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanAcct."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0DiagChainK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0DiagChainK.FPX_1.Chain."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0DiagGlue.DG."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0DiagLoopK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0DrvExit."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0DrvLib."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Spec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A"; "1None"; "1Some"; "1bool"; "1cons"; "1list"; "1nat"; "1nil"; "1option"; "1prod"; "1true"; "2and"; "2eq"; "2not"; "3Z"; "0HI"]; ["0LB"; "0LK"; "4Fs"; "5store_ok"; "6mkCfg"; "7FdChannel"; "7FdEntry"; "7Model"; "7event"; "7fd_lookup"; "7m_fds"; "7m_fs"; "8bvmap"; "0M"; "0M0"; "0MVi"]; ["0Ma"; "0Mb"; "0Mi"; "0R"; "0R'"; "9mrestrict"; ":credit"; ";ahid"; ";fframe"; "=dgW"; "<dg_chain"; "<dg_shape"; ">agree0"; "?WV_KEEP"; "@exitA"; "@stdoutPA"]; ["ACWA"; "Adinv"; "BFPState"; "Bgetr"; "Bmkst"; "Bseg_rom"; "CTSet"; "Ct_emit"; "Ct_eq"; "Ct_exit"; "DW"; "Dexit_code"; "Esrealizes"; "Fmem_grows"; "Gloaded_segments"; "0S"]; ["0Sf"; "HIn"; "Hconcat"; "Iadd"; "Ile"; "Ilt"; "Imodulo"; "Iof_nat"; "Ipow"; "Isub"; "0T"; "0T'"; "0a"; "0ar"; "0cr"; "0d"]; ["0evs"; "0fs"; "0fx"; "0i"; "0k"; "0model"; "0n"; "0parts"; "0pc"; "0r"; "0scfg"; "0sp0"; "JZ_to_bv"; "Jbv"; "Jbv_unsigned"; "0tid"]]).
Local Ltac lia := L5FastLiaT.plia2.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Notation u64A := (L5Defs.L5.u64_at ASEGS).
#[local] Notation u32A := (L5Defs.L5.u32_at ASEGS).
#[local] Notation filew := Ja0DiagGlue.DG.filew.
#[local] Notation agree0 := Ja0DiagGlue.DG.agree0.
#[local] Notation rom := (seg_rom ASEGS).
Record dg_wvA (usp S : Z) (RE : bvmap 5 word) (ME : word -> option byte) (wlo q c b1 l1 b2 l2 : Z) (bs1 bs2 : list byte) : Prop := DG_WVA {
dw_regs : getr RE 17%bv = Z_to_bv 64 66 /\ getr RE 10%bv = Z_to_bv 64 2 /\ getr RE 11%bv = Z_to_bv 64 q /\ getr RE 12%bv = Z_to_bv 64 c
/\ getr RE 9%bv = Z_to_bv 64 1273408 /\ getr RE 18%bv = Z_to_bv 64 c /\ getr RE 22%bv = Z_to_bv 64 (l1 + l2) /\ getr RE 19%bv = Z_to_bv 64 q;
dw_win : S - 5440 <= wlo /\ wlo + 32 + 16 <= S /\ wlo <= q /\ q + 16 * c <= wlo + 32 /\ (c = 1 \/ c = 2);
dw_iov0 : u64A ME q b1 /\ u64A ME (q + 8) l1;
dw_b1 : 0 <= b1 /\ 0 <= l1 /\ b1 + l1 <= 2 ^ 47 /\ (l1 = 0 \/ b1 + l1 <= wlo \/ wlo + 32 <= b1) /\ (l1 = 0 \/ b1 + l1 <= 0x691000 \/ usp - 8388608 <= b1)
/\ rdn ASEGS ME (Z_to_bv 64 b1) (Z.to_nat l1) = Some bs1;
dw_c1 : c = 1 -> l2 = 0 /\ bs2 = [];
dw_c2 : c = 2 -> u64A ME (q + 16) b2 /\ u64A ME (q + 24) l2 /\ 1 <= l1 + l2
/\ 0 <= b2 /\ 0 <= l2 /\ b2 + l2 <= 2 ^ 47 /\ (l2 = 0 \/ b2 + l2 <= wlo \/ wlo + 32 <= b2) /\ (l2 = 0 \/ b2 + l2 <= 0x691000 \/ usp - 8388608 <= b2)
/\ rdn ASEGS ME (Z_to_bv 64 b2) (Z.to_nat l2) = Some bs2;
dw_tot : l1 + l2 <= 2 ^ 30;
dw_fd : u32A ME 1273528 2
}.
Definition dg_finA (M0 : word -> option byte) (S Sf : Z) (RF : bvmap 5 word) (MF : word -> option byte) : Prop :=
getr RF 10%bv = Z_to_bv 64 2 /\ getr RF 2%bv = Z_to_bv 64 Sf /\ getr RF 4%bv = Z_to_bv 64 6745472
/\ agree0 M0 MF S
/\ u64A MF 1273448 0 /\ u64A MF 1273464 0 /\ u64A MF 1273416 0 /\ u64A MF 1273424 0.
Fixpoint dg_chain (usp : Z) (M0 : word -> option byte) (S Sf : Z) (parts : list (list byte)) (fx : PropExec.FPState) (R : bvmap 5 word) (pc : Z) (M : word -> option byte) : Prop :=
match parts with
| [] => exists fxF RF MF, msteps ASEGS (@mkst fx R (Z_to_bv 64 pc) M rom) (@mkst fxF RF (Z_to_bv 64 0x113924) MF rom) /\ dg_finA M0 S Sf RF MF
| bs :: rest =>
exists fxE RE ME wlo q c b1 l1 b2 l2 bs1 bs2,
msteps ASEGS (@mkst fx R (Z_to_bv 64 pc) M rom) (@mkst fxE RE (Z_to_bv 64 0x11b304) ME rom)
/\ dg_wvA usp S RE ME wlo q c b1 l1 b2 l2 bs1 bs2 /\ bs = bs1 ++ bs2
/\ agree0 M0 ME S
/\ forall RX MX,
(forall x : word, ~ (wlo <= bv_unsigned x < wlo + 32) -> MX x = ME x) -> mem_grows ME MX ->
(forall k, In k [2; 3; 4; 8; 9; 21; 23; 24; 25; 26; 27]%nat -> getr RX (Z_to_bv 5 (Z.of_nat k)) = getr RE (Z_to_bv 5 (Z.of_nat k))) ->
dg_chain usp M0 S Sf rest fxE RX 0x11b310 MX
end.
Definition dg_shape (parts : list (list byte)) (fs : Fs.Fs) : TSet := fold_right (fun bs K => t_emit (W 2 bs) K) (t_exit (exit_code 2) fs) parts.
Lemma dg_shape_nil : ltac2:(TCodec.tc2 tcn__Ja0DiagChainK "@'5'RMy8%211%411%511&B&Q;r2r1(7'H%211%63541pU481pU@:1").
Proof. intros [|bs rest] fs; cbn [dg_shape fold_right]; [apply t_exit_has_nil | apply t_emit_has_nil]. Qed.
Lemma t_emit_congrA : ltac2:(TCodec.tc2 tcn__Ja0DiagChainK "B'5'H%211&QF&QHr2r1%3221&QGr4r3%3221%4237%9221p071pTH<1pTF=1pU2?1").
Proof. intros evs T T' H tr. unfold t_emit. split; (intros [X|(tr' & E & Y)]; [left; exact X | right; exists tr'; split; [exact E | apply H; exact Y]]). Qed.
Lemma dg_shape_eq : ltac2:(TCodec.tc2 tcn__Ja0DiagChainK "J'5'RMy8%211%411%511&B&QH&Q;r2r1%3221&QG&QJ+2&R2%12=7%4231&QI&QK%116%321;%:251%@2<1pU4B1pU@D1").
Proof.
induction parts as [|bs rest IH]; intros fs; cbn [dg_shape fold_right concat].
- apply t_eq_sym. apply t_emit_W_nil. apply t_exit_has_nil.
- fold (dg_shape rest fs). eapply t_eq_trans; [|apply t_emit_W_app]. apply t_emit_congrA. apply IH.
Qed.
Section FPX_1.
Variable scfg : SpuriousCfg.
Section Chain.
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
Hypothesis Hex : incl EX_CELLS (asc_cells C).
Variable M0 : word -> option byte.
#[local] Notation dinvA := (dinv ar HI sp0 M0).
#[local] Notation usp := (bv_unsigned sp0).
Definition dgW (S a : Z) : Prop := S - 5440 <= a < S \/ filew a.
#[using="Hsp M0"] Lemma dgW_cwa : ltac2:(TCodec.tc2 tcn__Ja0DiagChainK "M'5'9'>%2211%411';&R4&R9&RNyR0vRK%3221+TP0%6221r2%9221%:225%<221&Q9r3%2216&Q@r5%23=14p041p081pTJH1pT0I1pQ2H1").
Proof.
intros LB S a HS [Ha|Ha]; unfold CWA; [right; left; pose proof Hsp; lia|]. right; right.
exists 0x136e40, 0x137140. split; [unfold IMG_W_A; cbn [In]; tauto | unfold Ja0DiagGlue.DG.filew in Ha; lia].
Qed.
#[using="sp0 M0"] Lemma agree0_Z : ltac2:(TCodec.tc2 tcn__Ja0DiagChainK "Q='RMyR0%211'8y8%511%311p051'>&Q<r3r2r1%43321';&R4z%2215&R5&R8+2+R0%3221%52;1%:271&=&Q9r4%221A%411'<r6&RL%12Q0G%311r7%113%73O31p091p0?1pTJQ01p0L1pT0Q21pR4Q41pR2Q51").
Proof. intros Ma Mb S AG a Ha Hn. apply AG; rewrite u64_lit by lia; intros X; apply Hn; [left | right]; exact X. Qed.
#[using="sp0 M0"] Lemma agree0_trans2 : ltac2:(TCodec.tc2 tcn__Ja0DiagChainK "QA'RMyR0%211'8y8%511%311p051'>&Q<r4r3r1%43321r5r2%73251';&R4z%2218&R5&R8+2+R0%3221%52>1%:271&=&Q9%12@?%311'<r7&RL%12Q2H%311r8%113%73Q131p091p0>1pTJQ21p0K1p0O1pT0Q51pR4Q71pR2Q81pR6Q91").
Proof. intros Mi Ma Mb S A1 A2 a Ha Hn. rewrite (agree0_Z Mi Mb S A2 a Ha Hn), (agree0_Z Mi Ma S A1 a Ha Hn). reflexivity. Qed.
Section SE.
Variables (R R' : bvmap 5 word).
Lemma keep_nat : (forall r, In r WV_KEEP -> getr R' r = getr R r) ->
forall k, In k [2; 3; 4; 8; 9; 21; 23; 24; 25; 26; 27]%nat -> getr R' (Z_to_bv 5 (Z.of_nat k)) = getr R (Z_to_bv 5 (Z.of_nat k)).
Proof using Type R R'.
intros KR k Hk.
apply KR. unfold WV_KEEP. cbn [In] in Hk |- *.
repeat (destruct Hk as [<-|Hk]; [repeat first [left; apply bv_eq; reflexivity | right]|]). destruct Hk.
Qed.
End SE.
#[using="L C IL HIok ICok ILY Hsp Hal DL Hex"] Theorem dg_chain_run : ltac2:(TCodec.tc2 tcn__Ja0DiagChainK "UL'5'RMy8%211%411%511'9'>%2211%911&Q8%;11&Q6yR0%=11'8%11=p031&B'QB&Ly5%2218'G'QAvR=v?vRKvNr>r=r<r;r2r1%;::987654321'<&K%115r7%43F21&Q<&Q5&Q7r3%22?1r4%5221%73A1@&QM%72E4r5%:221%42G1';&R4&R9&RN%12Q=O+TP0%4221%621O%72Q04%9221%92Q3Q2%;213&R6+@%22Q71z%Q23QO21+XPPP0%@2>1%B21Q8&R3%12OQ:%E21B'6%G29Q=&R7%11Q?%72Q51r6%L221'3&C&QNrI&RLr8%@21Q<%32R>1%74651Q@(:%QJ3:21p0<1p0B1pU:D1pU0RK1p0G1p0K1pU>RN1pTJRO1+RPP0%QA21R6&R5+QV`P0%22R91%QF241rD%F2S1R=%211(1%11S>%R>3S231p071pU8S=1&Q>r@rC%3221&Q?%11='F%S=11&I&J%11S0+2%Q92SD1%5231(2(E%114%32;1%S33;51&Q:rFrErKrAr?rG%S421SA%S621SC%99RG87Q465K41'QLvRJ(D&QDrB%QO2T:Q1&QE%11R3%554>3=1%721SN&Q;rL%221Q7%=4R9<41p0?1p0J1p0Q81p0Q;1p0Q@1p0QO1p0S01p0S61p0S91p0SD1p0SJ1p0T31p0T91pU<TF1pQLTM1pUBU81pR8TJ1pU6TN1pU4U01pV0U<1pT2U=1pT0U>1pR0U51p2U>1pTNU<1pQ4U>1pQ2UA1pU@UF1").
Proof.
induction parts as [|bs rest IH]; intros LB LK cr A MVi S Sf tid fs fx R pc M model D EFS AGI MGI HS HSf HSf16 WINi IMGi XAi SOPi FD2 CH; pose proof Hsp as Hsp'.
-
cbn [dg_chain] in CH. destruct CH as (fxF & RF & MF & MS & (F10 & F2 & F4 & AGF & C1 & C2 & C3 & C4)).
pose proof (ArtBridge.msteps_mem_grows ASEGS _ _ MS) as MGF. cbn [ms_mem] in MGF.
apply (drv_piece scfg L ar C IL HI HIok sp0 Hsp DL M0 LB LK cr A M model fx fxF R (Z_to_bv 64 pc) RF (Z_to_bv 64 0x113924) MF (dgW S) _ D MS MGF
(agree0_trans2 MVi _ MF S AGI AGF) (fun a Ha => dgW_cwa LB S a HS Ha)).
intros M1 model1 D1 SBM1 VIS1 FRM1.
assert (FRi : forall a, 0 <= a < 2 ^ 64 -> ~ dgW S a -> MF (Z_to_bv 64 a) = MVi (Z_to_bv 64 a)) by (exact (agree0_Z MVi MF S AGF)).
assert (MGiF : mem_grows MVi MF) by (eapply mem_grows_trans; [exact MGI | exact MGF]).
assert (TR : forall a (n : nat) bs0, rdn ASEGS MVi (Z_to_bv 64 a) n = Some bs0 ->
(0 <=? a) && (a + Z.of_nat n <=? 2 ^ 63) && ((a + Z.of_nat n <=? 1273408) || (1273548 <=? a)) && ((a + Z.of_nat n <=? 0x7fff00000000)) = true ->
rdn ASEGS MF (Z_to_bv 64 a) n = Some bs0).
{ intros a n bs0 Hr Hb. apply andb_prop in Hb as (Hb & B4). apply andb_prop in Hb as (Hb & B3). apply andb_prop in Hb as (B1 & B2).
apply Z.leb_le in B1, B2, B4. apply (TRf MVi MF (dgW S) FRi a n bs0 Hr); [lia | lia|].
intros i Hi [X|X]; [lia|]. unfold Ja0DiagGlue.DG.filew in X. apply orb_prop in B3 as [B3|B3]; apply Z.leb_le in B3; lia. }
destruct XAi as (XC & TIDC & HTr & DESC). destruct SOPi as (P1 & P2 & P3 & P4 & P5).
assert (XP : exit_pre ar HI sp0 M0 LB LK cr A M1 model1 Sf tid).
{ unfold exit_pre. rewrite VIS1. split; [exact D1|]. split; [lia|]. split; [lia|]. split; [exact HSf16|].
split; [intros a n Ha Hn d k Hd Hk; apply (store_ok_mono ASEGS k MVi MF _ MGiF); apply (WINi a n); assumption|].
split; [intros i Hi; rewrite FRi; [apply IMGi; exact Hi | lia | intros [X|X]; [lia | unfold Ja0DiagGlue.DG.filew in X; lia]]|].
unfold exitA. split; [|split; [exact (TR _ _ _ TIDC eq_refl) | split; [exact HTr|]]].
- unfold cells_at in *. rewrite Forall_forall in *. intros c Hin. pose proof (XC c Hin) as Hc.
unfold XC_CELLS in Hin. cbn [In] in Hin.
repeat (destruct Hin as [<-|Hin]; [cbn [fst snd] in Hc |- *; first [exact C1 | exact C2 | exact C3 | exact C4 | exact (TR _ _ _ Hc eq_refl)]|]). destruct Hin.
- intros i Hi. rewrite FRi; [apply DESC; exact Hi | lia | intros [X|X]; [lia | unfold Ja0DiagGlue.DG.filew in X; lia]]. }
rewrite <- EFS. rewrite <- (proj2 (sbm_fds model model1 SBM1)). cbn [dg_shape fold_right]. unfold exit_code.
apply (exit_run_e scfg L ar C IL HI HIok ICok ILY sp0 Hsp DL Hex M0 LB LK cr A M1 model1 RF Sf 2 tid XP ltac:(lia) F2 F4 F10).
rewrite VIS1. unfold stdoutPA. repeat split; first [exact (TR _ _ _ P1 eq_refl) | exact (TR _ _ _ P2 eq_refl) | exact (TR _ _ _ P3 eq_refl) | exact (TR _ _ _ P4 eq_refl) | exact (TR _ _ _ P5 eq_refl)].
-
cbn [dg_chain] in CH. destruct CH as (fxE & RE & ME & wlo & q & c & b1 & l1 & b2 & l2 & bs1 & bs2 & MS & WV & Ebs & AGE & KONT).
destruct WV as [(G17 & G10 & G11 & G12 & G9 & G18 & G22 & G19) (W1 & W2 & W3 & W4 & Wc) (I0 & I1) (B1a & B1b & B1c & B1d & B1e & B1r) HC1 HC2 HTOT HFD].
pose proof (ArtBridge.msteps_mem_grows ASEGS _ _ MS) as MGE. cbn [ms_mem] in MGE.
apply (drv_piece scfg L ar C IL HI HIok sp0 Hsp DL M0 LB LK cr A M model fx fxE R (Z_to_bv 64 pc) RE (Z_to_bv 64 0x11b304) ME (dgW S) _ D MS MGE
(agree0_trans2 MVi _ ME S AGI AGE) (fun a Ha => dgW_cwa LB S a HS Ha)).
intros M1 model1 D1 SBM1 VIS1 FRM1.
assert (MGiE : mem_grows MVi ME) by (eapply mem_grows_trans; [exact MGI | exact MGE]).
pose proof (dinv_lzinv scfg L ar C IL HI HIok sp0 DL M0 _ _ _ _ _ _ D1) as (HH1 & HL1 & HA1 & HM1 & Hh1).
assert (Hq : 0 <= wlo /\ wlo <= wlo + 32 /\ wlo + 32 + 16 <= 2 ^ 47) by lia.
assert (Hf : 0 <= 1273408 /\ (1273408 + 124 <= wlo \/ wlo + 32 + 16 <= 1273408 + 120) /\ 1273408 + 124 < 2 ^ 63) by lia.
assert (NLq : forall x, wlo <= x < wlo + 32 -> page_in_ranges (page_base_of x) (m_vm_lazy model1) = false).
{ intros x Hx. apply (nl_pt scfg L ar C IL HI HIok sp0 Hsp DL M0 _ _ _ _ _ _ x D1); lia. }
assert (FD1 : fd_lookup (m_fds model1) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2))) by (rewrite (sbm_fds' _ _ SBM1); exact FD2).
rewrite Ebs. cbn [dg_shape fold_right]. fold (dg_shape rest fs). unfold W at 1.
apply (@wv_loop fxE scfg (ahid A model1) A HH1 (m_vm_lazy model1) HL1 HA1 1273408 2 ltac:(lia) wlo (wlo + 32) Hq Hf NLq (dg_shape rest fs) (dg_shape_nil rest fs)
(length (bs1 ++ bs2)) true RE M1 model1 q c b1 l1 b2 l2 bs1 bs2).
+ lia.
+ reflexivity.
+ exact HM1.
+ exact Hh1.
+ exact FD1.
+ unfold wv_regs. repeat split; assumption.
+ rewrite VIS1. unfold wv_iov. split; [exact W3|]. split; [exact W4|]. split; [exact Wc|]. split; [exact I0|]. split; [exact I1|].
split. { replace (Z_to_bv 64 q) with (Z_to_bv 64 (q + 0)) by (f_equal; lia). apply (store_ok_mono ASEGS _ MVi ME _ MGiE). apply (WINi q (16 * c)); lia. }
split. { unfold wv_buf. split; [exact B1a|]. split; [exact B1b|]. split; [exact B1c|]. split; [exact B1d|]. split; [exact B1r|].
intros x Hx. apply (nl_pt scfg L ar C IL HI HIok sp0 Hsp DL M0 _ _ _ _ _ _ x D1); lia. }
split; [exact HC1|]. intros Hc2. destruct (HC2 Hc2) as (I2 & I3 & T1 & B2a & B2b & B2c & B2d & B2e & B2r).
split; [exact I2|]. split; [exact I3|]. split; [|exact T1].
unfold wv_buf. split; [exact B2a|]. split; [exact B2b|]. split; [exact B2c|]. split; [exact B2d|]. split; [exact B2r|].
intros x Hx. apply (nl_pt scfg L ar C IL HI HIok sp0 Hsp DL M0 _ _ _ _ _ _ x D1); lia.
+ exact HTOT.
+ rewrite VIS1. exact HFD.
+
intros R3 M3 model3 MI3 SBM3 KR3 FRM3 FRV3 GRM3 GRV3.
assert (D3 : dinvA LB LK cr A M3 model3).
{ apply (dinv_frame scfg L ar C IL HI HIok sp0 Hsp DL M0 LB LK cr A M1 M3 model1 model3 D1).
- intros a Ha Hn. apply FRM3; [exact Ha|]. intros X. apply Hn. unfold CWA. right; left. lia.
- exact GRM3.
- exact (sbm_vml _ _ SBM3).
- exact MI3.
- rewrite (sbm_halted_eq _ _ SBM3). exact Hh1. }
pose proof (ahid_sbm A model1 model3 SBM3) as AH3. rewrite VIS1 in FRV3, GRV3. rewrite <- AH3 in FRV3, GRV3.
set (MV3 := mrestrict (ahid A model3) M3) in *.
apply (IH LB LK cr A MVi S Sf tid fs fxE R3 0x11b310 M3 model3 D3).
* rewrite <- EFS. rewrite <- (proj2 (sbm_fds model model1 SBM1)). exact (proj2 (sbm_fds model1 model3 SBM3)).
* intros x Hx Hfw. fold MV3. pose proof (u64_range x) as Ux. rewrite <- (Z_to_bv_bv_unsigned 64 x). rewrite FRV3 by lia. rewrite Z_to_bv_bv_unsigned. apply AGE; assumption.
* fold MV3. eapply mem_grows_trans; [exact MGiE | exact GRV3].
* exact HS.
* exact HSf.
* exact HSf16.
* exact WINi.
* exact IMGi.
* exact XAi.
* exact SOPi.
* rewrite (sbm_fds' _ _ SBM3). exact FD1.
* fold MV3. apply (KONT R3 MV3).
-- intros x Hx. pose proof (u64_range x) as Ux. rewrite <- (Z_to_bv_bv_unsigned 64 x). rewrite FRV3 by lia. reflexivity.
-- exact GRV3.
-- exact (keep_nat RE R3 KR3).
Qed.
End Chain.
End FPX_1.

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
PropExec CatExec CatSim SeqExec StoreOk ShapeAlg ShapeLaws SpinAlg Hoare AgentLib SymDrive SymDriveX RefMemcpyLib
DrvNodesLazyK As0DrvKitA Jb0Drv_defs Jb0RegionPoisoned Jb0DiagWritev.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Jb0DiagLoopK () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Peano."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.LinuxProcessSem.Run."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanAcct."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Jb0DiagLoopK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Jb0DiagLoopK.FPX_1.Loop."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Jb0DiagWritev."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Jb0RegionPoisoned."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.RefMemcpyLib."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymDriveX."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A"; "1None"; "1Some"; "1app"; "1bool"; "1cons"; "1length"; "1list"; "1nat"; "1nil"; "1option"; "1prod"; "2I"; "2and"; "2eq"; "2not"]; ["2or"; "3le"; "3lt"; "4map"; "4skipn"; "5Z"; "0H"; "0K"; "6fetch_word"; "6word_to_le_bytes"; "7mkCfg"; "8FdChannel"; "8FdEntry"; "8Model"; "8WriteEv"; "8event"]; ["8fd_lookup"; "8m_fds"; "8m_halted"; "8m_vm_lazy"; "9bvmap"; "0Lr"; "0M"; "0M'"; "0M1"; "0MV"; "0MV'"; "0R"; "0R'"; "0R1"; ":MInv"; ":mrestrict"]; [":same_but_materialized"; ";msteps"; "=wv_buf"; "=wv_done"; "=wv_iov"; "=wv_loop_stmt"; "=wv_pc"; "=wv_regs"; "<WV_KEEP"; ">W64"; "?keeps_but"; "@getr"; "@mkst"; "@rdn"; "@regupd"; "@seg_rom"]; ["@v_addi"; "Acallee_saved"; "BTSet"; "Bt_emit"; "Csrealizes"; "DECALLW"; "Eloaded_segments"; "FIn"; "Fincl"; "Gadd"; "Gle"; "Glt"; "Gof_nat"; "Gpow"; "Gsub"; "Gto_nat"]; ["0T"; "0a"; "0b"; "0b1"; "0b2"; "0bs"; "0bs1"; "0bs2"; "0c"; "0f"; "0fd"; "0fx"; "0k"; "0l"; "0l1"; "0l2"]; ["0lazy"; "0m"; "0m'"; "0model"; "0model'"; "0model1"; "0n"; "0pc"; "0pc'"; "0q"; "0qhi"; "0qlo"; "0r"; "0s"; "0scfg"; "HBV"]; ["HZ_to_bv"; "Hbv"; "Hbv_unsigned"; "0v"; "0x"]]).
Local Ltac lia := L5FastLiaT.plia2.
Open Scope Z_scope.
#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation rom := (seg_rom ASEGS).
Definition WV_KEEP : list reg := [2; 3; 4; 8; 9; 21; 23; 24; 25; 26; 27]%bv.
Lemma wv_keep_cs : ltac2:(TCodec.tc2 tcn__Jb0DiagLoopK "<'SAy5%211&R7r1&QH%33421r2&R1%63721p041pVJ91").
Proof. intros r Hr. unfold WV_KEEP in Hr. unfold callee_saved. cbn [In] in *. tauto. Qed.
Lemma wv_keep_not : ltac2:(TCodec.tc2 tcn__Jb0DiagLoopK "Q1'SAy5%211&R7r1&QH%33421&?r2(5(S?+1(<%33<21+B%53>13+C%73@15+D%93B17+F%;3D19(9%11E%?3F31%@3G61%A3H91%B3I<1%C3J?1%J3KE1%G11p0I1pVJN1").
Proof.
intros r Hr. unfold WV_KEEP in Hr. cbn [In] in Hr.
repeat (destruct Hr as [<-|Hr]; [cbn [In]; intros X; repeat (destruct X as [X|X]; [discriminate X|]); exact X|]). destruct Hr.
Qed.
Lemma wv_keep_of : ltac2:(TCodec.tc2 tcn__Jb0DiagLoopK "QF'7'SAy5%211%411&Q4yR0%611%3261&QJr3r2r1%43321&R8r4(5(S?+1(<%33B21+B%53D13+C%73F15+D%93H17+F%;3J19(9%11K%?3L31%@3M61%A3N91%B3O<1%C3Q0?1%F3Q1E1&R7&QH%23Q4K1'>&QKr5%221Q0r6%421Q2%63Q731p081pVJQ=1p0=1p0Q51pRJQ;1pRHQ<1pR<QA1").
Proof. intros Lr R R' KB Hi r Hr. apply KB; [exact (wv_keep_cs r Hr)|]. intros X. exact (wv_keep_not r Hr (Hi r X)). Qed.
Lemma sbm_fds' : ltac2:(TCodec.tc2 tcn__Jb0DiagLoopK "F'M&Q@r2r1%3221'>'7';'SAyR0%211'L%5221%711&Q1%11=r3%311%=3531p0?1pV6D1pV4E1").
Proof. intros m m' ->. destruct m as [fd [maps lazy mat] io fsy pr lim tm]. reflexivity. Qed.
Lemma rdn_skipn_Z : ltac2:(TCodec.tc2 tcn__Jb0DiagLoopK "QI'SAyR0%211':y8%511%311p051'E'7%115'>%912&QM&R6r5&S@r4%22A1&R?r3%211%948741(2r2%22?1%?3>41'=&R:z%2216%327>%5221r6%6251r8&R9r7%221E%G2Q61&R>%128H%G11%N4M841&D%J1L%23Q91O%H2Q51%Q53Q451p0?1p0B1p0I1pUJQ<1pU<Q;1pV>Q>1pU4Q?1pR>QA1").
Proof.
intros M a n bs k Hr Hk Ha.
pose proof (SeqExec.rdn_skipn ASEGS M (Z.to_nat n) (Z_to_bv 64 a) bs (Z.to_nat k) Hr ltac:(lia)) as X.
replace (Z.to_nat (n - k)) with (Z.to_nat n - Z.to_nat k)%nat by lia.
replace (Z_to_bv 64 (a + k)) with (Z_to_bv 64 a + nat_to_word (Z.to_nat k))%bv; [exact X|].
apply bv_eq. unfold nat_to_word. rewrite bv_add_unsigned, !Z_to_bv_unsigned. rewrite Z2Nat.id by lia.
unfold bv_wrap. rewrite <- Zplus_mod. reflexivity.
Qed.
Ltac cs_in := unfold callee_saved; cbn [In]; repeat first [left; reflexivity | right].
Lemma cs_not10 : ltac2:(TCodec.tc2 tcn__Jb0DiagLoopK "B'SAy5%211&R7r1&R1%33421&?'>r2(S?+:(<%33<21%63<51%811p0:1pVJ?1").
Proof. intros r Hr ->. unfold callee_saved in Hr. cbn [In] in Hr. repeat (destruct Hr as [Hr|Hr]; [discriminate Hr|]). exact Hr. Qed.
Lemma incl_body : ltac2:(TCodec.tc2 tcn__Jb0DiagLoopK "M&R8'SAy5%211(5(S?+B(<%33621+D%53813+F%73:15(9%11;%;3<31%<3=61%=3>91'7%11@/031+1%A3D1?+C%C3F1A%E3F19%F3GB1%G3H51%L3I81").
Proof. intros r Hr. cbn [In] in *. tauto. Qed.
Lemma incl_ret : ltac2:(TCodec.tc2 tcn__Jb0DiagLoopK "N&R8'SAy5%211(5(S?+1(<%33621+C%53813(9%119%93:31%:3;61'7%11=/031+B%>3A1<+D%@3C1>+F%B3E1@%D3E1<%E3F41%F3G@1%G3H81%H3ID1%M3J<1").
Proof. intros r Hr. cbn [In] in *. tauto. Qed.
Ltac cs_out := let X := fresh in intros X; cbn [In] in X; repeat (destruct X as [X|X]; [discriminate X|]); exact X.
Lemma pcE_af0 : ltac2:(TCodec.tc2 tcn__Jb0DiagLoopK "@'>'SAyR0%211&R0&S@+QSdYL%2251+4%5221(S?+QSdZ0(<%33;21/01;%?3<61"). Proof. apply bv_eq. vm_compute. reflexivity. Qed.
Lemma pcE_b78 : ltac2:(TCodec.tc2 tcn__Jb0DiagLoopK "@'>'SAyR0%211&R0&S@+QSd^4%2251+4%5221(S?+QSd^8(<%33;21/01;%?3<61"). Proof. apply bv_eq. vm_compute. reflexivity. Qed.
Lemma pcE_af8 : ltac2:(TCodec.tc2 tcn__Jb0DiagLoopK "<'>'SAyR0%211(S?+QSdZ8(<%33521/015&S@%1285%;3831"). Proof. apply bv_eq. vm_compute. reflexivity. Qed.
Lemma pcE_b84 : ltac2:(TCodec.tc2 tcn__Jb0DiagLoopK "<'>'SAyR0%211(S?+QSd^D(<%33521/015&S@%1285%;3831"). Proof. apply bv_eq. vm_compute. reflexivity. Qed.
Lemma pcE_b74 : ltac2:(TCodec.tc2 tcn__Jb0DiagLoopK "<'>'SAyR0%211(S?+QSd^4(<%33521/015&S@%1285%;3831"). Proof. apply bv_eq. vm_compute. reflexivity. Qed.
Lemma rdn_frame_w : ltac2:(TCodec.tc2 tcn__Jb0DiagLoopK "R7'SAyR0%211':y8%511%311p051'E'8'7%116'>%:12&QM&R6r5&S@r3%22B1r2%746521(2r1%22=1%=3<41&R:zr4%3221&R9&R<%114%32A1&R=+2+R0%3221%<251'=r7&SB%12Q9C%A231&R;r6%?11%A271%4261%:261r9%11Or:%11Q1%Q:3Q@31p061pW:QF1r8%Q92QIB%Q=4Q<21>%Q62QAQ<%QA3Q@21p061p0I1p0Q31p0Q81pU<QG1pV>QJ1pU4QL1pRFQN1pRDQO1").
Proof.
intros MV MV' a n bs Hr Ha Hn FR. rewrite <- Hr. apply rdn_agree. intros j Hj. rewrite (u64_lit a) by lia. apply FR. rewrite u64_lit by lia. lia.
Qed.
Section FPX_1. Context {fx : PropExec.FPState}.
Variable scfg : SpuriousCfg.
Section Loop.
Variable H : word -> bool.
Variable A : list (Z * Z).
Hypothesis HH : H_off_segments ASEGS H.
Variable lazy : list (word * word).
Hypothesis HLC : lazy_cover H lazy A.
Hypothesis HAwf : A_wf A.
Variables f fd : Z.
Hypothesis Hfd : 0 < fd < 2 ^ 31.
Variables qlo qhi : Z.
Hypothesis Hq : 0 <= qlo /\ qlo <= qhi /\ qhi + 16 <= 2 ^ 47.
Hypothesis Hf : 0 <= f /\ (f + 124 <= qlo \/ qhi + 16 <= f + 120) /\ f + 124 < 2 ^ 63.
Hypothesis NLq : forall x, qlo <= x < qhi -> page_in_ranges (page_base_of x) lazy = false.
Variable K : TSet.
Hypothesis HK0 : K [].
#[using="HH HLC HAwf"] Lemma msteps_vis : ltac2:(TCodec.tc2 tcn__Jb0DiagLoopK "SH&Q4y5'SAyR0%211%5241':y8%611%311p061'M&R2'>'7';%12<<%311&Q3r2%211vS0%93521'Q>v0r3%3221%E1G&Q2r4%211(1%11L%D3631'QA&R6&QLvRKr;r:&Q?vFr9%3221&QO%11:%:598731r8r7r6%>5=3215%A3@51&?r1%>3=@1%H1Q?%Q;3Q?21%511%@1Q7%Q>3QB14%811p041pU4QJ1%Q82Q7:&Q@%12JQ>%J2IQ5r<%QG3QJ21r>%11ArA%Q03O1C%QL3R031%J1QGrB%11QI%R03R431p051pU4R;1%51K%R43R81J%N11%Q41R0%R73R;1M%Q111p041pU4RC1'R4vS>(Jr@%QH5QGE1Q<Q?%321Q<r=%74QL621p091p0B1p0N1p0Q21p0Q51pV:RJ1pR@RL1%R35R2Q29Q4QJ%>21QI%A4R6@1QIp041p0Q=1p0QI1p0R<1p0RD1p0RI1pU2S41pV8S61pRFS81pVBS?1pRJS?1pR>S;1pV@SB1pRHSB1").
Proof.
intros R pc M R' pc' MV' model T HL HI Hh MS GR KONT.
apply (rz_msteps_lz ASEGS scfg H A R pc M R' pc' MV' model T HH asegs_wx ltac:(rewrite HL; exact HLC) HAwf HI Hh MS).
intros model' HI' SBM VIS. apply (KONT _ model' HI' SBM VIS).
- intros a Ha. unfold munrestrict. destruct (H a) eqn:E; [reflexivity|]. rewrite Ha. unfold mrestrict. rewrite E. reflexivity.
- intros a Ha. unfold munrestrict. destruct (H a) eqn:E; [exact Ha|]. apply GR. unfold mrestrict. rewrite E. exact Ha.
Qed.
Definition wv_pc (s : bool) : word := if s then Z_to_bv 64 0x11d13c else Z_to_bv 64 0x11d1c4.
Definition wv_regs (s : bool) (R : bvmap 5 word) (q c rem : Z) : Prop :=
getr R 17%bv = Z_to_bv 64 66 /\ getr R 10%bv = Z_to_bv 64 fd /\ getr R 11%bv = Z_to_bv 64 q /\ getr R 12%bv = Z_to_bv 64 c
/\ getr R 9%bv = Z_to_bv 64 f /\ getr R 18%bv = Z_to_bv 64 c /\ getr R 22%bv = Z_to_bv 64 rem
/\ getr R (if s then 19%bv else 20%bv) = Z_to_bv 64 q.
Definition wv_buf (MV : word -> option byte) (b l : Z) (bs : list byte) : Prop :=
0 <= b /\ 0 <= l /\ b + l <= 2 ^ 47 /\ (l = 0 \/ b + l <= qlo \/ qhi <= b)
/\ rdn ASEGS MV (Z_to_bv 64 b) (Z.to_nat l) = Some bs
/\ (forall x, b <= x < b + l -> page_in_ranges (page_base_of x) lazy = false).
Definition wv_iov (MV : word -> option byte) (q c b1 l1 b2 l2 : Z) (bs1 bs2 : list byte) : Prop :=
qlo <= q /\ q + 16 * c <= qhi /\ (c = 1 \/ c = 2)
/\ rdn ASEGS MV (Z_to_bv 64 q) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 b1))
/\ rdn ASEGS MV (Z_to_bv 64 (q + 8)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 l1))
/\ store_ok ASEGS MV (Z_to_bv 64 q) (Z.to_nat (16 * c)) = true
/\ wv_buf MV b1 l1 bs1
/\ (c = 1 -> l2 = 0 /\ bs2 = [])
/\ (c = 2 -> rdn ASEGS MV (Z_to_bv 64 (q + 16)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 b2))
/\ rdn ASEGS MV (Z_to_bv 64 (q + 24)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 l2))
/\ wv_buf MV b2 l2 bs2 /\ 1 <= l1 + l2).
#[using="f Hq Hf"] Lemma wv_buf_tr : ltac2:(TCodec.tc2 tcn__Jb0DiagLoopK "QI'SAyR0%211':y8%511%311p051pW:62'E'7%116&QBr5r3r2r1%544321'=&R:z%2215&R;&R=+2+R0%3221%52;1%:271&?vS;%<21@vS:%;2B1%@231%611'>r8&S@%12Q6I%311r9%113%73Q531p091p0A1pU4Q51r6r4%Q542Q41Q3p041p0Q21pU<Q91pULQ<1pU6Q=1pRFQ?1pRDQA1").
Proof.
intros MV MV' b l bs (B1 & B2 & B3 & B4 & B5 & B6) FR. repeat split; try assumption.
rewrite <- B5. apply rdn_agree. intros j Hj. rewrite u64_lit by lia. apply FR; lia.
Qed.
#[using="f Hq Hf"] Lemma wv_buf_skip : ltac2:(TCodec.tc2 tcn__Jb0DiagLoopK "Q9'SAyR0%211':y8%511%311p051'E'7%115&QBr5r4r3r2%544321'=&R:z%2215%3268%5221r7&R9r6%221<&R>%12@>&D&R?%11A%33K1C%F4:751p0<1p0C1pUJL1pU<K1pULN1pU6O1pRDQ11").
Proof.
intros MV b l bs k (B1 & B2 & B3 & B4 & B5 & B6) Hk. repeat split; try lia.
- exact (rdn_skipn_Z MV b l bs k B5 Hk B1).
- intros x Hx. apply B6. lia.
Qed.
Definition wv_done (R : bvmap 5 word) (M : word -> option byte) (model : Model) : Prop :=
forall R' M' (model' : Model),
MInv A model' -> same_but_materialized model model' ->
(forall r, In r WV_KEEP -> getr R' r = getr R r) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (qlo <= a < qhi) -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (qlo <= a < qhi) -> mrestrict H M' (Z_to_bv 64 a) = mrestrict H M (Z_to_bv 64 a)) ->
(forall a : word, M a <> None -> M' a <> None) ->
(forall a : word, mrestrict H M a <> None -> mrestrict H M' a <> None) ->
srealizes ASEGS scfg (mkCfg (mkst R' (Z_to_bv 64 0x11d148) M' rom) model') K.
#[using="Type"] Lemma wv_done_tr : ltac2:(TCodec.tc2 tcn__Jb0DiagLoopK "S;&Q4y5'SAyR0%211%5241':y8%611%311p061'MpW:83&QCr6r5r4%43321&Q@r2%2251%C1D&R7r1&QH%33421'>&QKr7%221:r:%421<%63L31p081pVJ=1'E'=&R:z%221@&R;&R=+2+R0%3221%52F1%:271&?vS;%<21NvS:%;2Q01%@231%611r8&S@r3%22QF1%411r;%113%Q33QD31p091p0A1pU4M1&Q?vFr9%3321;r<%5341=%Q=3QN31p0C1p0K1pU4Q71%@1QD(1%11R5%QD3R531%Q011%=1QM%QG3R814%Q311p041pU4R@1%D3C@QN%QL3R=19%Q811%G3FQJR5%QO3R@1<%Q;11p041pU4RH1%R@3QOJQ7p021p0;1p0F1p0Q11p0R01p0R?1p0RC1pV<RJ1pRBRJ1pRLS21pV8RM1pR>RO1pRHS51").
Proof.
intros R M model R1 M1 model1 D SBM KR F1 F2 G1 G2 R' M' model' MI SBM' KR' F1' F2' G1' G2'.
apply (D R' M' model' MI (same_but_materialized_trans _ _ _ SBM SBM')).
- intros r Hr. rewrite (KR' r Hr). exact (KR r Hr).
- intros a Ha Hn. rewrite (F1' a Ha Hn). exact (F1 a Ha Hn).
- intros a Ha Hn. rewrite (F2' a Ha Hn). exact (F2 a Ha Hn).
- intros a Ha. exact (G1' a (G1 a Ha)).
- intros a Ha. exact (G2' a (G2 a Ha)).
Qed.
#[using="Type"] Lemma W64_out : ltac2:(TCodec.tc2 tcn__Jb0DiagLoopK "Q?'SAyR0%211':y8%511%311p051'E&R:zr3%3221&R9r4+8%3221&R=+2+R0%3221%<251&?'=r5&SB%12I?%B231&R;%@25>%2241%8241%:11'>&QIr7r6%3421=G%31H%63Q121p081p0D1p0N1pW:Q91pW8Q41pU4Q51pR>Q71").
Proof.
intros M a v x Ha Hb Hn. unfold W64. destruct (Z_lt_le_dec (bv_unsigned x) a) as [Lt|Ge].
- apply wbytes_below; [rewrite u64_lit by lia; rewrite length_N_to_le_bytes; lia | rewrite u64_lit by lia; exact Lt].
- apply wbytes_above. rewrite u64_lit by lia. rewrite length_N_to_le_bytes. lia.
Qed.
#[using="Type"] Lemma W64_hit : ltac2:(TCodec.tc2 tcn__Jb0DiagLoopK "Q?'SAyR0%211':y8%511%311p051'E&R:zr2%3221&R9r3+8%3221&R=+2+R0%3221%<251'>'7%11C%F11&QM&R6&QIr5r4%3321A&S@%12Q03u8%948421(2&I%62Q5H%2251%42@1%C3@61p0E1p0O1pW8Q41pU4Q51pR>Q71").
Proof. intros M a v Ha Hb. unfold W64. apply rdn_wbytes_hit8. rewrite u64_lit by lia. lia. Qed.
#[using="Type"] Lemma W64_rdn_out : ltac2:(TCodec.tc2 tcn__Jb0DiagLoopK "R6'SAyR0%211':y8%511%311p051'E'8'7%116&R:zr5%3221&R9r6+8%3221&R=+2+R0%3221%<251&R<%11<%;2:1%@215'@r7%61>%@221r9%F221%C22A%H216%8231'>%Q41L&QM&R6r;&S@r8%22Q<1%64541@(2%12Q5O%;3:31&QIr<r:%332;1%;2QEE%?4>21;%92Q=J%C3B21p091p0F1p0Q01p0Q>1p0Q61p0Q@1pU<QE1pV>QH1pW:QJ1pW8QK1pU4QL1pR>QN1").
Proof.
intros M a v x n bs Ha Hb Hx Hn Hd Hr. rewrite <- Hr. apply rdn_agree. intros j Hj. rewrite u64_lit by lia.
apply W64_out; [exact Ha | exact Hb |]. rewrite u64_lit by lia. lia.
Qed.
Definition wv_loop_stmt (n : nat) : Prop :=
forall (s : bool) R M (model : Model) q c b1 l1 b2 l2 bs1 bs2,
(length (bs1 ++ bs2) <= n)%nat ->
m_vm_lazy model = lazy -> MInv A model -> m_halted model = None ->
fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
wv_regs s R q c (l1 + l2) ->
wv_iov (mrestrict H M) q c b1 l1 b2 l2 bs1 bs2 ->
l1 + l2 <= 2 ^ 30 ->
rdn ASEGS (mrestrict H M) (Z_to_bv 64 (f + 120)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 fd)) ->
wv_done R M model ->
srealizes ASEGS scfg (mkCfg (mkst R (wv_pc s) M rom) model) (t_emit (map (WriteEv (Z_to_bv 64 fd)) (bs1 ++ bs2)) K).
#[using="Type"] Lemma wv_buf_len : ltac2:(TCodec.tc2 tcn__Jb0DiagLoopK "M'SAyR0%211':y8%511%311p051'E'7%115&QBr4r3r2r1%544321'>'8&6%12?6&R?%119%63531p081pU<?1pULB1pU6C1pRDE1").
Proof. intros MV b l bs (_ & _ & _ & _ & B5 & _). exact (rdn_length _ _ _ _ _ B5). Qed.
Section SE.
Variables (n : nat).
Lemma wv_after : (forall m, (m < n)%nat -> wv_loop_stmt m) ->
forall (s : bool) R M (model : Model) q c b1 l1 b2 l2 bs1 bs2 (k : nat),
(length (bs1 ++ bs2) <= n)%nat -> (k <= length (bs1 ++ bs2))%nat -> (1 <= k)%nat \/ l1 + l2 = 0 ->
m_vm_lazy model = lazy -> MInv A model -> m_halted model = None ->
fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
wv_regs s R q c (l1 + l2) ->
wv_iov (mrestrict H M) q c b1 l1 b2 l2 bs1 bs2 ->
l1 + l2 <= 2 ^ 30 ->
rdn ASEGS (mrestrict H M) (Z_to_bv 64 (f + 120)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 fd)) ->
wv_done R M model ->
srealizes ASEGS scfg (mkCfg (mkst (regupd R 10%bv (Z_to_bv 64 (Z.of_nat k))) (v_addi (wv_pc s) 4) M rom) model)
(t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn k (bs1 ++ bs2))) K).
Proof using HH HLC HAwf Hfd Hq Hf HK0 n.
intros IH s R M model q c b1 l1 b2 l2 bs1 bs2 k Hn Hk Hk1 HL HI Hh FD RG IOV H30 HFD DONE.
destruct RG as (G17 & G10 & G11 & G12 & G9 & G18 & G22 & Gq).
destruct IOV as (Q1 & Q2 & Hc & C0 & C8 & SOK & BUF1 & HC1 & HC2).
pose proof (wv_buf_len _ _ _ _ BUF1) as LEN1.
assert (LEN2 : length bs2 = Z.to_nat l2 /\ 0 <= l2).
{ destruct Hc as [->| ->]; [destruct (HC1 eq_refl) as (-> & ->); split; [reflexivity | lia]|].
destruct (HC2 eq_refl) as (_ & _ & BUF2 & _). split; [exact (wv_buf_len _ _ _ _ BUF2) | exact (proj1 (proj2 BUF2))]. }
destruct LEN2 as (LEN2 & Hl2). pose proof BUF1 as (Hb1 & Hl1 & Hb1l & _).
assert (LEN : Z.of_nat (length (bs1 ++ bs2)) = l1 + l2) by (rewrite length_app, LEN1, LEN2; lia).
set (R1 := regupd R 10%bv (Z_to_bv 64 (Z.of_nat k))).
assert (R1k : getr R1 10%bv = Z_to_bv 64 (Z.of_nat k)) by (unfold R1; apply getr_same; intros X; discriminate X).
assert (R1o : forall r : reg, r <> 10%bv -> getr R1 r = getr R r) by (intros r Hr; unfold R1; apply getr_other; exact Hr).
assert (Hq' : 0 <= q /\ q + 32 < 2 ^ 63) by lia.
assert (RET : exists R2, msteps ASEGS (mkst R1 (v_addi (wv_pc s) 4) (mrestrict H M) rom)
(mkst R2 (if Z.eqb (Z.of_nat k) (l1 + l2) then Z_to_bv 64 0x11d148 else Z_to_bv 64 0x11d1d4) (mrestrict H M) rom)
/\ getr R2 10%bv = Z_to_bv 64 (Z.of_nat k) /\ getr R2 19%bv = Z_to_bv 64 q
/\ (forall r, In r callee_saved -> ~ In r [1; 19]%bv -> getr R2 r = getr R r)).
{ rewrite <- pcE_af8, <- pcE_b84. destruct s; cbn [wv_pc] in *; [rewrite pcE_af0 | rewrite pcE_b78].
- destruct (wv_ret_A (mrestrict H M) rom q (l1 + l2) (Z.of_nat k) ltac:(lia) ltac:(lia) Hq' R1 R1k ltac:(rewrite R1o by (intros X; discriminate X); exact G22))
as (R2 & MS & V10 & KB).
exists R2. split; [exact MS|]. split; [exact V10|]. split.
+ rewrite (KB 19%bv ltac:(cs_in) ltac:(cs_out)). rewrite R1o by (intros X; discriminate X). exact Gq.
+ intros r Hr Hn'. rewrite (KB r Hr) by (intros X; apply Hn'; cbn [In] in *; tauto). apply R1o. exact (cs_not10 r Hr).
- destruct (wv_ret_B (mrestrict H M) rom q (l1 + l2) (Z.of_nat k) ltac:(lia) ltac:(lia) Hq' R1 R1k ltac:(rewrite R1o by (intros X; discriminate X); exact G22)
ltac:(rewrite R1o by (intros X; discriminate X); exact Gq)) as (R2 & MS & V10 & V19 & KB).
exists R2. split; [exact MS|]. split; [exact V10|]. split; [exact V19|].
intros r Hr Hn'. rewrite (KB r Hr Hn'). apply R1o. exact (cs_not10 r Hr). }
destruct RET as (R2 & MS2 & V10 & V19 & KB2).
apply (msteps_vis R1 _ M R2 _ (mrestrict H M) model _ HL HI Hh MS2 (fun a Ha => Ha)).
intros M2 model2 HI2 SBM2 VIS2 FRM2 GRM2.
assert (EQ2 : forall a, M2 a = M a) by (intros a; apply FRM2; reflexivity).
assert (DONE2 : wv_done R2 M2 model2).
{ apply (wv_done_tr R M model R2 M2 model2 DONE SBM2).
- intros r Hr. apply KB2; [exact (wv_keep_cs r Hr)|]. intros X. exact (wv_keep_not r Hr (incl_ret r X)).
- intros a _ _. apply EQ2.
- intros a _ _. rewrite VIS2. reflexivity.
- exact GRM2.
- intros a Ha. rewrite VIS2. exact Ha. }
assert (HL2 : m_vm_lazy model2 = lazy) by (rewrite (sbm_lazy_eq _ _ SBM2); exact HL).
assert (Hh2 : m_halted model2 = None) by (rewrite (sbm_halted_eq _ _ SBM2); exact Hh).
assert (FD2 : fd_lookup (m_fds model2) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd))) by (rewrite (sbm_fds' _ _ SBM2); exact FD).
destruct (Z.eqb_spec (Z.of_nat k) (l1 + l2)) as [E|NE].
-
rewrite skipn_all2 by lia. cbn [map].
apply (srz_conseq ASEGS scfg _ K); [|apply t_eq_sym; apply t_emit_nil_eq; exact HK0].
apply (DONE2 R2 M2 model2 HI2 (same_but_materialized_refl _)); auto.
-
assert (Hk1' : (1 <= k)%nat) by (destruct Hk1 as [?|Z0]; [assumption | lia]).
assert (NPOS : (0 < n)%nat) by lia.
assert (R2o : forall r : reg, In r callee_saved -> ~ In r [1; 19]%bv -> getr R2 r = getr R r) by exact KB2.
assert (V18 : getr R2 18%bv = Z_to_bv 64 c) by (rewrite (R2o 18%bv ltac:(cs_in) ltac:(cs_out)); exact G18).
assert (V22 : getr R2 22%bv = Z_to_bv 64 (l1 + l2)) by (rewrite (R2o 22%bv ltac:(cs_in) ltac:(cs_out)); exact G22).
assert (V9 : getr R2 9%bv = Z_to_bv 64 f) by (rewrite (R2o 9%bv ltac:(cs_in) ltac:(cs_out)); exact G9).
assert (Hf' : 0 <= f /\ (f + 124 <= q \/ q + 32 <= f + 120) /\ f + 124 < 2 ^ 63) by lia.
destruct (Z_le_gt_dec (Z.of_nat k) l1) as [LO|HI'].
+
assert (SOK16 : store_ok ASEGS (mrestrict H M) (Z_to_bv 64 q) 16 = true).
{ apply (store_ok_sub ASEGS _ (Z_to_bv 64 q) _ (Z.to_nat (16 * c))); [rewrite u64_lit by lia; lia | exact SOK | lia | rewrite u64_lit by lia; lia]. }
destruct (wv_body_lo (mrestrict H M) rom f q c (l1 + l2) (Z.of_nat k) ltac:(lia) ltac:(lia) Hq' b1 l1 fd Hf' ltac:(lia) HFD ltac:(lia) ltac:(lia)
R2 ltac:(lia) Hb1 ltac:(lia) C0 C8 SOK16 V10 V19 V18 V22 V9 ltac:(lia))
as (R3 & MS3 & W17 & W10 & W11 & W12 & W20 & W18 & W22 & KB3).
rewrite pcE_b84, pcE_b74 in MS3.
set (MV3 := W64 (W64 (mrestrict H M) q (b1 + Z.of_nat k)) (q + 8) (l1 - Z.of_nat k)) in *.
assert (FR3f : forall x : word, ~ (q <= bv_unsigned x < q + 16) -> MV3 x = mrestrict H M x).
{ intros x Hx. unfold MV3. rewrite !W64_out; [reflexivity | | | | | |]; lia. }
assert (FR3 : forall a, 0 <= a < 2 ^ 64 -> ~ (qlo <= a < qhi) -> MV3 (Z_to_bv 64 a) = mrestrict H M (Z_to_bv 64 a)).
{ intros a Ha Hna. apply FR3f. rewrite u64_lit by lia. lia. }
assert (GR3 : forall a : word, mrestrict H M a <> None -> MV3 a <> None).
{ intros a Ha. unfold MV3, W64. apply wbytes_grows. apply wbytes_grows. exact Ha. }
rewrite <- VIS2 in MS3.
apply (msteps_vis R2 _ M2 R3 _ MV3 model2 _ HL2 HI2 Hh2 MS3 ltac:(rewrite VIS2; exact GR3)).
intros M3 model3 HI3 SBM3 VIS3 FRM3 GRM3.
assert (IHn : wv_loop_stmt (n - 1)) by (apply IH; lia).
replace (skipn k (bs1 ++ bs2)) with (skipn k bs1 ++ bs2).
2:{ rewrite skipn_app. replace (k - length bs1)%nat with 0%nat by lia. reflexivity. }
replace k with (Z.to_nat (Z.of_nat k)) at 1 by lia.
apply (IHn false R3 M3 model3 q c (b1 + Z.of_nat k) (l1 - Z.of_nat k) b2 l2).
* rewrite length_app, length_skipn, Nat2Z.id. rewrite length_app in Hn. lia.
* rewrite (sbm_lazy_eq _ _ SBM3); exact HL2.
* exact HI3.
* rewrite (sbm_halted_eq _ _ SBM3); exact Hh2.
* rewrite (sbm_fds' _ _ SBM3); exact FD2.
* unfold wv_regs. replace (l1 - Z.of_nat k + l2) with (l1 + l2 - Z.of_nat k) by ring. repeat split; try assumption.
rewrite (KB3 9%bv ltac:(cs_in) ltac:(cs_out)). exact V9.
* rewrite VIS3. unfold wv_iov. split; [exact Q1|]. split; [exact Q2|]. split; [exact Hc|].
split; [unfold MV3; apply W64_rdn_out; [lia | lia | lia | cbn; lia | cbn; lia | apply W64_hit; lia]|].
split; [unfold MV3; apply W64_hit; lia|].
split; [apply (store_ok_mono ASEGS _ (mrestrict H M) MV3); [exact GR3 | exact SOK]|].
split; [apply (wv_buf_tr (mrestrict H M) MV3); [apply wv_buf_skip; [exact BUF1 | lia] | exact FR3]|].
split; [exact HC1|].
intros Hc2. destruct (HC2 Hc2) as (C16 & C24 & BUF2 & TOT).
split; [apply (rdn_frame_w _ MV3 _ _ _ C16); [lia | cbn; lia | intros x Hx; apply FR3f; cbn in Hx; lia]|].
split; [apply (rdn_frame_w _ MV3 _ _ _ C24); [lia | cbn; lia | intros x Hx; apply FR3f; cbn in Hx; lia]|].
split; [exact (wv_buf_tr _ MV3 _ _ _ BUF2 FR3) | lia].
* lia.
* rewrite VIS3. apply (rdn_frame_w _ MV3 _ _ _ HFD); [lia | cbn; lia | intros x Hx; apply FR3f; cbn in Hx; lia].
* apply (wv_done_tr R2 M2 model2 R3 M3 model3 DONE2 SBM3).
-- exact (wv_keep_of _ R2 R3 KB3 incl_body).
-- intros a Ha Hna. apply FRM3. rewrite VIS2. apply FR3; assumption.
-- intros a Ha Hna. rewrite VIS3, VIS2. apply FR3; assumption.
-- exact GRM3.
-- intros a Ha. rewrite VIS3. apply GR3. rewrite <- VIS2. exact Ha.
+
assert (Hc2 : c = 2) by (destruct Hc as [Hc|Hc]; [destruct (HC1 Hc) as (Z0 & _); lia | exact Hc]).
destruct (HC2 Hc2) as (C16 & C24 & BUF2 & TOT). pose proof BUF2 as (Hb2 & _ & Hb2l & _). subst c.
assert (SOK16 : store_ok ASEGS (mrestrict H M) (Z_to_bv 64 (q + 16)) 16 = true).
{ apply (store_ok_sub ASEGS _ (Z_to_bv 64 q) _ (Z.to_nat (16 * 2))); [rewrite u64_lit by lia; lia | exact SOK | rewrite !u64_lit by lia; lia | rewrite !u64_lit by lia; lia]. }
destruct (wv_body_hi (mrestrict H M) rom f q 2 (l1 + l2) (Z.of_nat k) ltac:(lia) ltac:(lia) Hq' l1 fd Hf' ltac:(lia) HFD b2 l2
R2 eq_refl ltac:(lia) ltac:(lia) Hb2 ltac:(lia) C8 C16 C24 SOK16 V10 V19 V18 V22 V9 ltac:(lia))
as (R3 & MS3 & W17 & W10 & W11 & W12 & W20 & W18 & W22 & KB3).
rewrite pcE_b84, pcE_b74 in MS3.
set (d := Z.of_nat k - l1) in *.
set (MV3 := W64 (W64 (mrestrict H M) (q + 16) (b2 + d)) (q + 24) (l2 - d)) in *.
assert (FR3f : forall x : word, ~ (q + 16 <= bv_unsigned x < q + 32) -> MV3 x = mrestrict H M x).
{ intros x Hx. unfold MV3. rewrite !W64_out; [reflexivity | | | | | |]; lia. }
assert (FR3 : forall a, 0 <= a < 2 ^ 64 -> ~ (qlo <= a < qhi) -> MV3 (Z_to_bv 64 a) = mrestrict H M (Z_to_bv 64 a)).
{ intros a Ha Hna. apply FR3f. rewrite u64_lit by lia. lia. }
assert (GR3 : forall a : word, mrestrict H M a <> None -> MV3 a <> None).
{ intros a Ha. unfold MV3, W64. apply wbytes_grows. apply wbytes_grows. exact Ha. }
rewrite <- VIS2 in MS3.
apply (msteps_vis R2 _ M2 R3 _ MV3 model2 _ HL2 HI2 Hh2 MS3 ltac:(rewrite VIS2; exact GR3)).
intros M3 model3 HI3 SBM3 VIS3 FRM3 GRM3.
assert (IHn : wv_loop_stmt (n - 1)) by (apply IH; lia).
replace (skipn k (bs1 ++ bs2)) with (skipn (Z.to_nat d) bs2 ++ []).
2:{ assert (E1 : skipn k bs1 = []) by (apply skipn_all2; lia). rewrite app_nil_r, skipn_app, E1. cbn [app]. f_equal. unfold d. lia. }
apply (IHn false R3 M3 model3 (q + 16) 1 (b2 + d) (l2 - d) 0 0).
* rewrite app_nil_r, length_skipn. rewrite length_app in Hn. unfold d. lia.
* rewrite (sbm_lazy_eq _ _ SBM3); exact HL2.
* exact HI3.
* rewrite (sbm_halted_eq _ _ SBM3); exact Hh2.
* rewrite (sbm_fds' _ _ SBM3); exact FD2.
* unfold wv_regs. replace (l2 - d + 0) with (l1 + l2 - Z.of_nat k) by (unfold d; ring). repeat split; try assumption.
rewrite (KB3 9%bv ltac:(cs_in) ltac:(cs_out)). exact V9.
* rewrite VIS3. unfold wv_iov. split; [lia|]. split; [lia|]. split; [left; reflexivity|].
split; [unfold MV3; apply W64_rdn_out; [lia | lia | lia | cbn; lia | cbn; lia | apply W64_hit; lia]|].
split; [replace (q + 16 + 8) with (q + 24) by ring; unfold MV3; apply W64_hit; lia|].
split; [apply (store_ok_mono ASEGS _ (mrestrict H M) MV3); [exact GR3 | exact SOK16]|].
split; [apply (wv_buf_tr (mrestrict H M) MV3); [apply wv_buf_skip; [exact BUF2 | unfold d; lia] | exact FR3]|].
split; [intros _; split; reflexivity | intros X; discriminate X].
* unfold d. lia.
* rewrite VIS3. apply (rdn_frame_w _ MV3 _ _ _ HFD); [lia | cbn; lia | intros x Hx; apply FR3f; cbn in Hx; lia].
* apply (wv_done_tr R2 M2 model2 R3 M3 model3 DONE2 SBM3).
-- exact (wv_keep_of _ R2 R3 KB3 incl_body).
-- intros a Ha Hna. apply FRM3. rewrite VIS2. apply FR3; assumption.
-- intros a Ha Hna. rewrite VIS3, VIS2. apply FR3; assumption.
-- exact GRM3.
-- intros a Ha. rewrite VIS3. apply GR3. rewrite <- VIS2. exact Ha.
Qed.
End SE.
#[using="Type"] Lemma fetch_wv_pc : ltac2:(TCodec.tc2 tcn__Jb0DiagLoopK "B'4'>':'SAyQ0%211%411&H&R6&QFr1%211%5241(2&R5%22:1%?3:41pVLA1").
Proof. intros [|]; vm_compute; reflexivity. Qed.
#[using="HH HLC HAwf Hfd Hq Hf NLq HK0"] Theorem wv_loop : ltac2:(TCodec.tc2 tcn__Jb0DiagLoopK "5'8&QEr1%211pV>41").
Proof.
intros n. induction n as [n IH] using lt_wf_ind.
intros s R M model q c b1 l1 b2 l2 bs1 bs2 Hn HL HI Hh FD RG IOV H30 HFD DONE.
pose proof RG as (G17 & G10 & G11 & G12 & G9 & G18 & G22 & Gq).
pose proof IOV as (Q1 & Q2 & Hc & C0 & C8 & SOK & BUF1 & HC1 & HC2).
pose proof BUF1 as (Hb1 & Hl1 & Hb1l & _ & RD1 & NL1).
pose proof (wv_buf_len _ _ _ _ BUF1) as LEN1.
assert (NLI : forall m, m <= qhi - q -> nolazy_rng (m_vm_lazy model) (Z_to_bv 64 q) m).
{ intros m Hm j Hj. rewrite HL, u64_lit by lia. apply NLq. lia. }
assert (UQ : bv_unsigned (Z_to_bv 64 q) = q) by (apply u64_lit; lia).
assert (C0f := rdn_of_mrestrict ASEGS H M HH _ _ _ C0). assert (C8f := rdn_of_mrestrict ASEGS H M HH _ _ _ C8).
assert (RD1f := rdn_of_mrestrict ASEGS H M HH _ _ _ RD1).
destruct Hc as [Hc1|Hc2].
-
destruct (HC1 Hc1) as (-> & ->). subst c. rewrite app_nil_r in *. rewrite Z.add_0_r in *.
destruct (Z.eq_dec l1 0) as [Z0|NZ].
+
subst l1. assert (bs1 = []) by (apply length_zero_iff_nil; exact LEN1). subst bs1.
eapply (rz_writev1_zero_lz ASEGS scfg R (wv_pc s) M model ECALLW fd (Z_to_bv 64 q) (Z_to_bv 64 b1));
[apply fetch_wv_pc | apply is_ecall_ECALLW | exact Hh | exact FD | exact Hfd | exact G17 | exact G10 | exact G11 | exact G12
| exact C0f | rewrite UQ; exact C8f | rewrite UQ; unfold TASK_SIZE; lia | rewrite u64_lit by lia; unfold TASK_SIZE; lia | apply NLI; lia |].
pose proof (wv_after n IH s R M model q 1 b1 0 b2 0 [] [] 0%nat) as X. cbn [app skipn Z.of_nat] in X. rewrite Z.add_0_r in X.
apply X; try assumption; try lia.
+ eapply (rz_writev1_wall_lz ASEGS scfg R (wv_pc s) M model ECALLW fd (Z_to_bv 64 q) (Z_to_bv 64 b1) (Z_to_bv 64 l1) bs1 K);
[apply fetch_wv_pc | apply is_ecall_ECALLW | exact Hh | exact FD | exact Hfd | exact G17 | exact G10 | exact G11 | exact G12
| exact C0f | rewrite UQ; exact C8f | unfold word_to_nat; rewrite u64_lit by lia; exact RD1f
| rewrite UQ; unfold TASK_SIZE; lia | rewrite !u64_lit by lia; unfold TASK_SIZE; lia | apply NLI; lia
| intros j Hj; rewrite HL; rewrite !u64_lit in * by lia; apply NL1; lia | rewrite u64_lit by lia; lia | rewrite u64_lit by lia; lia | exact HK0 |].
intros k Hk1 Hk2.
pose proof (wv_after n IH s R M model q 1 b1 l1 b2 0 bs1 [] k) as X. rewrite app_nil_r, Z.add_0_r in X.
apply X; try assumption; try lia.
-
destruct (HC2 Hc2) as (C16 & C24 & BUF2 & TOT). subst c.
pose proof BUF2 as (Hb2 & Hl2 & Hb2l & _ & RD2 & NL2).
assert (C16f := rdn_of_mrestrict ASEGS H M HH _ _ _ C16). assert (C24f := rdn_of_mrestrict ASEGS H M HH _ _ _ C24).
assert (RD2f := rdn_of_mrestrict ASEGS H M HH _ _ _ RD2).
eapply (rz_writev2_wall_lz ASEGS scfg R (wv_pc s) M model ECALLW fd (Z_to_bv 64 q) (Z_to_bv 64 b1) (Z_to_bv 64 l1) (Z_to_bv 64 b2) (Z_to_bv 64 l2) bs1 bs2 K);
[apply fetch_wv_pc | apply is_ecall_ECALLW | exact Hh | exact FD | exact Hfd | exact G17 | exact G10 | exact G11 | exact G12
| exact C0f | rewrite UQ; exact C8f | rewrite UQ; exact C16f | rewrite UQ; exact C24f
| unfold word_to_nat; rewrite u64_lit by lia; exact RD1f | unfold word_to_nat; rewrite u64_lit by lia; exact RD2f
| rewrite UQ; unfold TASK_SIZE; lia | rewrite !u64_lit by lia; unfold TASK_SIZE; lia | rewrite !u64_lit by lia; unfold TASK_SIZE; lia
| apply NLI; lia
| intros j Hj; rewrite HL; rewrite !u64_lit in * by lia; apply NL1; lia
| intros j Hj; rewrite HL; rewrite !u64_lit in * by lia; apply NL2; lia
| rewrite !u64_lit by lia; lia | rewrite !u64_lit by lia; lia | exact HK0 |].
intros k Hk1 Hk2.
apply (wv_after n IH s R M model q 2 b1 l1 b2 l2 bs1 bs2 k); try assumption. left; exact Hk1.
Qed.
End Loop.
End FPX_1.

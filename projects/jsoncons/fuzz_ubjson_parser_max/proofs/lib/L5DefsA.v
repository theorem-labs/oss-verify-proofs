(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct
HeapIface HeapIfaceA BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5LazyA.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__L5DefsA () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.DecodeC."; "LinuxProcessSemantics.Riscv.Instr."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanAcct."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5DefsA.L5A.SCFG_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5KnA.L5KA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A"; "0C"; "1Some"; "1bool"; "1false"; "1fst"; "1list"; "1nat"; "1option"; "1pair"; "1prod"; "1snd"; "1true"; "2I"; "2and"; "2eq"]; ["2iff"; "2not"; "2or"; "3Forall"; "3map"; "4Z"; "0H"; "0L"; "5fetch_word"; "5is_ecall"; "6Model"; "6m_vm_lazy"; "6page_base"; "6page_in_ranges"; "7decode_any"; "8Jalr"]; ["8instr"; "9bvmap"; "0M"; "0P"; "0R"; ":mrestrict"; ":page_allowedb"; ":range_avoids"; ":segs_below_b"; ":wx_segs_nowrap"; ";msteps"; "<SB"; "<ahid"; "<asan_layout"; "<asan_statics"; "<asan_statics_cells"]; ["<cell_is"; "<in_shadow_of"; "<shadow_allowed"; "=defined"; "=hull_apart"; "=hull_hi"; "=hull_lo"; "=img_clear"; "=u32_at"; "=u64_at"; "=u8_at"; "=writable"; ">AS0_ALY_CELLS_D4"; ">as0_layout"; ">avis"; "?zeros_at"]; ["@FPState"; "@getr"; "@mkst"; "@seg_rom"; "Aloaded_segments"; "BNoDup"; "Cadd"; "Cland"; "Cle"; "Clt"; "Cmodulo"; "Cof_nat"; "Cpow"; "0W"; "0a"; "0a'"]; ["0c"; "0fx"; "0hi"; "0i"; "0k"; "0lo"; "0m"; "0n"; "0n'"; "0p"; "0pc"; "0r"; "DBV"; "DZ_to_bv"; "Dbv"; "Dbv_unsigned"]; ["0v"; "0w"]]).
Module L5A.
Abbreviation RSEGS := Asan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Asan.M.loaded_segments)) (only parsing).
Section SCFG_1.
Context {SCFG_P : ScfgP}.
Definition cfg {fx : FPState} (R : bvmap 5 word) (pc : Z) (M : word -> option byte) (model : Model) : config :=
mkCfg (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) model.
Lemma segs_below : ltac2:(TCodec.tc2 tcn__L5DefsA "8'?'3&Q8&R4+VbTP0%3221(<%73621"). Proof. vm_compute. reflexivity. Qed.
Lemma wx_nowrap : ltac2:(TCodec.tc2 tcn__L5DefsA "3&Q9&R4%211"). Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.
Lemma land_m2_even : ltac2:(TCodec.tc2 tcn__L5DefsA "C'E&R8zr1%3221'?&R:r2+2%3221%53:18&R7r3-2%3221%:3?13p061p0=1pUHB1").
Proof. intros r.
intros Hr He. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec.
change (-2) with (Z.lnot 1). rewrite Z.lnot_spec by lia.
destruct (Z.eq_dec i 0) as [->|NZ].
- rewrite Z.bit0_eqb. change (Z.testbit 1 0) with true. cbn [negb]. rewrite Bool.andb_false_r. symmetry. apply Z.eqb_neq. lia.
- replace (Z.testbit 1 i) with false. rewrite Bool.andb_true_r. reflexivity. symmetry. rewrite <- (Z.pow_0_r 2). rewrite Z.pow2_bits_eqb by lia. apply Z.eqb_neq. lia.
Qed.
Lemma ret_to : ltac2:(TCodec.tc2 tcn__L5DefsA "S8'R0&Q1y5'RNyR0%211%5241'8y8%611%311p061'EyQ0%;11'?%912&H&R4&RMr3%22A1%5241(2r2%22;1%;3:41'3&I%119(4%@3421':'Q0%221F%L11&Nr4%211(9(O(RLz(=%33Q:21+1%53Q<13y<%73165%93531+4%<4BQ721%M2B1%Q63B?1&R1r8&R;u1%211%Q82QI1%6251%Q:2QIH%Q?3QI21'>&R8r5%22H1&R9&R<+2+Q?%3221%5271%:271&R:r6%2217%QN3R11Q3'Q:&R2r<r;r9%R02R?1r:&R3%11R4%8576431r7%R62RE1%;5:9164%=3R941p0?1p0D1p0Q01p0Q:1p0R11p0R71pUHRF1pTLRE1pUFRH1pR6RJ1pR:S01pU4S71").
Proof. intros fx R M pc W r.
intros HF HEC HD H1 Hr He. eapply mst_step; [reflexivity | | apply mst_refl].
assert (D: decode_any W = Some (Jalr 0 (reg 1) (0%bv : bv 12), 4%Z)). { rewrite HD. repeat f_equal; apply bv_eq; reflexivity. }
rewrite (step_jalr_x0 RSEGS R _ M (seg_rom RSEGS) _ (reg 1) (0%bv : bv 12) (Z_to_bv 64 r) HF HEC D H1).
f_equal. f_equal. unfold v_jalr. f_equal. unfold jalr_tgtZ. change (bv_signed (0%bv : bv 12)) with 0. rewrite Z.add_0_r.
rewrite BG.unsigned_lit by lia. apply land_m2_even; lia.
Qed.
Lemma hull_lo_eq : ltac2:(TCodec.tc2 tcn__L5DefsA "7'?'E&QF&R4%211+RPP0%63521"). Proof. vm_compute. reflexivity. Qed.
Lemma hull_hi_eq : ltac2:(TCodec.tc2 tcn__L5DefsA "7'?'E&QE&R4%211+VbTP0%63521"). Proof. vm_compute. reflexivity. Qed.
Lemma hull_apart_of : ltac2:(TCodec.tc2 tcn__L5DefsA "C'E'B&R8&R6r2r1%3221+RPP0%6221+VbTP0%8216%:231&QD&R4r3%3321;p051pU@A1pTNB1").
Proof. intros a n. unfold L5.hull_apart. rewrite hull_lo_eq, hull_hi_eq. tauto. Qed.
Lemma hull_apart_lit : ltac2:(TCodec.tc2 tcn__L5DefsA "C'E&QD&R4r2r1%43321'B&R8&R6r3%2217+RPP0%5221+VbTP0%7215%9231p0;1pU@A1pTNB1").
Proof. intros a n. unfold L5.hull_apart. rewrite hull_lo_eq, hull_hi_eq. tauto. Qed.
Definition avis (H : word -> bool) (a n : Z) : Prop := forall i, 0 <= i < n -> H (Z_to_bv 64 (a + i)) = false.
Lemma avis_sub : ltac2:(TCodec.tc2 tcn__L5DefsA "L'RNyR0%211'3p021'E&QNr5r4r3%43321&R8%1253&R6%1265r6%3219%6231r8%=31<;p031p091p0<1pUBB1pU0C1pU@D1pTNE1pQ>G1").
Proof. intros H a n a' n'. intros V H1 H2 i Hi. replace (a' + i) with (a + (a' - a + i)) by lia. apply V. lia. Qed.
Lemma range_avoids_of_avis : ltac2:(TCodec.tc2 tcn__L5DefsA "Q6'RNyR0%211'3p021'E'7&QNr3r2&R;r1%211%63541&R8z%2218&R6r4%91;%3221&R<+2+R0%3221%;251&Q7r6&RMr5%22M1%5341=p071p0A1p0E1pU@M1pTNO1pQ>Q11").
Proof. intros H a n.
intros V Ha Hn k Hk. unfold woff. rewrite BG.unsigned_lit by lia. apply V. lia.
Qed.
Section WithH.
Variable H : word -> bool.
Lemma u64_at_vis : ltac2:(TCodec.tc2 tcn__L5DefsA "Q:'RNyR0%211'8y8%511%311p051'E&QNvFr2+8%43321&R8zr3%3221&R6r4%2218&R<+2+R0%3221%;251&@&QI&R4&Q5r6%22E1r5%64521>%74642?%9221p0;1p0D1p0I1pV2O1pTNQ01pR6Q21").
Proof. intros M a v. intros V Ha Hn. unfold L5.u64_at. rewrite (rdn_mrestrict_eq RSEGS H 8 M _ (range_avoids_of_avis H a 8 V Ha Hn)). tauto. Qed.
Lemma u32_at_vis : ltac2:(TCodec.tc2 tcn__L5DefsA "Q:'RNyR0%211'8y8%511%311p051'E&QNvFr2+4%43321&R8zr3%3221&R6r4%2218&R<+2+R0%3221%;251&@&QH&R4&Q5r6%22E1r5%64521>%74642?%9221p0;1p0D1p0I1pV2O1pTNQ01pR6Q21").
Proof. intros M a v. intros V Ha Hn. unfold L5.u32_at. rewrite (rdn_mrestrict_eq RSEGS H 4 M _ (range_avoids_of_avis H a 4 V Ha Hn)). tauto. Qed.
Lemma u8_at_vis : ltac2:(TCodec.tc2 tcn__L5DefsA "Q:'RNyR0%211'8y8%511%311p051'E&QNvFr2+1%43321&R8zr3%3221&R6r4%2218&R<+2+R0%3221%;251&@&QJ&R4&Q5r6%22E1r5%64521>%74642?%9221p0;1p0D1p0I1pV2O1pTNQ01pR6Q21").
Proof. intros M a v. intros V Ha Hn. unfold L5.u8_at. rewrite (rdn_mrestrict_eq RSEGS H 1 M _ (range_avoids_of_avis H a 1 V Ha Hn)). tauto. Qed.
Lemma writable_vis : ltac2:(TCodec.tc2 tcn__L5DefsA "Q:'RNyR0%211'8y8%511%311p051'E&QNvFr2r1%43321&R8zr3%3221&R6r4%2214&R<+2+R0%3221%;251&@&QK&R4&Q5r6%22E1r5%64521>%74642?%9221p0;1p0D1p0I1pU@O1pTNQ01pR6Q21").
Proof. intros M a n.
intros V Ha Hn. unfold L5.writable. split; intros W d k Hd Hk.
- rewrite <- (store_ok_mrestrict_eq RSEGS H k M). apply W; lia. apply range_avoids_of_avis. eapply avis_sub. exact V. lia. lia. lia. lia.
- rewrite (store_ok_mrestrict_eq RSEGS H k M). apply W; lia. apply range_avoids_of_avis. eapply avis_sub. exact V. lia. lia. lia. lia.
Qed.
Lemma defined_vis : ltac2:(TCodec.tc2 tcn__L5DefsA "K'RNyR0%211'8y8%511%311p051'E&QNvFr2r1%43321&@&QC&Q5r4%2281r3%53219%6342:%8221p0:1pU@@1pTNA1pR6C1").
Proof. intros M a n. intros V. unfold L5.defined. split; intros D i Hi; specialize (D i Hi); rewrite (mrestrict_visible H M _ (V i Hi)) in *; exact D. Qed.
Lemma zeros_at_vis : ltac2:(TCodec.tc2 tcn__L5DefsA "K'RNyR0%211'8y8%511%311p051'E&QNvFr2r1%43321&@&QO&Q5r4%2281r3%53219%6342:%8221p0:1pU@@1pTNA1pR6C1").
Proof. intros M a n. intros V. unfold L5KA.zeros_at. split; intros D i Hi; specialize (D i Hi); rewrite (mrestrict_visible H M _ (V i Hi)) in *; exact D. Qed.
Lemma img_clear_mrestrict : ltac2:(TCodec.tc2 tcn__L5DefsA "G'RNyR0%211'8y8%511%311p051'E&QGr3r2r1%43321&Q5vFr4%3221%93187p061pU6<1pU<=1pR6?1").
Proof. intros M lo hi. intros C i Hi. unfold mrestrict. destruct (H _); [reflexivity | apply C; exact Hi]. Qed.
Lemma mrestrict_agree : ltac2:(TCodec.tc2 tcn__L5DefsA "Q;'RNyR0%211'8y8%511%311p051'E'>&R8r3r1%3221&R9r2%2241%8241'?'3vF&RM%12E7%311(4%73621p091pU8C1r4%C21A%@2BC%F221&Q5r6%23>1<%21=%B3N21p061pU8N1p0<1pU6Q01pU<Q11pR6Q31").
Proof. intros M lo hi. intros V i Hi. apply mrestrict_visible. apply V. exact Hi. Qed.
End WithH.
Lemma ahid_not_lazy : ltac2:(TCodec.tc2 tcn__L5DefsA "N'6':'E%2211%411'J'RNyR0%211'?'3&M&Lr1%211&Kr2%211%7241(4%;3:21&Q<r4r3%33218%@3?16p061pV4C1pU>G1p2I1").
Proof. intros A m w. intros E. unfold ahid, mkH. rewrite E. reflexivity. Qed.
Lemma ahid_allowed : ltac2:(TCodec.tc2 tcn__L5DefsA "M'6':'E%2211%411'J'RNyR0%211'?'3&Q6r3&Lr1%211%5241(<%93821&Q<r4r2%332:1(4%?3>21p071pV4B1pU>F1p2H1").
Proof. intros A m w. intros E. unfold ahid, mkH. rewrite E. cbn. apply Bool.andb_false_r. Qed.
Lemma avis_of_not_lazy : ltac2:(TCodec.tc2 tcn__L5DefsA "R4'6':'E%2211%411'J!p051'RNyR0%211'?'3&M&Lr1%211&Kr5%211%7241(<%;3:21&ROr2%22@1%811p051pV4B1'>&R8z%221A&R9r3%22D1%7241&Ar6&R6%12F@%311%511p071pU8Q:1r4%@2?1%82M2&R<+2+R0%3221%F251&QN&Q<r9r8%3221%531DQ8p071p0>1p0A1p0Q21pU@QM1pTNQN1pR8QJ1pU>QM1p2QO1").
Proof. intros A m P a n.
intros HL HP Ha Hn i Hi. apply ahid_not_lazy. destruct (page_in_ranges _ _) eqn:E; [|reflexivity].
exfalso. apply (HP i Hi). specialize (HL _ E). rewrite BG.unsigned_lit in HL by lia. exact HL.
Qed.
Lemma avis_of_shadow_allowed : ltac2:(TCodec.tc2 tcn__L5DefsA "Q9'6':'E%2211%411'J&QBr6r4r3%43321'>&R8zr1%3221&R9%1238%7231&QAr7&R6r5r2%3221%635B1p081pU8I1&QN&Q<r8%221;%431HGp061p0H1pU@Q11pTNQ21pU:Q31pUDQ41pU>Q21p2Q41").
Proof. intros A m p k a n. intros SA HI i Hi. apply ahid_allowed. apply SA. apply HI. exact Hi. Qed.
Definition SM1 : Z := 0x5d3a0. Definition SM2 : Z := 0x5d530. Definition SM3 : Z := 0x5d6cc.
Definition AS0_ALY_CELLS_D4 : list (Z * Z * Z) :=
[ (0x13acf8, 8, SB); (0x13ad00, 4, 1); (0x134648, 8, 0x124db0); (0x1345d8, 8, 0x10b84c);
(0x132638, 8, 0x13acf8);
(0x132640, 8, 0x13b9e8); (0x13b9e8, 8, 0); (0x132648, 8, 0x13b9f0); (0x13b9f0, 8, 0);
(0x132650, 8, 0x13b9e0); (0x13b9e0, 8, 0x7fffffffffff);
(0x1331a0, 8, 0x13b9d9); (0x13b9d9, 1, 1);
(0x134640, 8, 0x1249ac);
(0x13b9d8, 1, 1);
(0x134538, 8, 0x125990);
(0x66ed78, 8, 0x66eda0); (0x66eda8, 8, 0x66f580);
(0x13a560, 1, 1); (0x13a564, 4, 0);
(0x66ed28, 8, 0x690238);
(0x132628, 8, 0x1cc828); (0x1cc8b1, 1, 1);
(0x132688, 8, 0x1ca798); (0x1ca798, 4, 0);
(0x133440, 8, 8) ].
Lemma AS0_ALY_CELLS_D4_nodup : ltac2:(TCodec.tc2 tcn__L5DefsA ">'R5'E&D':%1233%2214&5r1%23471%33881qU251&QL%:47;21%=2<1").
Proof.
unfold AS0_ALY_CELLS_D4; cbn [map fst].
repeat (apply List.NoDup_cons; [cbn; intros H; repeat (destruct H as [H|H]; [lia|]); exact H |]). apply List.NoDup_nil.
Qed.
Lemma AS0_ALY_CELLS_D4_img : ltac2:(TCodec.tc2 tcn__L5DefsA "G'C':'E%2211%3212'>&R8+RPP0&5r1%23781%33991%6251&R6&;%13==5%3251+VbTP0%<221%>271qU2@1&QL%F3B21").
Proof. repeat constructor; cbn; lia. Qed.
Record as0_layout (L : asan_layout) (C : asan_statics_cells) : Prop := ALY {
aly_segs : hl_segs L = RSEGS;
aly_sm1 : hl_stack_malloc L 1 = SM1; aly_sm2 : hl_stack_malloc L 2 = SM2; aly_sm3 : hl_stack_malloc L 3 = SM3;
aly_nr : hl_handle_no_return L = 0x80890;
aly_memset : hl_asan_memset L = 0x777d8; aly_memcpy : hl_asan_memcpy L = 0x7733c; aly_memmove : hl_asan_memmove L = 0x77a18;
aly_malloc : hl_malloc L = 0x78ec0; aly_free : hl_free L = 0x78ebc; aly_aligned : hl_aligned_alloc L = 0x78ec8;
aly_img_lo : hl_img_lo L = 0x10000; aly_img_hi : hl_img_hi L = 0x691000;
aly_scr_sm : hl_scr_stack_malloc L = 512; aly_scr_nr : hl_scr_no_return L = 4160; aly_scr_mem : hl_scr_mem L = 2560;
aly_scr_malloc : hl_scr_malloc L = 4096; aly_scr_free : hl_scr_free L = 4096; aly_scr_aligned : hl_scr_aligned L = 4096;
aly_got_lo : asc_got_lo C = 0x12c000; aly_got_hi : asc_got_hi C = 0x134000;
aly_cells : incl AS0_ALY_CELLS_D4 (asc_cells C);
aly_static_img : forall a, hl_rt_static L a -> 0x10000 <= a < 0x691000;
aly_ro_img : forall a, hl_rt_ro L a -> 0x10000 <= a < 0x691000;
aly_static_lo : forall a, hl_rt_static L a -> 0x134000 <= a;
aly_cost : 0 <= hl_k_per_malloc L /\ 0 <= hl_b_lin L /\ 0 <= hl_b_overhead L
}.
Lemma u64_at_of_cell : ltac2:(TCodec.tc2 tcn__L5DefsA "G'RNyR0%211'8y8%511%311p051'E&Q@&R4r3r2u8r1%6554321&QIr4%248176p041pV2<1pTN=1pR6?1"). Proof. intros M a v. intros H; exact H. Qed.
Lemma u32_at_of_cell : ltac2:(TCodec.tc2 tcn__L5DefsA "G'RNyR0%211'8y8%511%311p051'E&Q@&R4r3r2u4r1%6554321&QHr4%248176p041pV2<1pTN=1pR6?1"). Proof. intros M a v. intros H; exact H. Qed.
Lemma statics_facts : ltac2:(TCodec.tc2 tcn__L5DefsA "Q='Q='Q?'RNyR0%211'8y8%511%311p051'QMr3r2%3221&Q>&R4%23154'>&QG+QU`P0+QV`P0%33:21&QI+QW[WH&Q;%34:>21&QH+QW[X0+1%34>B21+QVab8+QTc]@%:4AE21+QVa^H+QQ^R<%=4DH21%C241%D281%E2=1%F2B1p0H1p0L1pR6Q11p4Q:1pQ@Q<1").
Proof. intros L C M.
intros LY (G & CS). rewrite (aly_got_lo L C LY), (aly_got_hi L C LY) in G. rewrite Forall_forall in CS.
pose proof (aly_cells L C LY) as IC.
split. exact G.
split. exact (CS _ (IC _ (or_introl eq_refl))).
split. exact (CS _ (IC _ (or_intror (or_introl eq_refl)))).
split. exact (CS _ (IC _ (or_intror (or_intror (or_introl eq_refl))))). exact (CS _ (IC _ (or_intror (or_intror (or_intror (or_introl eq_refl)))))).
Qed.
End SCFG_1.
End L5A.

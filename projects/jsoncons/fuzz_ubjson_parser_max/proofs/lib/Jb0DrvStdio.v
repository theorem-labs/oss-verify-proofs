(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: writes out encoded statements of rdn_tr, img_cell, vis_stk, stk_wr, stk_def, stk_sh0, hi_sh0, kimg_clear and kword_lit as plain Rocq lemmas, and turns the Section SE encoded pr_cell_vis into a plain universally quantified lemma; taken in part from projects/jsoncons/fuzz_bigint/proofs/lib/Bo0DrvStdio.v, 31 lines within its lines 34-161. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import
PropExec CatExec CatSim SeqExec StoreOk ShapeAlg SpinAlg Hoare AsanAcctShape SymExec2 SymExec2Sound SymRun SymDrive SymDriveX
HeapIface HeapIfaceA IcptIfaceAB0 DrvKitA DrvNodesLazyK As0DrvKitA Jb0DrvEntry Jb0Drv_defs Jb0DrvLib Jb0DrvRead.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Import SX2. Import SX2S.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Jb0DrvStdio () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.LinuxProcessSem.State."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanAcct."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.DrvKitA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.IcptIfaceAB0."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Jb0DrvLib."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Jb0DrvStdio."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2Sound.SX2S."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymRun."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A"; "1None"; "1O"; "1Some"; "1bool"; "1false"; "1fst"; "1list"; "1nat"; "1option"; "1pair"; "1prod"; "1snd"; "1true"; "2and"; "2eq"]; ["2not"; "2or"; "3Forall"; "4Z"; "0E"; "0HI"; "0IL"; "0LB"; "0LK"; "5store_ok"; "5word_to_le_bytes"; "6Model"; "0M"; "0M'"; "0M0"; "0MV"]; ["7mrestrict"; "8kentry_eqb"; "9credit"; ":ahid"; ":ar_sptop"; ":fframe"; ":shadow_allowed"; ";icl_poison"; "<dinv"; "<has_window"; "=PR_CELLS"; ">rdn"; "?ELit"; "?Env"; "?KImg"; "?KWord"]; ["?SA"; "?edenot"; "?env"; "?expr"; "?kentry"; "@know_ok"; "Avals_ev"; "Bloaded_segments"; "CIn"; "Cexistsb"; "Dadd"; "Ddiv"; "Dle"; "Dlt"; "Dof_nat"; "Dpow"]; ["Dsub"; "Dto_nat"; "0a"; "0ar"; "0bs"; "0cr"; "0d"; "0ebs"; "0hi"; "0i"; "0k"; "0kn"; "0lo"; "0model"; "0n"; "0r"]; ["0sp0"; "EZ_to_bv"; "Ebv"; "Ebv_unsigned"; "0v"; "0vals"; "0w"; "0x"]]).
Definition PR_CELLS : list (Z * Z * Z) :=
[(0x13d718, 1, 1); (0x13d719, 1, 1); (0x1ce5bc, 1, 1); (0x13ca38, 8, 0x7fff8000);
(0x136228, 8, 0x1242e0); (0x136230, 8, 0x11dffc); (0x1363a8, 8, 0x1267e4); (0x1363b0, 8, 0x126be8)].
Definition EX_CELLS : list (Z * Z * Z) :=
[(1270192, 8, 1270192); (1270704, 8, 1207272); (1282944, 8, 1); (1283024, 1, 0); (1286736, 4, 1); (1286896, 8, 0); (1295004, 1, 1); (1296952, 8, 2147450880); (1300248, 1, 1); (1893856, 8, 18446744073709551615); (1894624, 1, 0); (1286740, 1, 0)].
Definition DG_CELLS : list (Z * Z * Z) := [(1300248, 1, 1); (1300249, 1, 1); (1893820, 1, 1); (1296952, 8, 2147450880); (1270320, 8, 1171452); (1270696, 8, 1206244)].
Definition DGS_CELLS : list (Z * Z * Z) :=
[(1270616, 8, 1209096); (1270248, 8, 1205992); (0x13ca38, 8, 0x7fff8000); (0x13d728, 8, 0); (0x13d730, 8, 0); (0x13d720, 8, 2 ^ 47 - 1); (0x1ce663, 1, 1); (0x13d719, 1, 1); (0x1363a8, 8, 0x1267e4)].
Lemma rdn_tr : forall (M M' : word -> option byte) a (n : nat) bs,
rdn ASEGS M (Z_to_bv 64 a) n = Some bs -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
(forall i, a <= i < a + Z.of_nat n -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
rdn ASEGS M' (Z_to_bv 64 a) n = Some bs.
Proof.
intros M M' a n bs H Ha Hn HF. rewrite <- H. apply rdn_agree. intros j Hj. rewrite u_small by lia. apply HF. lia.
Qed.
Lemma img_cell : forall (MV : word -> option byte) a (n : nat) bs,
rdn ASEGS (fun _ => None) (Z_to_bv 64 a) n = Some bs -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
(forall i, a <= i < a + Z.of_nat n -> MV (Z_to_bv 64 i) = None) ->
rdn ASEGS MV (Z_to_bv 64 a) n = Some bs.
Proof. intros MV a n bs H Ha Hn HN. exact (rdn_tr (fun _ => None) MV a n bs H Ha Hn HN). Qed.
Section FPX_1. Context {fx : PropExec.FPState}.
Variable scfg : SpuriousCfg.
Section Stdio.
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
Hypothesis Hpr : incl PR_CELLS (asc_cells C).
Variable M0 : word -> option byte.
#[local] Notation dinvA := (dinv ar HI sp0 M0).
#[local] Notation usp := (bv_unsigned sp0).
Lemma vis_low : ltac2:(TCodec.tc2 tcn__Jb0DrvStdio "QF'7';'C%2211%411&Q5%611&Q2'RByR0%211'9y8%511%311p051'K'Q8vR3vEvR@vNr7r6r5r4r3r2%;::987654321'>&QLz%2215&QM+Vb\P0%2281%7241'?'4&Q3&RA%12Q0?%33CA1(5%73621p091p0B1pT6Q=1pTLQ01pQJQ21p2Q>1pT<Q<1pQBQ>1pQ@QA1").
Proof. intros LB LK cr A M model a D Ha. apply (vis_of_inv scfg L ar C IL HI HIok sp0 DL _ _ _ _ _ _ _ a (di_inv _ _ _ _ _ _ _ _ _ _ D)); lia. Qed.
Lemma vis_stk : forall LB LK cr A M (model : Model) a, dinvA LB LK cr A M model -> usp - 8388608 <= a < 2 ^ 64 -> ahid A model (Z_to_bv 64 a) = false.
Proof. intros LB LK cr A M model a D Ha. pose proof Hsp. apply (vis_of_inv scfg L ar C IL HI HIok sp0 DL _ _ _ _ _ _ _ a (di_inv _ _ _ _ _ _ _ _ _ _ D)); lia. Qed.
Lemma pr_cell_vis : forall LB LK cr A M (model : Model) a n v, dinvA LB LK cr A M model -> In (a, n, v) PR_CELLS ->
rdn ASEGS (mrestrict (ahid A model) M) (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)).
Proof.
intros LB LK cr A M model a n v.
intros D Hin.
pose proof (di_inv _ _ _ _ _ _ _ _ _ _ D) as HH.
destruct (aio_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & CS). rewrite (dla_segs _ _ _ _ DL) in CS.
pose proof (proj1 (Forall_forall _ _) CS (a, n, v) (Hpr _ Hin)) as X. unfold cell_is in X. cbn [fst snd] in X.
rewrite rdn_mrestrict_eq; [exact X|].
intros k Hk. unfold woff.
assert (B : 0 <= a /\ a + Z.of_nat (Z.to_nat n) <= 0x693000).
{ unfold PR_CELLS in Hin. cbn [In] in Hin. repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <- <-; cbn; lia|]). destruct Hin. }
rewrite (u_small a) by lia. apply (vis_low _ _ _ _ _ _ _ D). lia.
Qed.
Lemma stk_wr : forall vals ebs MV kn a n,
know_ok ASEGS (Env (vals_ev vals) ebs) MV kn -> has_window kn = true -> vals_ev vals 0 = sp0 ->
usp - 6144513 <= a -> a + n <= usp ->
forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV (Z_to_bv 64 (a + d)) k = true.
Proof.
intros vals ebs MV kn a n HK Hw P0 Ha Hn d k Hd Hk.
pose proof (window_store_ok sp0 vals ebs MV kn (a + d - usp) k HK Hw P0 ltac:(lia) ltac:(lia)) as W.
replace (usp + (a + d - usp)) with (a + d) in W by ring. exact W.
Qed.
Lemma stk_def : forall vals ebs MV kn a n,
know_ok ASEGS (Env (vals_ev vals) ebs) MV kn -> has_window kn = true -> vals_ev vals 0 = sp0 ->
usp - 6144513 <= a -> a + n <= usp ->
forall i, 0 <= i < n -> MV (Z_to_bv 64 (a + i)) <> None.
Proof.
intros vals ebs MV kn a n HK Hw P0 Ha Hn i Hi. pose proof Hsp.
pose proof (stk_wr vals ebs MV kn a n HK Hw P0 Ha Hn i 1%nat ltac:(lia) ltac:(lia)) as W.
apply (store_ok_defined sp0); [lia | exact W].
Qed.
Lemma stk_sh0 : forall LB LK cr A M (model : Model) x, dinvA LB LK cr A M model ->
(usp - 8388608) / 8 + 0x7fff8000 <= x <= (usp - 1) / 8 + 0x7fff8000 ->
mrestrict (ahid A model) M (Z_to_bv 64 x) = Some (Z_to_bv 8 0).
Proof.
intros LB LK cr A M model x D Hx. pose proof Hsp as Hsp'. pose proof (di_inv _ _ _ _ _ _ _ _ _ _ D) as HH.
pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & _ & _ & _ & _ & _ & STSH & _).
assert (CE : ahl_ceil ar = usp - 8388608) by (unfold ahl_ceil; rewrite (dla_sptop _ _ _ _ DL); reflexivity).
assert (IS : in_shadow_of (ahl_ceil ar) (ar_sptop ar - ahl_ceil ar) x).
{ unfold in_shadow_of, S, SB. rewrite CE, (dla_sptop _ _ _ _ DL). replace (usp - 8388608 + (usp - (usp - 8388608)) - 1) with (usp - 1) by ring. exact Hx. }
unfold mrestrict. rewrite (vis_of_allowed _ _ _ _ _ STSH IS).
apply (di_stksh _ _ _ _ _ _ _ _ _ _ D). unfold in_shadow_of, S, SB, STKTOP. rewrite CE, (dla_sptop _ _ _ _ DL).
assert (MX : usp <= Z.max usp (ar_stack_top ar)) by lia.
split; [lia|]. assert ((usp - 1) / 8 <= (usp - 8388608 + (Z.max usp (ar_stack_top ar) - (usp - 8388608)) - 1) / 8) by (apply Z.div_le_mono; lia). lia.
Qed.
Lemma hi_sh0 : forall LB LK cr A M (model : Model) x, dinvA LB LK cr A M model ->
shadow_allowed A (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) ->
(usp - 8388608) / 8 + 0x7fff8000 <= x <= (2 ^ 47 - 1) / 8 + 0x7fff8000 ->
mrestrict (ahid A model) M (Z_to_bv 64 x) = Some (Z_to_bv 8 0).
Proof.
intros LB LK cr A M model x D SAH Hx. pose proof Hsp as Hsp'.
assert (CE : ahl_ceil ar = usp - 8388608) by (unfold ahl_ceil; rewrite (dla_sptop _ _ _ _ DL); reflexivity).
assert (IS : in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) x).
{ unfold in_shadow_of, S, SB. rewrite CE. replace (usp - 8388608 + (2 ^ 47 - (usp - 8388608)) - 1) with (2 ^ 47 - 1) by ring. lia. }
unfold mrestrict. rewrite (vis_of_allowed _ _ _ _ _ SAH IS). exact (di_hish _ _ _ _ _ _ _ _ _ _ D x IS).
Qed.
Lemma img_sh0 : ltac2:(TCodec.tc2 tcn__Jb0DrvStdio "S2'7';'C%2211%411&Q5%611&Q2'RByR0%211'9y8%511%311p051'K'Q8vR3vEvR@vNr9r8r7r6r5r4%;::987654321&QL+RPP0%2214&QJ%1276+Vb\P0%6221&QMz%221<'B'A%92BA&6r1%23Q:Q:1%@241&<%13Q=Q=4%C21I%9241qU0Q?1&Q7vF%211%?3QC41'>&QK+8%22Q31+QoooPP0%L221%Q021Q4&R0+1%22G1%9218%Q2217%Q62Q:1%=271'?&Q0&Q3r<r:%3221r;&RA%12R4QE%83431(3%42R4Q;%22R41%=3R441p0?1p0N1p0Q?1p0QC1p0QH1p0QL1pU@RG1pTNRH1pT6RI1pTLR<1pQJR>1p2RJ1pT<RH1pQBRJ1pQ@RM1").
Proof.
intros LB LK cr A M model a n x D Ha Hn Hp HP Hx. pose proof (di_inv _ _ _ _ _ _ _ _ _ _ D) as HH.
destruct (aic_img_shadow _ _ _ _ _ ICok _ _ _ _ _ _ _ HH a n) as (Z0 & SA);
[rewrite (dla_img_lo _ _ _ _ DL); lia | rewrite (dla_img_hi _ _ _ _ DL); lia | exact Hp | exact HP |].
assert (IS : in_shadow_of a n x) by (unfold in_shadow_of, S, SB; exact Hx).
unfold mrestrict. rewrite (vis_of_allowed _ _ _ _ _ SA IS). exact (Z0 x IS).
Qed.
Lemma kimg_clear : forall E MV kn lo hi, know_ok ASEGS E MV kn -> existsb (kentry_eqb (KImg lo hi)) kn = true ->
forall i, lo <= i < hi -> MV (Z_to_bv 64 i) = None.
Proof.
intros E MV kn lo hi HK Hb. apply existsb_exists in Hb as (K & Hin & Heq). apply kentry_eqb_eq in Heq. subst K.
pose proof (proj1 (Forall_forall _ _) HK _ Hin) as X. cbn [kentry_ok] in X. exact (proj2 (proj2 X)).
Qed.
Lemma kword_lit : forall E MV kn a (w : nat) v, know_ok ASEGS E MV kn -> existsb (kentry_eqb (KWord (SA (ELit 0) a) w v)) kn = true ->
0 <= a -> a + Z.of_nat w <= 2 ^ 63 ->
rdn ASEGS MV (Z_to_bv 64 a) w = Some (word_to_le_bytes w (edenot E v)).
Proof.
intros E MV kn a w v HK Hb Ha Hw. apply existsb_exists in Hb as (K & Hin & Heq). apply kentry_eqb_eq in Heq. subst K.
pose proof (proj1 (Forall_forall _ _) HK _ Hin) as X. cbn [kentry_ok] in X. destruct X as (_ & _ & X).
unfold adenot, v_addi in X. cbn [a_base a_off edenot] in X. rewrite (u_small 0) in X by lia. rewrite Z.add_0_l in X. exact X.
Qed.
End Stdio.
End FPX_1.

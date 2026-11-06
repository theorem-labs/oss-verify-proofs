(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__L5Defs () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.Run."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5.WithSegs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1None"; "1app"; "1bool"; "1false"; "1length"; "1list"; "1nat"; "1nil"; "1option"; "1prod"; "1true"; "2and"; "2eq"; "2ex"; "2iff"; "3Z"]; ["0F"; "0G"; "0K"; "4mkCfg"; "5Model"; "5m_halted"; "5m_vm_lazy"; "6bvmap"; "0M"; "0M'"; "0M''"; "0Q"; "0R"; "0R'"; "0R''"; "7msteps"]; ["8regs_preserved"; ":defined"; ":frame_but"; ":hull_apart"; ":limbs_at"; ":outside"; ":range"; ":u64_at"; ":u8_at"; ":writable"; "9SCFG"; ";FPState"; ";mkst"; ";rdn"; ";seg_rom"; "<TSet"]; ["=srealizes"; ">mem_grows"; "0SCFG_P"; "?incl"; "@add"; "@land"; "@le"; "@lt"; "@modulo"; "@mul"; "@of_nat"; "@pow"; "@testbit"; "0a"; "0a'"; "0b"]; ["0fb"; "0fx"; "0fx'"; "0i"; "0m"; "0model"; "0n"; "0n'"; "0pc"; "0pc'"; "0q"; "0segs"; "AZ_to_bv"; "Abv"; "Abv_unsigned"; "0v"]; ["0ws"]]).
Local Ltac lia := L5FastLia.plia.
Class ScfgP : Type := MkScfgP { SCFG : SpuriousCfg }.
Module L5.
Section WithSegs.
Variable segs : list Segment.
Definition u8_at (M : word -> option byte) (a : Z) (b : Z) : Prop :=
rdn segs M (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 b].
Definition u64_at (M : word -> option byte) (a : Z) (v : Z) : Prop :=
rdn segs M (Z_to_bv 64 a) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 v)).
Definition u32_at (M : word -> option byte) (a : Z) (v : Z) : Prop :=
rdn segs M (Z_to_bv 64 a) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 v)).
Definition bytes_at (M : word -> option byte) (p : Z) (bs : list Z) : Prop :=
forall i, (i < length bs)%nat -> u8_at M (p + Z.of_nat i) (nth i bs 0).
Definition limbs_at (M : word -> option byte) (q : Z) (ws : list Z) : Prop :=
forall i, (i < length ws)%nat -> u64_at M (q + 8 * Z.of_nat i) (nth i ws 0).
Definition defined (M : word -> option byte) (a n : Z) : Prop :=
forall i, 0 <= i < n -> M (Z_to_bv 64 (a + i)) <> None.
Definition writable (M : word -> option byte) (a n : Z) : Prop :=
forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok segs M (Z_to_bv 64 (a + d)) k = true.
Definition img_clear (M : word -> option byte) (lo hi : Z) : Prop :=
forall i, lo <= i < hi -> M (Z_to_bv 64 i) = None.
Definition hull_lo : Z := fold_right Z.min (2 ^ 64) (map (fun s => Z.of_N (seg_base s)) segs).
Definition hull_hi : Z := fold_right Z.max 0 (map (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s)) segs).
Definition hull_apart (a n : Z) : Prop := a + n <= hull_lo \/ hull_hi <= a.
Lemma hull_apart_sub : ltac2:(TCodec.tc2 tcn__L5Defs "E'?&Q3r4r3%3221&QFr5%2214&QD%1276r6%3215%7231%<27;p021p081p0<1pT@A1pSNB1pT>C1pSLD1").
Proof. intros a n a' n'. unfold hull_apart. lia. Qed.
Definition range : Type := (Z * Z)%type.
Definition in_rng (r : range) (a : Z) : Prop := fst r <= a < fst r + snd r.
Definition outside (F : list range) (a : Z) : Prop := forall r, In r F -> ~ in_rng r a.
Definition frame_but (F : list range) (M M' : word -> option byte) : Prop :=
forall x : word, outside F (bv_unsigned x) -> M' x = M x.
Lemma frame_but_refl : ltac2:(TCodec.tc2 tcn__L5Defs "A'5&Q6%211'R=yR0%211'8y8%511%311p051&Q2r2r1%33211pQB51pQ2>1").
Proof. intros F M. intros x _. reflexivity. Qed.
Lemma outside_app : ltac2:(TCodec.tc2 tcn__L5Defs "D'5&Q6%211'?&>&Q5&1r3r2%33821r1%6221';%8263%9264%3221%<251pSL>1pQ4@1pQ2A1").
Proof. intros F G a. unfold outside. split. intros H; split; intros r Hr; apply H; apply in_app_iff; auto. intros [H1 H2] r Hr. apply in_app_iff in Hr. destruct Hr; auto. Qed.
Lemma frame_but_mono : ltac2:(TCodec.tc2 tcn__L5Defs "Q0'5&Q6%211'R=yR0%211'8y8%511%311p051'?&Q5r4r1%3221r6r2%6221p041pSL91&Q2r5r3%33217%433<2p021p071pQDB1pQBC1pQ4L1pQ2M1").
Proof. intros F G M M'. intros HFG HF x Hx. apply HF. apply HFG. exact Hx. Qed.
Lemma frame_but_trans : ltac2:(TCodec.tc2 tcn__L5Defs "L'5&Q6%211'R=yR0%211'8y8%511%311p051&Q2r5r3r2%43321&1r7r6%33B21%93187p061p071pQF=1pQD>1pQB?1pQ4H1pQ2I1").
Proof. intros F G M M' M''. intros H1 H2 x Hx. apply outside_app in Hx. destruct Hx as [HxF HxG]. rewrite (H2 x HxG). apply H1. exact HxF. Qed.
Lemma frame_but_weaken : ltac2:(TCodec.tc2 tcn__L5Defs "J'5&Q6%211'R=yR0%211'8y8%511%311p051&QCr4r3%33=21&Q2r5r2%33251%43376p021p071pQD<1pQB=1pQ4F1pQ2G1").
Proof. intros F G M M'. intros Hi. apply frame_but_mono. intros a HG r Hr. apply HG. apply Hi. exact Hr. Qed.
Lemma unsigned_lit : ltac2:(TCodec.tc2 tcn__L5Defs "G'?';&QFzr1%3221&QG&QK+2+R0%3221%5271%;271'<&R>yR0&R<r2%2231%5241%73D13p091pSLF1").
Proof. intros a. intros H. rewrite Z_to_bv_unsigned. unfold bv_wrap. apply Z.mod_small. exact H. Qed.
Lemma rdn_frame : ltac2:(TCodec.tc2 tcn__L5Defs "R0'R=yR0%211'8y8%511%311p051'5&Q6%211&Q2r1r3r2%43321'6'?&QFz%2218&QD&QJ%11:%32:1&QK+2+R0%3221%;251';r4%>21D&QGr5%=11%?251%42I1%8261&Q5r8%221Kp041pT8J1'<%Q51Q8%Q;11&Q=vR;&R<%12QAC%443;1Ar9%64513C%:3831p0<1p0K1p0Q51pSLQ91pT>Q;1p0Q=1pQ2QC1pQDQG1pQBQH1").
Proof. intros M M' F.
intros HF. induction n as [|n IH]; intros a Ha Hn Hout. reflexivity.
cbn [rdn]. rewrite (HF (Z_to_bv 64 a)). 2: { rewrite unsigned_lit by lia. apply Hout. lia. }
replace (Z_to_bv 64 a + 1)%bv with (Z_to_bv 64 (a + 1)).
2: { apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_unsigned (1%bv : bv 64)) with 1. rewrite <- Zplus_mod_idemp_l. reflexivity. }
rewrite (IH (a + 1)); [reflexivity | lia | lia | intros i Hi; apply Hout; lia].
Qed.
Lemma u64_at_frame : ltac2:(TCodec.tc2 tcn__L5Defs "QI'R=yR0%211'8y8%511%311p051'5&Q6%211'?&Q2r3r5r4%43321&QFz%2216&QD+8%2271&QK+2+R0%3221%:251';r6r1%>221&QG%=24<%2241%7241&Q5r8r2%3221p051pT8N1&Q7r9%231?Nr7%4331Ap031p071p0F1p0O1p0Q31pU0Q91pSLQ:1pQ2Q<1pQDQ@1pQBQA1").
Proof. intros M M' F a v. intros HF Ha H8 Ho Hu. unfold u64_at. rewrite (rdn_frame M M' F HF 8%nat a Ha ltac:(cbn; lia)). exact Hu. intros i Hi; apply Ho; cbn in Hi; lia. Qed.
Lemma u8_at_frame : ltac2:(TCodec.tc2 tcn__L5Defs "Q>'R=yR0%211'8y8%511%311p051'5&Q6%211'?&Q2r3r5r4%43321&QFz%2216&QD+1%2271&QK+2+R0%3221%:251&Q5r6%221@&Q8r9%2314Cr7%43316p031p071p0;1p0D1p0H1pT0N1pSLO1pQ2Q11pQDQ51pQBQ61").
Proof. intros M M' F a b. intros HF Ha H1 Ho Hu. unfold u8_at. rewrite (rdn_frame M M' F HF 1%nat a Ha ltac:(cbn; lia)). exact Hu. intros i Hi; cbn in Hi. replace i with a by lia. exact Ho. Qed.
Lemma limbs_at_frame : ltac2:(TCodec.tc2 tcn__L5Defs "R3'R=yR0%211'8y8%511%311p051'5&Q6%211'?%411&Q2r3r5r4%43321&QFz%2216&QD&QI+8&QJ&4%12?<%311%6251%82=1&QK+2+R0%3221%@251';r6r1%D221&QG%?2MI%A11%D2C1%F271%5271%:271&Q5r8r2%3221p051pT8Q81&Q4r9%231BQ7r7%4331Dp031p071p0I1p0Q81p0Q<1pU2QB1pTFQD1pQ2QF1pQDQJ1pQBQK1").
Proof. intros M M' F q ws. intros HF Hq Hh Ho HL i Hi. eapply u64_at_frame. exact HF. lia. lia. intros j Hj; apply Ho; lia. apply HL; exact Hi. Qed.
Lemma defined_grows : ltac2:(TCodec.tc2 tcn__L5Defs "H'R=yR0%211'8y8%511%311p051'?&QAr4r3%3221&Q1r5r2%33251%43376p021p071pT><1pSL=1pQD?1pQB@1").
Proof. intros M M' a n. intros G D i Hi. apply G. apply D. exact Hi. Qed.
Lemma writable_grows : ltac2:(TCodec.tc2 tcn__L5Defs "H'R=yR0%211'8y8%511%311p051'?&QAr4r3%3221&Q9r5r2%33251%43376p021p071pT><1pSL=1pQD?1pQB@1").
Proof. intros M M' a n. intros G W d k Hd Hk. eapply store_ok_mono. exact G. apply W; assumption. Qed.
Lemma writable_sub : ltac2:(TCodec.tc2 tcn__L5Defs "O'R=yR0%211'8y8%511%311p051'?&Q9r5r4r3%43321&QF%1253&QD%1265r6%3219%6231r8%=31<;p031p091p0<1pT@B1pSNC1pT>D1pSLE1pQBG1").
Proof. intros M a n a' n'. intros W H1 H2 d k Hd Hk. replace (a' + d) with (a + (a' - a + d)) by lia. apply W; lia. Qed.
Lemma defined_sub : ltac2:(TCodec.tc2 tcn__L5Defs "O'R=yR0%211'8y8%511%311p051'?&Q1r5r4r3%43321&QF%1253&QD%1265r6%3219%6231r8%=31<;p031p091p0<1pT@B1pSNC1pT>D1pSLE1pQBG1").
Proof. intros M a n a' n'. intros D H1 H2 i Hi. replace (a' + i) with (a + (a' - a + i)) by lia. apply D; lia. Qed.
Lemma regs_preserved_refl : ltac2:(TCodec.tc2 tcn__L5Defs ":&Gy5'R=yR0%211%5241&Q0r1%2211pQJ41").
Proof. intros R. intros r _; reflexivity. Qed.
Lemma regs_preserved_trans : ltac2:(TCodec.tc2 tcn__L5Defs "A&Gy5'R=yR0%211%5241&Q0r3r2%3221r5%5214p031p041pQN91pQL:1pQJ;1").
Proof. intros R R' R''. intros A B r Hr. rewrite (B r Hr). apply A. exact Hr. Qed.
Definition ra_ok (r : Z) : Prop := 0 <= r < 2 ^ 47 /\ r mod 2 = 0.
Inductive bstore : Type := BInl (v0 v1 : Z) | BDyn (cap : Z) (q : Z).
Record bigobj : Type := BO { bo_fb : Z; bo_len : nat; bo_st : bstore }.
Definition bo_dyn (b : bigobj) : bool := Z.testbit (bo_fb b) 0.
Definition bo_neg (b : bigobj) : bool := Z.testbit (bo_fb b) 1.
Definition bo_cap (b : bigobj) : Z := match bo_st b with BInl _ _ => 2 | BDyn c _ => c end.
Definition bo_data (o : Z) (b : bigobj) : Z := match bo_st b with BInl _ _ => o + 16 | BDyn _ q => q end.
Definition big_at (M : word -> option byte) (o : Z) (b : bigobj) : Prop :=
u8_at M o (bo_fb b) /\ 0 <= bo_fb b < 256 /\
u64_at M (o + 8) (Z.of_nat (bo_len b)) /\
match bo_st b with
| BInl v0 v1 => Z.testbit (bo_fb b) 0 = false /\ u64_at M (o + 16) v0 /\ u64_at M (o + 24) v1 /\ (bo_len b <= 2)%nat
/\ 0 <= v0 < 2 ^ 64 /\ 0 <= v1 < 2 ^ 64
| BDyn cap q => Z.testbit (bo_fb b) 0 = true /\ u64_at M (o + 16) cap /\ u64_at M (o + 24) q
/\ Z.of_nat (bo_len b) <= cap /\ 1 <= cap <= 2 ^ 27 /\ q mod 8 = 0 /\ 4096 <= q /\ q + 8 * cap <= 2 ^ 47
/\ hull_apart q (8 * cap)
end.
Definition bo_with_len (b : bigobj) (n : nat) : bigobj := BO (bo_fb b) n (bo_st b).
Definition bo_with_fb (b : bigobj) (fb : Z) : bigobj := BO fb (bo_len b) (bo_st b).
Lemma fb_dyn_nonneg : ltac2:(TCodec.tc2 tcn__L5Defs "N'?';&QFzr1%3221&QG+X0%2241%8241&>'<&QHr2+4%3221+1%63A21'2&QL%127A(:%;3421%42:7(3%>3721%I241%A2:1p0C1pT2M1").
Proof. intros fb.
intros Hfb.
replace (Z.testbit fb 1) with (Z.testbit (fb / 2) 0) by (rewrite (Z.div2_bits fb 0) by lia; reflexivity).
rewrite !Z.bit0_odd.
pose proof (Zmod_odd fb) as M1. pose proof (Zmod_odd (fb / 2)) as M2.
pose proof (Z.div_mod fb 2 ltac:(lia)) as D1. pose proof (Z.div_mod (fb / 2) 2 ltac:(lia)) as D2.
pose proof (Z.mod_pos_bound fb 2 ltac:(lia)) as B1. pose proof (Z.mod_pos_bound (fb / 2) 2 ltac:(lia)) as B2.
assert (E4: fb mod 4 = 2 * ((fb / 2) mod 2) + fb mod 2).
{ symmetry. apply (Zmod_unique fb 4 ((fb / 2) / 2)). lia. lia. }
rewrite E4. destruct (Z.odd fb), (Z.odd (fb / 2)); split; intros H; try lia; destruct H; try discriminate; lia.
Qed.
Lemma land253_nonneg : ltac2:(TCodec.tc2 tcn__L5Defs "J'?';&QFzr1%3221&QG+X0%2241%8241'<'2&QLr2+1%3221(3%73621&QEr3+WM%3221%<3F13p061p0?1pT2I1").
Proof. intros fb.
intros Hfb B1. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec.
destruct (Z.eq_dec i 1) as [->|Hi1]. { rewrite B1. reflexivity. }
destruct (Z_lt_le_dec i 8) as [Hlt|Hge].
- replace (Z.testbit 253 i) with true. apply Bool.andb_true_r.
assert (Hc : i = 0 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7) by lia.
destruct Hc as [->|[->|[->|[->|[->|[->| ->]]]]]]; reflexivity.
- assert (Z.testbit fb i = false) as ->.
{ apply Z.testbit_false. lia. rewrite Z.div_small. reflexivity. split. lia.
apply Z.lt_le_trans with (2 ^ 8). lia. apply Z.pow_le_mono_r; lia. }
reflexivity.
Qed.
Lemma land_byte_range : ltac2:(TCodec.tc2 tcn__L5Defs "D'?';&QFzr1%3221&QG+X0%2241%8241&QEr3r2%3221%<2;1%9228%?221p081pT:B1pSLC1").
Proof. intros a m.
intros Hm. replace m with (Z.land m (Z.ones 8)) by (rewrite Z.land_ones, Z.mod_small; lia).
rewrite Z.land_assoc. rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia.
Qed.
Fixpoint limbs_val (ws : list Z) : Z := match ws with [] => 0 | w :: r => w + 2 ^ 64 * limbs_val r end.
Definition lstr_short (M : word -> option byte) (o : Z) (s : list Z) : Prop :=
(length s <= 22)%nat /\ u8_at M o (2 * Z.of_nat (length s)) /\ bytes_at M (o + 1) s /\ u8_at M (o + 1 + Z.of_nat (length s)) 0.
Definition lstr_long (M : word -> option byte) (o : Z) (s : list Z) (w0 p : Z) : Prop :=
Z.testbit w0 0 = true /\ u64_at M o w0 /\ u64_at M (o + 8) (Z.of_nat (length s)) /\ u64_at M (o + 16) p /\
bytes_at M p s /\ u8_at M (p + Z.of_nat (length s)) 0.
Context {SCFG_P : ScfgP}.
Lemma cps_of_msteps : ltac2:(TCodec.tc2 tcn__L5Defs "R;'Q;&Gy5'R=yR0%211%5241'8y8%611%311p061'D&Q?'<%81:&Er2%211(0%11?%73631'5'9%12CC%311&Fr3%211(7%116%A3631'OvR;&Q<r<r:r9r8&Q>%117%7565431r;r7r6r5%<543216%?3>61'Q@&Q:vQB%211(C%C5B?:9=%2219r4%84G521r>%H51G@FB%721?%<4K91?p051p0?1p0Q01p0Q;1pQ6QD1pT<QF1pQDQH1pTDQO1pQLQO1pQBQK1pTBR21pQJR21pT6R91pT4R:1").
Proof. intros fx fx' R pc M R' pc' M' model K. intros Hh Hl Hms Hk. eapply srz_msteps; eauto. Qed.
Lemma run_cps : ltac2:(TCodec.tc2 tcn__L5Defs "RM'Q;&Gy5'R=yR0%211%5241'8y8%611%311p061!p021p081p0?1'D&Q?'<%<1>&Er2%211(0%11C%73631'5'9%12GG%311&Fr3%211(7%116%A3631'=';'OvR;&Q<r<r;r:r9&Q>%117%7565431r8r1%:5CM214%=3<41r=%13FQ04%A231qQDQ<1%D2Q=1qQLQC1%F2QD1qT6QK1%H2QL1r>%13OQ9='Q@&Q:vQB%211(Cr4%M51Q6JQ@G%321J%84Q051Gp0:1pQDQN1pQLR41pT6R;1%Q45Q2Q1Q0LNr6%;221r5%A4Q9>21p061p0F1p0Q@1p0QK1pQ6R41pT<R61pTDRB1pQBR=1pTBRD1pQJRD1pT4RK1pQHR=1").
Proof. intros Q fx R pc M pc' model K. intros Hh Hl (fx' & R' & M' & Hms & HQ) HK. eapply cps_of_msteps; eauto. Qed.
End WithSegs.
End L5.

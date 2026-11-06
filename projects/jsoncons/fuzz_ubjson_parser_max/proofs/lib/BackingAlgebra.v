(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Monad Specs Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import AsanCeil.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__BackingAlgebra () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Nat."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.Run."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap."; "LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mprotect."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanCeil."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.BackingAlgebra."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A"; "0C"; "0C1"; "0C2"; "1andb"; "1app"; "1bool"; "1cons"; "1false"; "1length"; "1list"; "1nat"; "1negb"; "1nil"; "1orb"; "1pair"]; ["1prod"; "1true"; "2and"; "2eq"; "2or"; "3add"; "4Z"; "5valid_sp"; "6Model"; "6ProcInput"; "6VmMaps"; "6init_model"; "6iv_subtract"; "6lazy_interior"; "6live_bytes"; "6m_vm_lazy"]; ["6m_vm_materialized"; "6m_vmmaps"; "6maps_subtract"; "6maps_subtract_all"; "6page_outside_range"; "6page_size"; "6region_free"; "6vm_add_lazy"; "6vm_backing_used"; "6vm_forget_range"; "6vm_init_sp"; "6vm_limit"; "6vm_maps"; "6vm_noaccess"; "6with_vm_backing"; "6with_vmmaps"]; ["7mmap_fixed_rw_budget_ok"; "7mmap_noreserve_b"; "7with_mmap_backing"; "7with_mmap_replacement"; "8mprotect_budget_ok"; "0P"; "0Q"; "9init_sp_ok"; ":B"; ":S"; ":covered"; ":in_iv"; ":in_rng"; ":iv_count"; ":iv_wf"; ":ivs_wf"]; [":model_ivs_wf"; ":overlap_sum"; ":sum_count"; ":zcount"; ";In"; ";filter"; "<add"; "<le"; "<lt"; "<modulo"; "<mul"; "<of_nat"; "<pow"; "<sub"; "<to_nat"; "0Z_"]; ["0a"; "0addr"; "0brk0"; "0f"; "0flags"; "0h"; "0h'"; "0hi"; "0inp"; "0l"; "0l1"; "0l2"; "0lim"; "0lo"; "0m"; "0mbase"]; ["0n"; "0n1"; "0n2"; "0p"; "0q"; "0reserved"; "0sp"; "=Z_to_bv"; "=bv"; "=bv_unsigned"; "0sz"; "0x"; "0z"]]).
Fixpoint zcount (P : Z -> bool) (lo : Z) (n : nat) : Z :=
match n with
| O => 0
| S k => (if P lo then 1 else 0) + zcount P (lo + 1) k
end.
Lemma zcount_nonneg : ltac2:(TCodec.tc2 tcn__BackingAlgebra "?'F'6p021';&R7z&R3r3r2r1%43321%7261pV291pUL=1pS<<1").
Proof. intros P lo n. revert lo. induction n; intros lo; cbn; [lia|]. destruct (P lo); specialize (IHn (lo+1)); lia. Qed.
Lemma zcount_le_len : ltac2:(TCodec.tc2 tcn__BackingAlgebra "@'F'6p021';&R7&R3r3r2r1%43321&R;%113%8231pV2:1pUL>1pS<=1").
Proof.
intros P lo n. revert lo. induction n; intros lo; [cbn; lia|].
cbn [zcount]. rewrite Nat2Z.inj_succ. destruct (P lo); specialize (IHn (lo+1)); lia.
Qed.
Lemma zcount_mono : ltac2:(TCodec.tc2 tcn__BackingAlgebra "Q6'F'6pVH21';'B&R7r3r1%3221&R8&R6&R;r2%211%4281%6281%<281'Cr6%117(A%43D21%41@%63F13p031p091pVHJ1&R3r5%231GAr4%431IC%K231p071pV2O1pULQ31pS>Q21pS<Q31").
Proof.
intros P Q lo n. revert lo. induction n; intros lo H; [cbn; lia|].
cbn [zcount]. rewrite Nat2Z.inj_succ in H.
assert (IH := IHn (lo + 1) ltac:(intros x Hx; apply H; lia)).
destruct (P lo) eqn:EP.
- rewrite (H lo ltac:(lia) EP). lia.
- destruct (Q lo); lia.
Qed.
Lemma zcount_ext : ltac2:(TCodec.tc2 tcn__BackingAlgebra "Q3'F'6pVH21';'B&R7r3r1%3221&R8&R6&R;r2%211%4281%6281%<281'Cr6%117r5%119%53E31p071pVHH1&R3%136D>r4%331F@%<3M31p061pV2L1pULQ01pS>O1pS<Q01").
Proof.
intros P Q lo n H.
pose proof (zcount_mono P Q lo n ltac:(intros x Hx HP; rewrite <- (H x Hx); exact HP)).
pose proof (zcount_mono Q P lo n ltac:(intros x Hx HQ; rewrite (H x Hx); exact HQ)). lia.
Qed.
Lemma zcount_or_le : ltac2:(TCodec.tc2 tcn__BackingAlgebra "J'F'6pVH21';&R7&R3&>r5r1%211r4%113%6231qVH=1r2%:3217&R6%<3739r3%>315;%4231%A261pV2C1pULG1pS>F1pS<G1").
Proof.
intros P Q lo n. revert lo. induction n; intros lo; [cbn; lia|].
cbn [zcount]. specialize (IHn (lo + 1)). destruct (P lo), (Q lo); cbn [orb]; lia.
Qed.
Lemma zcount_and_split : ltac2:(TCodec.tc2 tcn__BackingAlgebra "N'F'6p021pVH32';'C&R3r4r2r1%43321&R6&4r5%115%816%4221qVHA1%<31:9&<%115%9271qVHF1%A31?>%=261%D3I?1pV2F1pULK1pS>I1pS<K1").
Proof.
intros P Q lo n. revert lo. induction n; intros lo; [cbn; lia|].
cbn [zcount]. specialize (IHn (lo + 1)). destruct (P lo), (Q lo); cbn [andb negb]; lia.
Qed.
Lemma zcount_const_false : ltac2:(TCodec.tc2 tcn__BackingAlgebra "='F';'C&R3(8q051r2r1%53321z%83:21pV2:1pUL<1").
Proof. intros lo n. revert lo. induction n; intros; cbn; [lia|]. rewrite IHn. lia. Qed.
Lemma zcount_const_true : ltac2:(TCodec.tc2 tcn__BackingAlgebra ">'F';'C&R3(Aq051r2r1%53321&R;%113%93;31pV2;1pUL=1").
Proof. intros lo n. revert lo. induction n; intros; [cbn; lia|]. cbn [zcount]. rewrite Nat2Z.inj_succ, IHn. lia. Qed.
Lemma zcount_false : ltac2:(TCodec.tc2 tcn__BackingAlgebra "Q1'F'6pVH21';'B&R7r3r1%3221&R8&R6&R;r2%211%4281%6281%<281'Cr5%117(8%43D21p061pVHG1&R3r4%231D>z%;3L21p061pV2K1pULO1pS<N1").
Proof. intros P lo n H. rewrite (zcount_ext P (fun _ => false) lo n H). apply zcount_const_false. Qed.
Lemma zcount_true : ltac2:(TCodec.tc2 tcn__BackingAlgebra "Q0'F'6pVH21';'B&R7r3r1%3221&R8&R6&R;r2%211%4281%6281%<281'Cr5%117(A%43D21p061pVHG1&R3r4%231D>%:3K1>p051pV2J1pULN1pS<M1").
Proof. intros P lo n H. rewrite (zcount_ext P (fun _ => true) lo n H). apply zcount_const_true. Qed.
Lemma zcount_split : ltac2:(TCodec.tc2 tcn__BackingAlgebra "I'F'6p021';'C&R3r4r3&Er2r1%3221%73651&R6%93875&R;%117%42:1%=3<18%6251%@3D81pV6B1pV4C1pULG1pS<F1").
Proof.
intros P lo n1 n2. revert lo. induction n1; intros lo.
- cbn [zcount Nat.add]. rewrite Z.add_0_r. reflexivity.
- cbn [zcount Nat.add]. rewrite IHn1, Nat2Z.inj_succ.
replace (lo + 1 + Z.of_nat n1) with (lo + Z.succ (Z.of_nat n1)) by lia. lia.
Qed.
Definition B (p : word * word) : Z := bv_unsigned (fst p).
Definition S (p : word * word) : Z := bv_unsigned (snd p).
Definition in_rng (lo hi x : Z) : bool := (lo <=? x) && (x <? hi).
Definition in_iv (p : word * word) (x : Z) : bool := in_rng (B p) (B p + S p) x.
Definition covered (C : list (word * word)) (x : Z) : bool := existsb (fun c => in_iv c x) C.
Definition iv_count (P : Z -> bool) (p : word * word) : Z := zcount P (B p) (Z.to_nat (S p)).
Definition iv_wf (p : word * word) : Prop := B p + S p <= 2 ^ 64.
Lemma B_range : ltac2:(TCodec.tc2 tcn__BackingAlgebra "D'@'S8yR0%211%4211'B&R7z&QHr1%211%5241&R8&R<+2+R0%3221%5271%=271pV8?1").
Proof. intros p. unfold B. exact (bv_unsigned_in_range _ (fst p)). Qed.
Lemma S_range : ltac2:(TCodec.tc2 tcn__BackingAlgebra "D'@'S8yR0%211%4211'B&R7z&QIr1%211%5241&R8&R<+2+R0%3221%5271%=271pV8?1").
Proof. intros p. unfold S. exact (bv_unsigned_in_range _ (snd p)). Qed.
Lemma fg_lit : ltac2:(TCodec.tc2 tcn__BackingAlgebra "G'F'B&R7zr1%3221&R8&R<+2+R0%3221%5271%;271'C&S9yR0&S7r2%2231%5241%73D13p091pVJF1").
Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. exact Hz. Qed.
Lemma live_bytes_app : ltac2:(TCodec.tc2 tcn__BackingAlgebra "F':'@'S8yR0%211%4211%611'C'F&N&5r2r1%33821%511&R6%715%815%3221%<3;51pUH>1pUF?1").
Proof. induction l1 as [|[a s] l1 IH]; intros; cbn -[Z.add]; [lia|rewrite IH; lia]. Qed.
Lemma maps_subtract_app : ltac2:(TCodec.tc2 tcn__BackingAlgebra "I':'@'S8yR0%211%4211%611'F'C&Q2&5r4r3%33821r2r1%73321%83632%93643%93>21%<3>41pU@>1pUL?1pUHA1pUFB1").
Proof. induction l1 as [|[a s] l1 IH]; intros; cbn; [reflexivity|rewrite IH, app_assoc; reflexivity]. Qed.
Lemma maps_subtract_all_app : ltac2:(TCodec.tc2 tcn__BackingAlgebra "F':'@'S8yR0%211%4211%611'C&Q3&5r2r1%33721r3%6221%7252%8253%83<21%;3<41pUH=1pUF>1p4?1").
Proof.
induction C as [|[a n] C IH]; intros; cbn; [reflexivity|].
rewrite maps_subtract_app. apply IH.
Qed.
Lemma maps_subtract_all_nil_l : ltac2:(TCodec.tc2 tcn__BackingAlgebra "?':'@'S8yR0%211%4211%611'C&Q3(=%115r1%4221%63713p481").
Proof. induction C as [|[a n] C IH]; cbn; [reflexivity|exact IH]. Qed.
Lemma maps_subtract_all_cons_l : ltac2:(TCodec.tc2 tcn__BackingAlgebra "J'@'S8yR0%211%4211':%112'C&Q3(7r3r2%33821r1%6221&5(=%11=%93>81%;216%<297%63A21%?3@81p4A1pUDB1pV8E1").
Proof. intros. change (p :: l) with ([p] ++ l). apply maps_subtract_all_app. Qed.
Fixpoint sum_count (P : Z -> bool) (l : list (word * word)) : Z :=
match l with
| [] => 0
| q :: r => iv_count P q + sum_count P r
end.
Lemma sum_count_app : ltac2:(TCodec.tc2 tcn__BackingAlgebra "J'F'6p021':'@'S8yR0%211%4211%611'C&R2r3&5r2r1%33821%6251&R6%8275%9285%3221%<3F51pUH>1pUF?1pS<G1").
Proof. induction l1; intros; cbn -[Z.add]; [lia|rewrite IHl1; lia]. Qed.
Lemma sum_count_nonneg : ltac2:(TCodec.tc2 tcn__BackingAlgebra "C'F'6p021':'@'S8yR0%211%4211%611&R7z&R2r2r1%3221%6251pUD81pS<@1").
Proof. induction l; cbn -[Z.add]; [lia|]. pose proof (zcount_nonneg P (B a) (Z.to_nat (S a))). unfold iv_count. lia. Qed.
Lemma sum_count_mono : ltac2:(TCodec.tc2 tcn__BackingAlgebra "O'F'6pVH21':'@'S8yR0%211%4211%611'Cr4r1%211(A%53>21r2%611%83A14p041pVHD1&R7&R2%12<7r3%3219%5231p071pUDC1pS>K1pS<L1").
Proof.
intros P Q l H. induction l; cbn -[Z.add]; [lia|].
pose proof (zcount_mono P Q (B a) (Z.to_nat (S a)) ltac:(intros; auto)). unfold iv_count. lia.
Qed.
Lemma sum_count_ext : ltac2:(TCodec.tc2 tcn__BackingAlgebra "K'F'6pVH21':'@'S8yR0%211%4211%611'Cr4r1%211r3%113%63?31pVHA1&R2r2%2291%3272%<3F21p061pUD?1pS>G1pS<H1").
Proof.
intros P Q l H. induction l; cbn -[Z.add]; [lia|].
unfold iv_count. rewrite (zcount_ext P Q) by (intros; apply H). lia.
Qed.
Lemma sum_count_or_le : ltac2:(TCodec.tc2 tcn__BackingAlgebra "N'F'6pVH21':'@'S8yR0%211%4211%611&R7&R2&>r4r1%211r3%113%6231qVHC1%9216&R6%;268r2%=21:%4231%@261pUDB1pS>J1pS<K1").
Proof.
intros P Q l. induction l; cbn -[Z.add]; [lia|].
pose proof (zcount_or_le P Q (B a) (Z.to_nat (S a))). unfold iv_count in *. lia.
Qed.
Lemma live_bytes_sum_count : ltac2:(TCodec.tc2 tcn__BackingAlgebra "B':'@'S8yR0%211%4211%611'C'F&Nr1%211&R2(Aq061%3215%93851pUD;1").
Proof.
induction l as [|[b s] l IH]; cbn -[Z.add]; [lia|].
unfold iv_count, B, S. cbn [fst snd]. rewrite zcount_const_true, IH.
pose proof (bv_unsigned_in_range 64 s). rewrite Z2Nat.id by lia. reflexivity.
Qed.
Definition ivs_wf (l : list (word * word)) : Prop := forall q, In q l -> iv_wf q.
Lemma ivs_wf_nil : ltac2:(TCodec.tc2 tcn__BackingAlgebra "9&QO(='@'S8yR0%211%4211%611%811").
Proof. intros q []. Qed.
Lemma ivs_wf_cons : ltac2:(TCodec.tc2 tcn__BackingAlgebra "E'@'S8yR0%211%4211':%112&QNr2%211&QO%113(7r4r3%33;21%611p061p091pUD=1pV8@1").
Proof. intros p l Hp Hl q [<-|Hq]; auto. Qed.
Lemma ivs_wf_cons_inv : ltac2:(TCodec.tc2 tcn__BackingAlgebra "F'@'S8yR0%211%4211':%112&QO(7r2r1%33721%511'B&QNr3%211%:18%5221p071pUD>1pV8A1").
Proof. intros p l H. split; [apply H; now left|intros q Hq; apply H; now right]. Qed.
Lemma ivs_wf_app : ltac2:(TCodec.tc2 tcn__BackingAlgebra "C':'@'S8yR0%211%4211%611&QOr2%211&5r4r3%33821%711p061p071pUH;1pUF<1").
Proof. intros l1 l2 H1 H2 q Hq. apply in_app_iff in Hq as [Hq|Hq]; auto. Qed.
Lemma ivs_wf_app_inv : ltac2:(TCodec.tc2 tcn__BackingAlgebra "E':'@'S8yR0%211%4211%611&QO&5r2r1%33621%511'Br3%811%917%4221p061pUH=1pUF>1").
Proof. intros l1 l2 H. split; intros q Hq; apply H; apply in_app_iff; auto. Qed.
Lemma ivs_wf_filter : ltac2:(TCodec.tc2 tcn__BackingAlgebra "D'@'S8yR0%211%4211'6p021':%114&QOr1%211&R5r3r2%33;21%711p061pUD:1pU8=1").
Proof. intros f l H q Hq. apply filter_In in Hq as [Hq _]. auto. Qed.
Lemma iv_wf_intro : ltac2:(TCodec.tc2 tcn__BackingAlgebra "H'S8yR0%211&R7&R6&S9r2%2261r1%4281%6231&R<+2+R0%3221%<251&QN(?r3%24AA1=%411p061pV2D1pU2E1").
Proof. intros a n H. exact H. Qed.
Ltac in_rng_tf :=
intros x Hx; unfold in_rng;
first [ rewrite (proj2 (Z.leb_gt _ _)) by lia; cbn [andb negb]; first [reflexivity | rewrite ?andb_true_r; reflexivity]
| rewrite (proj2 (Z.leb_le _ _)) by lia; rewrite (proj2 (Z.ltb_ge _ _)) by lia; cbn [andb negb]; first [reflexivity | rewrite ?andb_true_r, ?andb_false_r; reflexivity]
| rewrite (proj2 (Z.leb_le _ _)) by lia; rewrite (proj2 (Z.ltb_lt _ _)) by lia; cbn [andb negb]; first [reflexivity | rewrite ?andb_true_r, ?andb_false_r; reflexivity] ].
Lemma count_outside_gen : forall P lo hi A Z_,
0 <= Z_ -> lo <= hi ->
zcount (fun x => P x && negb (in_rng lo hi x)) A (Z.to_nat Z_)
= (if A <? lo then zcount P A (Z.to_nat (Z.min Z_ (lo - A))) else 0)
+ (if hi <? A + Z_ then zcount P (Z.max A hi) (Z.to_nat (A + Z_ - Z.max A hi)) else 0).
Proof.
intros P lo hi A Z_ HZ Hlh.
destruct (A <? lo) eqn:El; destruct (hi <? A + Z_) eqn:Er;
rewrite ?Z.ltb_lt, ?Z.ltb_ge in El, Er.
- destruct (Z.le_gt_cases (lo - A) Z_) as [H1|H1]; [|lia].
replace (Z.to_nat Z_) with (Z.to_nat (lo - A) + (Z.to_nat (hi - lo) + Z.to_nat (A + Z_ - hi)))%nat by lia.
rewrite !zcount_split.
rewrite (zcount_ext _ P A) by in_rng_tf.
rewrite (zcount_false _ (A + _)) by in_rng_tf.
rewrite (zcount_ext _ P (A + _ + _)) by in_rng_tf.
rewrite (Z.min_r Z_ (lo - A) H1), (Z.max_r A hi) by lia.
rewrite !Z2Nat.id by lia.
replace (A + (lo - A) + (hi - lo)) with hi by lia.
replace (A + Z_ - hi) with (A + Z_ - hi) by lia. lia.
- destruct (Z.le_gt_cases (A + Z_) lo) as [H1|H1].
+ rewrite (zcount_ext _ P) by in_rng_tf. rewrite (Z.min_l Z_ (lo - A)) by lia. lia.
+ replace (Z.to_nat Z_) with (Z.to_nat (lo - A) + Z.to_nat (A + Z_ - lo))%nat by lia.
rewrite zcount_split.
rewrite (zcount_ext _ P A) by in_rng_tf.
rewrite (zcount_false _ (A + _)) by in_rng_tf.
rewrite (Z.min_r Z_ (lo - A)) by lia. lia.
- destruct (Z.le_gt_cases hi A) as [H1|H1].
+ rewrite (zcount_ext _ P) by in_rng_tf. rewrite (Z.max_l A hi) by lia.
replace (A + Z_ - A) with Z_ by lia. lia.
+ replace (Z.to_nat Z_) with (Z.to_nat (hi - A) + Z.to_nat (A + Z_ - hi))%nat by lia.
rewrite zcount_split.
rewrite (zcount_false _ A) by in_rng_tf.
rewrite (zcount_ext _ P (A + _)) by in_rng_tf.
rewrite (Z.max_r A hi) by lia. rewrite !Z2Nat.id by lia.
replace (A + (hi - A)) with hi by lia. lia.
- rewrite zcount_false by in_rng_tf. lia.
Qed.
Lemma count_inside : ltac2:(TCodec.tc2 tcn__BackingAlgebra "I'F&R7zr1%3221r5r4%6221&R3&QLr6%2216&R>r3%211%73491&R=%12<7%A231p0<1p0@1pU0E1p2F1pU@G1pULH1").
Proof.
intros lo hi A Z_ HZ Hlh.
pose proof (zcount_and_split (fun _ => true) (in_rng lo hi) A (Z.to_nat Z_)) as Hsplit.
cbn [andb] in Hsplit. rewrite zcount_const_true, Z2Nat.id in Hsplit by lia.
rewrite (zcount_ext (fun x => negb (in_rng lo hi x)) (fun x => true && negb (in_rng lo hi x))) in Hsplit by reflexivity.
rewrite (count_outside_gen (fun _ => true) lo hi A Z_ HZ Hlh) in Hsplit.
rewrite !zcount_const_true in Hsplit.
rewrite (zcount_ext (fun x => in_rng lo hi x) (in_rng lo hi)) in Hsplit by reflexivity.
destruct (A <? lo) eqn:El; destruct (hi <? A + Z_) eqn:Er;
rewrite ?Z.ltb_lt, ?Z.ltb_ge in El, Er; rewrite ?Z2Nat.id in Hsplit by lia; lia.
Qed.
Lemma iv_subtract_sem : ltac2:(TCodec.tc2 tcn__BackingAlgebra "QN'S8yR0%211'F&QN(?r4r3%346621%511&R7r2%2251'B'@%12==&R4r1&Lr7r6r5%44321@%73861%D1=p021pV:;1'6p0I1'C&R2%12>9&QM&4%G1A&<&QL%13A@D%311%6251qVHQ51%Q44Q7Q7FE%:221%>3Q8<1pS<@1&QJ%12HM&QK%127O%=3LQ;Q0%?11%B231%G3I61pVHQB1%Q92:1%Q:2M1p0Q<1p0Q@1pU@QG1pULQH1pVFQJ1pU2QK1").
Proof.
intros a sz lo hi Hwf Hlh. unfold iv_wf, iv_count, B, S in *. cbn [fst snd] in *.
pose proof (bv_unsigned_in_range 64 a) as Ha. pose proof (bv_unsigned_in_range 64 sz) as Hs.
unfold bv_modulus in Ha, Hs.
set (A := bv_unsigned a) in *. set (Z_ := bv_unsigned sz) in *.
unfold iv_subtract. cbv zeta. fold A. fold Z_.
destruct (A <? lo) eqn:El; destruct (hi <? A + Z_) eqn:Er;
pose proof El as El'; pose proof Er as Er';
rewrite ?Z.ltb_lt, ?Z.ltb_ge in El', Er'; cbn [app].
-
assert (E1 : bv_unsigned (Z_to_bv 64 (Z.min Z_ (lo - A))) = Z.min Z_ (lo - A)) by (apply fg_lit; lia).
assert (E2 : bv_unsigned (Z_to_bv 64 (Z.max A hi)) = Z.max A hi) by (apply fg_lit; lia).
assert (E3 : bv_unsigned (Z_to_bv 64 (A + Z_ - Z.max A hi)) = A + Z_ - Z.max A hi) by (apply fg_lit; lia).
split; [|split].
+ intros q [<-|[<-|[]]]; cbn [fst snd]; rewrite ?E1, ?E2, ?E3; lia.
+ intros P. cbn [sum_count]. unfold iv_count, B, S. cbn [fst snd]. fold A. rewrite E1, E2, E3.
rewrite (count_outside_gen P lo hi A Z_) by lia. rewrite El, Er. lia.
+ intros x. unfold covered, in_iv, in_rng, B, S. cbn [existsb fst snd]. fold A. fold Z_. rewrite E1, E2, E3, orb_false_r.
apply Bool.eq_true_iff_eq.
rewrite orb_true_iff, !andb_true_iff, negb_true_iff, andb_false_iff, !Z.leb_le, !Z.ltb_lt, Z.leb_gt, Z.ltb_ge. lia.
-
assert (E1 : bv_unsigned (Z_to_bv 64 (Z.min Z_ (lo - A))) = Z.min Z_ (lo - A)) by (apply fg_lit; lia).
split; [|split].
+ intros q [<-|[]]; cbn [fst snd]; rewrite ?E1; lia.
+ intros P. cbn [sum_count]. unfold iv_count, B, S. cbn [fst snd]. fold A. rewrite E1.
rewrite (count_outside_gen P lo hi A Z_) by lia. rewrite El, Er. lia.
+ intros x. unfold covered, in_iv, in_rng, B, S. cbn [existsb fst snd]. fold A. fold Z_. rewrite E1, orb_false_r.
apply Bool.eq_true_iff_eq.
rewrite !andb_true_iff, negb_true_iff, andb_false_iff, !Z.leb_le, !Z.ltb_lt, Z.leb_gt, Z.ltb_ge. lia.
-
assert (E2 : bv_unsigned (Z_to_bv 64 (Z.max A hi)) = Z.max A hi) by (apply fg_lit; lia).
assert (E3 : bv_unsigned (Z_to_bv 64 (A + Z_ - Z.max A hi)) = A + Z_ - Z.max A hi) by (apply fg_lit; lia).
split; [|split].
+ intros q [<-|[]]; cbn [fst snd]; rewrite ?E2, ?E3; lia.
+ intros P. cbn [sum_count]. unfold iv_count, B, S. cbn [fst snd]. rewrite E2, E3.
rewrite (count_outside_gen P lo hi A Z_) by lia. rewrite El, Er. lia.
+ intros x. unfold covered, in_iv, in_rng, B, S. cbn [existsb fst snd]. fold A. fold Z_. rewrite E2, E3, orb_false_r.
apply Bool.eq_true_iff_eq.
rewrite !andb_true_iff, negb_true_iff, andb_false_iff, !Z.leb_le, !Z.ltb_lt, Z.leb_gt, Z.ltb_ge. lia.
-
split; [|split].
+ intros q [].
+ intros P. cbn [sum_count]. unfold iv_count, B, S. cbn [fst snd].
rewrite (count_outside_gen P lo hi A Z_) by lia. rewrite El, Er. lia.
+ intros x. unfold covered, in_iv, in_rng, B, S. cbn [existsb fst snd]. fold A. fold Z_.
symmetry. apply andb_false_iff.
destruct (Z.lt_ge_cases x A); [left|]. { apply andb_false_iff. left. apply Z.leb_gt. lia. }
destruct (Z.lt_ge_cases x (A + Z_)); [right|left].
{ apply negb_false_iff. apply andb_true_iff. split; [apply Z.leb_le|apply Z.ltb_lt]; lia. }
apply andb_false_iff. right. apply Z.ltb_ge. lia.
Qed.
Lemma maps_subtract_sem : ltac2:(TCodec.tc2 tcn__BackingAlgebra "QF':'@'S8yR0%211%4211%611'F&QOr3%211&R7r2%2241'B&Q2r5r4%33219%;11'6p0>1'C&R2r1r6%;31:9%4231&4%A15&<&QL%137@8%311%6251qVHL1%=21;%?3N:1pS<A1&QJ%12>@%22@A%;3JIB%=11%@231%G3I51pVHQ71%Q1291%Q22M1p0Q41p0Q81pU@Q<1pULQ=1pUDQ?1").
Proof.
induction l as [|[a sz] l IH]; intros lo hi Hwf Hlh.
- cbn. split; [apply ivs_wf_nil|]. split; [reflexivity|]. intros; reflexivity.
- apply ivs_wf_cons_inv in Hwf as [Ha Hl].
destruct (IH lo hi Hl Hlh) as (W & Sm & Cv).
destruct (iv_subtract_sem a sz lo hi Ha Hlh) as (W1 & Sm1 & Cv1).
cbn [maps_subtract]. split; [|split].
+ apply ivs_wf_app; [intros q Hq; apply W1; exact Hq|exact W].
+ intros P. rewrite sum_count_app, Sm1, Sm. reflexivity.
+ intros x. unfold covered. rewrite existsb_app. fold (covered (iv_subtract a sz lo hi) x).
fold (covered (maps_subtract l lo hi) x). fold (covered l x). rewrite Cv1, Cv.
cbn [existsb]. fold (covered l x). destruct (in_iv (a, sz) x), (covered l x), (in_rng lo hi x); reflexivity.
Qed.
Lemma maps_subtract_wf : ltac2:(TCodec.tc2 tcn__BackingAlgebra "H':'@'S8yR0%211%4211%611'F&QOr3%211&R7r2%2241&Q2r5r4%33218%:11p061p0:1pU@>1pUL?1pUDA1").
Proof. intros. apply maps_subtract_sem; assumption. Qed.
Lemma covered_app : ltac2:(TCodec.tc2 tcn__BackingAlgebra "I':'@'S8yR0%211%4211%611'F'C'6&QJ&5r3r2%33921r1%6221&>%8263%9264%3221%=3<51pVH?1pUHA1pUFB1").
Proof. intros. unfold covered. apply existsb_app. Qed.
Lemma maps_subtract_all_app_cuts : ltac2:(TCodec.tc2 tcn__BackingAlgebra "E':'@'S8yR0%211%4211%611'C&Q3r3&5r2r1%33821%6251%7264%8214%:3;31p8<1p6=1pUD>1").
Proof. intros l C1; revert l; induction C1 as [|[a n] C1 IH]; intros; cbn; [reflexivity|apply IH]. Qed.
Theorem live_msa : ltac2:(TCodec.tc2 tcn__BackingAlgebra "Q1':'@'S8yR0%211%4211%611&QOr1%211'B'C'F&N&Q3r2r3%3221%511&R2&<&QJr4%221?%411qVH=1%721;%@3?91%E1;%C221p0E1pUDI1p4J1").
Proof.
induction C as [|[a n] C IH]; intros l Hwf.
- cbn [maps_subtract_all covered existsb negb]. split; [apply live_bytes_sum_count|exact Hwf].
- cbn [maps_subtract_all].
pose proof (bv_unsigned_in_range 64 n) as Hn.
destruct (maps_subtract_sem l (bv_unsigned a) (bv_unsigned a + bv_unsigned n) Hwf ltac:(lia)) as (W & Sm & Cv).
destruct (IH _ W) as [Hl Hw]. split; [|exact Hw].
rewrite Hl, Sm. apply sum_count_ext. intros x.
unfold covered at 2. cbn [existsb]. fold (covered C x). unfold in_iv, B, S. cbn [fst snd].
destruct (covered C x), (in_rng _ _ x); reflexivity.
Qed.
Lemma m_vmmaps_with_vmmaps : ltac2:(TCodec.tc2 tcn__BackingAlgebra "<'J'H'C&Q1&Q?r2r1%3221%511%73914pUN91pU<;1"). Proof. reflexivity. Qed.
Lemma m_vm_lazy_with_vmmaps : ltac2:(TCodec.tc2 tcn__BackingAlgebra "D'J'H'C':'@'S8yR0%211%4211%611&O&Q?r2r1%3221%511%613%?3821pUNA1pU<C1"). Proof. reflexivity. Qed.
Lemma m_vm_materialized_with_vmmaps : ltac2:(TCodec.tc2 tcn__BackingAlgebra "B'J'H'C':'S8yR0%211%411&Q0&Q?r2r1%3221%511%613%=3821pUN?1pU<A1").
Proof. reflexivity. Qed.
Lemma m_vmmaps_with_vm_backing : ltac2:(TCodec.tc2 tcn__BackingAlgebra "G':'@'S8yR0%211%4211%611%713'H'C'J&Q1&Q>r3r2r1%43321%611%713%:3921pUN<1pV8>1pUD@1"). Proof. reflexivity. Qed.
Lemma m_vm_lazy_with_vm_backing : ltac2:(TCodec.tc2 tcn__BackingAlgebra "E':'@'S8yR0%211%4211%611%713'H'C&O&Q>r3r2r1%43321%611%83;15pUN:1pV8<1pUD>1"). Proof. reflexivity. Qed.
Lemma m_vm_materialized_with_vm_backing : ltac2:(TCodec.tc2 tcn__BackingAlgebra "E':'@'S8yR0%211%4211%611%713'H'C&Q0&Q>r3r2r1%43321%611%83:14pUN:1pV8<1pUD>1").
Proof. reflexivity. Qed.
Lemma m_vmmaps_vm_forget_range : ltac2:(TCodec.tc2 tcn__BackingAlgebra "@'F'H'C'J&Q1&Q9r3r2r1%43321%611%713%:3921pUN<1pU@>1pUL?1"). Proof. reflexivity. Qed.
Lemma m_vm_lazy_vm_forget_range : ltac2:(TCodec.tc2 tcn__BackingAlgebra "H'F'H'C':'@'S8yR0%211%4211%611&O&Q9r3r2r1%43321%611&Q2%814%23176%B3;41pUND1pU@F1pULG1"). Proof. reflexivity. Qed.
Lemma m_vm_materialized_vm_forget_range : ltac2:(TCodec.tc2 tcn__BackingAlgebra "H'F'H'C':'S8yR0%211%411&Q0&Q9r3r2r1%43321%611&R5&Q4%1276%:16%43=21%B3=61pUND1pU@F1pULG1").
Proof. reflexivity. Qed.
Lemma m_vmmaps_vm_add_lazy : ltac2:(TCodec.tc2 tcn__BackingAlgebra "B'S8yR0%211'H'C'J&Q1&Q7r3r2r1%43321%611%713%:3921pUN<1pV2>1pU2?1"). Proof. reflexivity. Qed.
Lemma m_vm_lazy_vm_add_lazy : ltac2:(TCodec.tc2 tcn__BackingAlgebra "I'S8yR0%211'H'C':'@%1255%311&O&Q7r3r2r1%43321%611&5&M%1276%:16%43=21%A3=61pUNC1pV2E1pU2F1"). Proof. reflexivity. Qed.
Lemma m_vm_materialized_vm_add_lazy : ltac2:(TCodec.tc2 tcn__BackingAlgebra "C'S8yR0%211'H'C':%114&Q0&Q7r3r2r1%43321%611%713%;3921pUN=1pV2?1pU2@1"). Proof. reflexivity. Qed.
Ltac model_proj :=
rewrite ?m_vmmaps_vm_add_lazy, ?m_vm_lazy_vm_add_lazy, ?m_vm_materialized_vm_add_lazy,
?m_vmmaps_vm_forget_range, ?m_vm_lazy_vm_forget_range, ?m_vm_materialized_vm_forget_range,
?m_vmmaps_with_vmmaps, ?m_vm_lazy_with_vmmaps, ?m_vm_materialized_with_vmmaps.
Definition model_ivs_wf (m : Model) : Prop :=
ivs_wf (vm_maps (m_vmmaps m)) /\ ivs_wf (vm_noaccess (m_vmmaps m)) /\ ivs_wf (m_vm_lazy m)
/\ init_sp_ok (m_vmmaps m).
Definition overlap_sum (l : list (word * word)) (lo hi : Z) : Z := sum_count (in_rng lo hi) l.
Lemma overlap_sum_app : ltac2:(TCodec.tc2 tcn__BackingAlgebra "J':'@'S8yR0%211%4211%611'F'C&R1&5r4r3%33821r2r1%73321&R6%93743%:3754%3221%=3>51pU@?1pUL@1pUHB1pUFC1").
Proof. intros. apply sum_count_app. Qed.
Lemma overlap_sum_cons : ltac2:(TCodec.tc2 tcn__BackingAlgebra "M'@'S8yR0%211%4211':%112'F'C&R1(7r4r3%33921r2r1%73321&R6&QM&QL%1265%321:%=3:87%6221%@3A81pU@B1pULC1pUDE1pV8H1").
Proof. reflexivity. Qed.
Lemma overlap_sum_nil : ltac2:(TCodec.tc2 tcn__BackingAlgebra "A'F'C&R1(='@'S8yR0%211%4211%611r2r1%:3321z%=3>21pU@?1pUL@1").
Proof. reflexivity. Qed.
Lemma iv_count_in_rng_le : ltac2:(TCodec.tc2 tcn__BackingAlgebra "G'@'S8yR0%211%4211'F&R7r2r1%3221&QM&QLr3%2216r4%5221&R=%12:5%<231p0:1pU@?1pUL@1pV8B1").
Proof. intros p lo hi H. unfold iv_count. apply count_inside; [pose proof (S_range p); lia|exact H]. Qed.
Lemma iv_count_in_rng_disjoint : ltac2:(TCodec.tc2 tcn__BackingAlgebra "Q0'@'S8yR0%211%4211'F'D&R7&R6&QHr3%211&QI%113%6231r2%9221r1%;217%=231'C&QM&QL%12=8r4%4221z%73F21p091pU@H1pULI1pV8K1").
Proof.
intros p lo hi H. unfold iv_count. apply zcount_false. intros x Hx.
pose proof (S_range p). rewrite Z2Nat.id in Hx by lia.
unfold in_rng. apply andb_false_iff. destruct H; [left; apply Z.leb_gt | right; apply Z.ltb_ge]; lia.
Qed.
Lemma overlap_sum_region_free : ltac2:(TCodec.tc2 tcn__BackingAlgebra "O':'@'S8yR0%211%4211%611'C'6&Q6r3r2r1%43321(A%83721'F&R1r4&S9%12A:&R6%32C;%2231%73641z%C3:21p0<1pV2H1pULI1pUDH1").
Proof.
induction l as [|[b s] l IH]; intros lo n H; [reflexivity|].
cbn [region_free] in H. apply andb_true_iff in H as [H1 H2].
rewrite overlap_sum_cons, (IH _ _ H2), iv_count_in_rng_disjoint; [lia|].
apply negb_true_iff in H1. unfold iv_overlap in H1. unfold B, S. cbn [fst snd].
apply andb_false_iff in H1 as [H1|H1]; apply Z.ltb_ge in H1; lia.
Qed.
Lemma overlap_sum_single_le : ltac2:(TCodec.tc2 tcn__BackingAlgebra "I'@'S8yR0%211%4211'F&R7r2r1%3221&R1(7r4(=%11:%43;31r3%7321:&R=%12<3%>231p0<1pU@A1pULB1pV8D1").
Proof. intros. rewrite overlap_sum_cons, overlap_sum_nil. pose proof (iv_count_in_rng_le p lo hi H). lia. Qed.
Lemma vm_backing_used_sem_maps : ltac2:(TCodec.tc2 tcn__BackingAlgebra "QA'H&QO&Q<&Q1r1%211%411%611'C'F&Q8r2%211&R6&R2&<&QJ&5'@'S8yR0%211%4211&Q=r3%F11%311&O%114%<3731%>21J%@11qVHG1%N1F%Q011%E231&R:&R;&9&Q0%11M%32D1%511&Q5%8221%Q02:1%Q63Q5Q21p0Q81pUNQ@1").
Proof.
intros m Wm. unfold vm_backing_used, vm_backed_maps.
rewrite <- maps_subtract_all_app_cuts. rewrite (proj1 (live_msa _ _ Wm)). reflexivity.
Qed.
Lemma vm_backing_used_sem : ltac2:(TCodec.tc2 tcn__BackingAlgebra "Q?'H&R0r1%211'C'F&Q8r2%211&R6&R2&<&QJ&5'@'S8yR0%211%4211&Q=&Q1r3%211%411&O%114%=3831%?21I%A11qVHH1&Q<%;1H%211%G241&R:&R;&9&Q0%11O%32F1%511&Q5%8221%Q22:1%Q83Q7Q41p0Q:1pUNQ>1").
Proof. intros m (Wm & _). apply vm_backing_used_sem_maps; exact Wm. Qed.
Lemma filter_length_le {A} : forall (f : A -> bool) l, (length (List.filter f l) <= length l)%nat.
Proof. induction l; cbn; [lia|]. destruct (f a); cbn; lia. Qed.
Theorem backing_forget_commit_le : ltac2:(TCodec.tc2 tcn__BackingAlgebra "QI'H'J'F&R0r4%211&R7r3r2%3221'C':'@'S8yR0%211%4211%611&Q<r5%211&Q1r6%211%611%?3851&Q=%115&Q2r7%911%511%431=L%G3@61&Q8&Q9&Q?r8%2291%43AD1%611&R6%815&R1%G17%K11%331HK%6251%Q:281p0@1p0I1p0Q:1p0Q?1pU@QC1pULQD1pU>QF1pUNQH1").
Proof.
intros m h' lo hi Hwf Hlh Hmaps Hna.
pose proof Hwf as (Wm & Wn & Wl & _).
assert (Hwf' : ivs_wf (vm_maps (m_vmmaps (vm_forget_range lo hi (with_vmmaps h' m))))).
{ model_proj. rewrite Hmaps. exact Wm. }
rewrite (vm_backing_used_sem_maps _ Hwf'), (vm_backing_used_sem _ Hwf).
model_proj. rewrite Hmaps, Hna.
destruct (maps_subtract_sem _ lo hi Wn Hlh) as (_ & _ & Cn).
destruct (maps_subtract_sem _ lo hi Wl Hlh) as (_ & _ & Cl).
pose proof (filter_length_le (page_outside_range lo hi) (m_vm_materialized m)).
unfold overlap_sum.
eapply Z.le_trans.
{ apply Z.add_le_mono_r.
apply (sum_count_mono _ (fun x => negb (covered (vm_noaccess (m_vmmaps m) ++ m_vm_lazy m) x) || in_rng lo hi x)).
intros x. rewrite !covered_app, Cn, Cl.
destruct (covered (vm_noaccess (m_vmmaps m)) x), (covered (m_vm_lazy m) x), (in_rng lo hi x); cbn; congruence. }
pose proof (sum_count_or_le (fun x => negb (covered (vm_noaccess (m_vmmaps m) ++ m_vm_lazy m) x)) (in_rng lo hi)
(vm_maps (m_vmmaps m))).
unfold page_size in *. lia.
Qed.
Theorem backing_mprotect_le : ltac2:(TCodec.tc2 tcn__BackingAlgebra "QG'H'J'F&R0r4%211&R7r3r2%3221'C':'@'S8yR0%211%4211%611&Q<r5%211&Q1r6%211%611%?3851&Q=%115&Q2r7%911%511%431=L%G3@61&Q8&Q?r8%2281%411&R6%614&R1%E16%I11%331FI%6251%Q8281p0>1p0G1p0Q81p0Q=1pU@QA1pULQB1pU>QD1pUNQF1").
Proof.
intros m h' lo hi Hwf Hlh Hmaps Hna.
pose proof Hwf as (Wm & Wn & Wl & _).
assert (Hwf' : ivs_wf (vm_maps (m_vmmaps (with_vmmaps h' m)))).
{ model_proj. rewrite Hmaps. exact Wm. }
rewrite (vm_backing_used_sem_maps _ Hwf'), (vm_backing_used_sem _ Hwf).
model_proj. rewrite Hmaps, Hna.
destruct (maps_subtract_sem _ lo hi Wn Hlh) as (_ & _ & Cn).
unfold overlap_sum.
eapply Z.le_trans.
{ apply Z.add_le_mono_r.
apply (sum_count_mono _ (fun x => negb (covered (vm_noaccess (m_vmmaps m) ++ m_vm_lazy m) x) || in_rng lo hi x)).
intros x. rewrite !covered_app, Cn.
destruct (covered (vm_noaccess (m_vmmaps m)) x), (covered (m_vm_lazy m) x), (in_rng lo hi x); cbn; congruence. }
pose proof (sum_count_or_le (fun x => negb (covered (vm_noaccess (m_vmmaps m) ++ m_vm_lazy m) x)) (in_rng lo hi)
(vm_maps (m_vmmaps m))).
unfold page_size in *. lia.
Qed.
Lemma lazy_interior_aligned : ltac2:(TCodec.tc2 tcn__BackingAlgebra "QA'S8yR0%211'C'F&R9&S9r2%2271&Q5%5221z%93821&R8r3%92>1%3251&R7&R6r5%>2C1r4%@2E1%5231&R<+2+R0%3221%;251':'@%12MM%311&Mr6%221@(7(?%14Q4Q44C(=%119%53:31%Q73:71p0?1p0L1p0Q11p0Q21pV2Q=1pU2Q>1").
Proof.
intros a n Ha Hn Hpos Hwf. unfold lazy_interior, page_size in *.
pose proof (bv_unsigned_in_range 64 a) as Ra. pose proof (bv_unsigned_in_range 64 n) as Rn.
unfold bv_modulus in Ra, Rn.
pose proof (Z.div_mod (bv_unsigned a) 4096 ltac:(lia)) as Da.
pose proof (Z.div_mod (bv_unsigned n) 4096 ltac:(lia)) as Dn.
rewrite Ha in Da. rewrite Hn in Dn.
set (qa := bv_unsigned a / 4096) in *. set (qn := bv_unsigned n / 4096) in *.
assert (E1 : (bv_unsigned a + 4096 - 1) / 4096 * 4096 = bv_unsigned a).
{ rewrite Da. replace (4096 * qa + 0 + 4096 - 1) with (qa * 4096 + 4095) by lia.
rewrite Z.div_add_l by lia. change (4095 / 4096) with 0. lia. }
assert (E2 : (bv_unsigned a + bv_unsigned n) / 4096 * 4096 = bv_unsigned a + bv_unsigned n).
{ rewrite Da, Dn. replace (4096 * qa + 0 + (4096 * qn + 0)) with ((qa + qn) * 4096) by lia.
rewrite Z.div_mul by lia. lia. }
cbv zeta. rewrite E1, E2.
rewrite (proj2 (Z.ltb_lt _ _)) by lia.
f_equal. f_equal.
- apply bv_eq. rewrite fg_lit by lia. reflexivity.
- apply bv_eq. rewrite fg_lit by lia. lia.
Qed.
Theorem backing_recommit_lazy_le : ltac2:(TCodec.tc2 tcn__BackingAlgebra "RA'H'J'S8yR0%211&R0r4%211'C'F&R9&S9r3%22:1&Q5%5221z%93821&R8%82@=%2241&R7&R6r6%=2E1r5%?2G1%5231&R<+2+R0%3221%;251':'@%12OO%311&Q<r8%211&Q1r9%211%611%Q43851&Q=%115&Q2r:%911%511%Q82Q@=r7%Q:2QB1%Q0231%83541%Q@3D:1&Q8&Q7&Q9%QA2QIC%Q721:&Q?r;%22@1%63541%83IL1%:11%;15%Q@221p0>1p0K1p0Q81p0QE1p0QI1p0QJ1p0R51pV2R91pU2R:1pU>R>1pUNR@1").
Proof.
intros m h' a n Hwf Hal Hnl Hpos Hend Hmaps Hna.
pose proof Hwf as (Wm & Wn & Wl & _).
set (lo := bv_unsigned a) in *. set (hi := (lo + bv_unsigned n)%Z) in *.
assert (Hlh : lo <= hi) by (pose proof (bv_unsigned_in_range 64 n); lia).
pose proof (lazy_interior_aligned a n Hal Hnl Hpos Hend) as Hli.
assert (Hwf' : ivs_wf (vm_maps (m_vmmaps (vm_add_lazy a n (vm_forget_range lo hi (with_vmmaps h' m)))))).
{ model_proj. rewrite Hmaps. exact Wm. }
rewrite (vm_backing_used_sem_maps _ Hwf'), (vm_backing_used_sem _ Hwf).
model_proj. rewrite Hmaps, Hna, Hli.
destruct (maps_subtract_sem _ lo hi Wn Hlh) as (_ & _ & Cn).
destruct (maps_subtract_sem _ lo hi Wl Hlh) as (_ & _ & Cl).
pose proof (filter_length_le (page_outside_range lo hi) (m_vm_materialized m)).
apply Z.add_le_mono; [|unfold page_size; nia].
apply sum_count_mono. intros x Hx.
rewrite covered_app in Hx. rewrite covered_app in Hx. rewrite Cn, Cl in Hx. rewrite covered_app.
revert Hx. unfold covered at 2. cbn [existsb]. unfold in_iv, B, S. cbn [fst snd]. fold lo. fold hi.
destruct (covered (vm_noaccess (m_vmmaps m)) x), (covered (m_vm_lazy m) x), (in_rng lo hi x); cbn; congruence.
Qed.
Lemma vm_limit_with_vmmaps : ltac2:(TCodec.tc2 tcn__BackingAlgebra "@'J'H'C'F&Q;&Q1&Q?r2r1%3221%511%711%815%;3:21pUN=1pU<?1").
Proof. reflexivity. Qed.
Theorem mmap_fixed_rw_budget_ok_commit_intro : ltac2:(TCodec.tc2 tcn__BackingAlgebra "Q>'S8yR0%211'H'C'6&QAr4%211(8%63521&R0%115&R7&R6&Q8r5%211&R1&Q<&Q1%115%311&S9%12GAr3%32I1%=231%:3641%?2<1&Q;%11:%C231&Q@r7r6%3421DM(A%Q23Q121p071p0L1p0O1pV2Q81pU4Q91pUNQ91pU:Q;1").
Proof.
intros flags m addr n Hnr Hwf Hb.
unfold mmap_fixed_rw_budget_ok, vm_backing_within_limit, with_mmap_replacement, with_mmap_backing.
rewrite Hnr. apply Z.leb_le. model_proj. unfold mmap_fixed_rw_next. cbn [vm_limit].
pose proof (bv_unsigned_in_range 64 n).
pose proof (backing_forget_commit_le m (mmap_fixed_rw_next (m_vmmaps m) addr n)
(bv_unsigned addr) (bv_unsigned addr + bv_unsigned n) Hwf ltac:(lia) eq_refl eq_refl).
unfold mmap_fixed_rw_next in *. lia.
Qed.
Theorem mmap_fixed_rw_budget_ok_recommit_intro : ltac2:(TCodec.tc2 tcn__BackingAlgebra "QN'S8yR0%211'H'C'6&QAr4%211(A%63521&R0%115'F&R9&S9%12?9&Q5%4221z%@3721&R8r5%82F1%3251&R7&R6r7%=2K1r6%?2M1%5231&R<+2+R0%3221%;251&Q8r9%211&Q;&Q1%114%311%C251&Q@r;r:r8%4432;1%Q>3Q=1Q9p071p0@1p0M1p0Q21p0Q31p0Q<1p0Q?1pV2QH1pU4QI1pUNQI1pU:QK1").
Proof.
intros flags m addr n Hnr Hwf Hal Hnl Hpos Hend Hb.
unfold mmap_fixed_rw_budget_ok, vm_backing_within_limit, with_mmap_replacement, with_mmap_backing.
rewrite Hnr. apply Z.leb_le. model_proj. unfold mmap_fixed_rw_next. cbn [vm_limit].
pose proof (backing_recommit_lazy_le m (mmap_fixed_rw_next (m_vmmaps m) addr n) addr n
Hwf Hal Hnl Hpos Hend eq_refl eq_refl).
unfold mmap_fixed_rw_next in *. lia.
Qed.
Theorem mprotect_budget_ok_intro_gen : ltac2:(TCodec.tc2 tcn__BackingAlgebra "Q7'H'S8yR0%211&R0r3%211&R7&R6&Q8r4%211&R1&Q<&Q1%115%311&S9%12@=r2%32B1%=231%:3641%?2<1&Q;%11:%C231'C'6&QDr5%231EJ(A%63521p081p0M1pV2Q11pU4Q21pUNQ61").
Proof.
intros m addr n Hwf Hb.
unfold mprotect_budget_ok, vm_backing_within_limit, mprotect_model_next.
apply Z.leb_le. model_proj. cbn [vm_limit].
pose proof (bv_unsigned_in_range 64 n).
pose proof (backing_mprotect_le m
(mkVmMapsFull (vm_reserved (m_vmmaps m)) (vm_maps (m_vmmaps m))
(maps_subtract (vm_noaccess (m_vmmaps m)) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
(vm_start_brk (m_vmmaps m)) (vm_brk (m_vmmaps m)) (vm_limit (m_vmmaps m)) (vm_mmap_base (m_vmmaps m)) (vm_init_sp (m_vmmaps m)))
(bv_unsigned addr) (bv_unsigned addr + bv_unsigned n) Hwf ltac:(lia) eq_refl eq_refl) as Hle.
cbv zeta in Hle. lia.
Qed.
Lemma lazy_interior_wf : ltac2:(TCodec.tc2 tcn__BackingAlgebra "H'S8yR0%211&R7&R6&S9r2%2261r1%4281%6231&R<+2+R0%3221%<251&QO&Mr3%221=%411p061pV2D1pU2E1").
Proof.
intros a n H. unfold lazy_interior. cbv zeta.
pose proof (bv_unsigned_in_range 64 a) as Ra. pose proof (bv_unsigned_in_range 64 n) as Rn. unfold bv_modulus in Ra, Rn.
unfold page_size.
set (lo' := (bv_unsigned a + 4096 - 1) / 4096 * 4096). set (hi' := (bv_unsigned a + bv_unsigned n) / 4096 * 4096).
assert (Hhi : hi' <= bv_unsigned a + bv_unsigned n).
{ subst hi'. pose proof (Z.mul_div_le (bv_unsigned a + bv_unsigned n) 4096 ltac:(lia)). lia. }
assert (Hlo : 0 <= lo').
{ subst lo'. apply Z.mul_nonneg_nonneg; [apply Z.div_pos; lia|lia]. }
destruct (lo' <? hi') eqn:E; [|apply ivs_wf_nil].
apply Z.ltb_lt in E. apply ivs_wf_cons; [|apply ivs_wf_nil].
unfold iv_wf, B, S. cbn [fst snd]. rewrite !fg_lit by lia. lia.
Qed.
Lemma model_ivs_wf_intro : ltac2:(TCodec.tc2 tcn__BackingAlgebra "M'H&QO&Q<&Q1r1%211%411%611&Q=r2%711%311%;11&Or3%211%?11&QGr4%@11%311&R0r5%211p041p091p0>1p0D1pUNL1").
Proof. intros; repeat split; assumption. Qed.
Lemma model_ivs_wf_with_vmmaps : ltac2:(TCodec.tc2 tcn__BackingAlgebra "Q3'J'H&R0r1%211&QO&Q<r3%211%411&Q=r4%211%811'C'S8yR0%211&Q:r5%211&Q1%11;%511%:3741&Q?r6%2218%J11p051p0A1p0F1p0L1pUNQ01pU<Q21").
Proof. intros h m (_ & _ & Wl & Wsp) Hm Hn Hsp. unfold model_ivs_wf. model_proj. repeat split; try assumption. eapply init_sp_ok_same; eassumption. Qed.
Lemma model_ivs_wf_vm_forget_range : ltac2:(TCodec.tc2 tcn__BackingAlgebra "B'F'H&R7r3r2%3221&R0%113&Q9r5r4%33218%611p061p091pUN>1pU@@1pULA1").
Proof.
intros lo hi m Hlh (Wm & Wn & Wl & Wsp). unfold model_ivs_wf. model_proj.
repeat split; try assumption. apply maps_subtract_wf; assumption.
Qed.
Lemma model_ivs_wf_vm_add_lazy : ltac2:(TCodec.tc2 tcn__BackingAlgebra "M'S8yR0%211'H&R7&R6&S9r3%2271r2%4291%6231&R<+2+R0%3221%<251&R0%119&Q7r5r4%3321?%611p061p091pUNG1pV2I1pU2J1").
Proof.
intros a n m H (Wm & Wn & Wl & Wsp). unfold model_ivs_wf. model_proj.
repeat split; try assumption. apply ivs_wf_app; [apply lazy_interior_wf; exact H|exact Wl].
Qed.
Lemma model_ivs_wf_with_mmap_backing : ltac2:(TCodec.tc2 tcn__BackingAlgebra "O'S8yR0%211'H&R7&R6&S9r3%2271r2%4291%6231&R<+2+R0%3221%<251&R0%119&QBr6r5r4%44321@%711p071p0:1pUNH1pV2J1pU2K1pU:L1").
Proof.
intros flags a n m H Hwf. unfold with_mmap_backing.
destruct (mmap_noreserve_b flags); [apply model_ivs_wf_vm_add_lazy; assumption|exact Hwf].
Qed.
Lemma model_ivs_wf_with_mmap_replacement : ltac2:(TCodec.tc2 tcn__BackingAlgebra "O'S8yR0%211'H&R7&R6&S9r3%2271r2%4291%6231&R<+2+R0%3221%<251&R0%119&QCr6r5r4%44321@%711p071p0:1pUNH1pV2J1pU2K1pU:L1").
Proof.
intros flags a n m H Hwf. unfold with_mmap_replacement.
apply model_ivs_wf_with_mmap_backing; [exact H|].
apply model_ivs_wf_vm_forget_range; [pose proof (bv_unsigned_in_range 64 n); lia|exact Hwf].
Qed.
Lemma model_ivs_wf_init : ltac2:(TCodec.tc2 tcn__BackingAlgebra "L':'@'S8yR0%211%4211%611'F'I&Gr3%211&R0&Kr7r6r5r4r2%66543291%811p0:1pUB>1pUJ@1pV>D1pV0E1pU6F1pV<E1").
Proof. intros. repeat split; try (intros q Hq; cbn in Hq; contradiction). apply init_sp_ok_init_model; assumption. Qed.

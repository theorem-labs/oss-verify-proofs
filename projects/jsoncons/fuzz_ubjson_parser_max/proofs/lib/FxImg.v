(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PrimString PrimInt63.
From Stdlib Require Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec AxSymExec3 AxSymExec3B.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Import ListNotations.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__FxImg () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "Corelib.Numbers.Cyclic.Int63.PrimInt63."; "Corelib.Numbers.Cyclic.Int63.Uint63Axioms."; "Corelib.Strings.PrimString."; "LinuxProcessSemantics.LinuxProcessSem.MemImageType."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AxSymExec3.AX2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.FxImg.IMGF."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1Some"; "1bool"; "1list"; "1nat"; "1option"; "1option_map"; "1true"; "2and"; "2eq"; "2iff"; "3N"; "3Z"; "3Zpos"; "3positive"; "4int"; "4leb"]; ["4ltb"; "5to_Z"; "5to_Z_rec"; "5wB"; "6string"; "7Segment"; "7seg_base"; "7seg_bytes"; "7seg_readable"; "8find_segment"; "8hex_byte_at"; "8hex_nybble"; "8segment_byte_at"; "9img_bytes"; ":find_sgi"; ":hex_byte_atI"]; [":img_bytesFF"; ":img_bytesI"; ":img_goI"; ":mk_stab"; ":nybI"; ":p2i"; ":seg_byte_atI"; ":sg_lo"; ":sg_r"; ":sg_seg"; ":sgi"; ":sgi_ok"; ":z61"; ";Forall2"; "<add"; "<le"]; ["<leb"; "<lt"; "<ltb"; "<mul"; "<of_N"; "<of_nat"; "<pow"; "<sub"; "0a"; "0acc"; "0b"; "0c"; "0chunks"; "0e"; "0g"; "0i"]; ["0n"; "0o"; "0off"; "0p"; "0r"; "0s"; "0seg"; "0segs"; "0sh"; "=bv"; "=bv_unsigned"; "0t"; "0u"; "0x"; "0y"; "0z"]]).
Module IMGF.
Import AX2.
Local Notation "'φ' x" := (Uint63.to_Z x) (at level 0).
Local Open Scope Z_scope.
Fixpoint p2i (p : positive) (n : nat) (sh : int) (acc : int) {struct p} : option int :=
match p with
| xH => match n with O => None | S _ => Some (PrimInt63.add acc (PrimInt63.lsl 1%uint63 sh)) end
| xO q => match n with O => None | S m => p2i q m (PrimInt63.add sh 1%uint63) acc end
| xI q => match n with O => None | S m => p2i q m (PrimInt63.add sh 1%uint63) (PrimInt63.add acc (PrimInt63.lsl 1%uint63 sh)) end
end.
Definition z61 (z : Z) : option int :=
match z with
| Z0 => Some 0%uint63
| Zpos p => p2i p 61 0%uint63 0%uint63
| Zneg _ => None
end.
Lemma wB63 : ltac2:(TCodec.tc2 tcn__FxImg "8'8';&C&QF+2+QO%3221%73651"). Proof. reflexivity. Qed.
Lemma p2i_spec : ltac2:(TCodec.tc2 tcn__FxImg "QK'='3&>'8'4%113&Q5r5r4r3r2%544321(0r1%22<1%<3:41&Q?&Q>&A%11;&QE%11>%5231+QN%8221'7z%;218&QA&QF+2%=1H%3221%52>1%9271';&QC(<r8%211r6%G11%=2<1%7241%K2=1%Q:3:J1r7%K11%C2B1%E2:1%I251p0A1p0L1p0Q61pT:QD1pSDQE1pTBQF1pT2QH1pT8QJ1").
Proof.
induction p as [q IH|q IH|]; intros n sh acc r H Hs Ha; (destruct n as [|m]; [discriminate|]); cbn [p2i] in H;
pose proof (Uint63.to_Z_bounded sh) as Bs;
assert (E1 : φ (PrimInt63.lsl 1%uint63 sh) = 2 ^ φ sh)
by (rewrite Uint63.lsl_spec, wB63; change (φ 1%uint63) with 1; rewrite Z.mul_1_l; apply Z.mod_small;
split; [apply Z.pow_nonneg; lia|apply Z.pow_lt_mono_r; lia]);
assert (P1 : 2 ^ (φ sh + 1) = 2 ^ φ sh * 2) by (rewrite Z.pow_add_r by lia; lia);
assert (P62 : 2 ^ φ sh * 2 <= 2 ^ 62) by (rewrite <- P1; apply Z.pow_le_mono_r; lia);
assert (E2 : φ (PrimInt63.add acc (PrimInt63.lsl 1%uint63 sh)) = φ acc + 2 ^ φ sh)
by (rewrite Uint63.add_spec, E1, wB63; apply Z.mod_small; lia);
assert (E3 : φ (PrimInt63.add sh 1%uint63) = φ sh + 1)
by (rewrite Uint63.add_spec, wB63; change (φ 1%uint63) with 1; apply Z.mod_small; lia);
assert (PN : 2 ^ Z.of_nat (S m) = 2 * 2 ^ Z.of_nat m) by (rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia; reflexivity).
- apply IH in H; [|rewrite E3; lia|rewrite E2, E3, P1; lia].
destruct H as [H1 H2]. rewrite H1, E2, E3, P1, PN. split; [|lia]. change (Z.pos q~1) with (2 * Z.pos q + 1). generalize (2 ^ φ sh). intros X. clear. ring.
- apply IH in H; [|rewrite E3; lia|rewrite E3, P1; lia].
destruct H as [H1 H2]. rewrite H1, E3, P1, PN. split; [|lia]. change (Z.pos q~0) with (2 * Z.pos q). generalize (2 ^ φ sh). intros X. clear. ring.
- injection H as <-. rewrite E2, PN. split; [lia|]. pose proof (Z.pow_pos_nonneg 2 (Z.of_nat m) ltac:(lia) ltac:(lia)). lia.
Qed.
Lemma z61_spec : ltac2:(TCodec.tc2 tcn__FxImg "O';&>'8'4%113&Q<r2%211(0r1%2291%93741'7&A%118r3%>3@21&Q?z%2214&QA&QF+2+QM%3221%52:1%>271%?2;1p0A1pSBL1pU0N1").
Proof.
intros z a H. destruct z as [|p|p]; cbn [z61] in H; [injection H as <-; split; [reflexivity|lia]| |discriminate].
apply p2i_spec in H; [|change (φ 0%uint63) with 0; lia|change (φ 0%uint63) with 0; cbn; lia].
change (φ 0%uint63) with 0 in H. change (Z.of_nat 61) with 61 in H. destruct H as [H1 H2]. split; [rewrite H1; cbn; lia|lia].
Qed.
Definition nybI (c : int) : int :=
if (if PrimInt63.leb 48%uint63 c then PrimInt63.leb c 57%uint63 else false) then PrimInt63.sub c 48%uint63
else if (if PrimInt63.leb 97%uint63 c then PrimInt63.leb c 102%uint63 else false) then PrimInt63.sub c 87%uint63
else 16%uint63.
Definition hex_byte_atI (s : PrimString.string) (o : int) : option Z :=
let ci := PrimInt63.add o o in
let ci1 := PrimInt63.add ci 1%uint63 in
let s_len := PrimString.length s in
if (if PrimInt63.ltb ci1 s_len then true else PrimInt63.eqb ci1 (PrimInt63.sub s_len 1%uint63)) then
let h := nybI (PrimString.get s ci) in
let l := nybI (PrimString.get s ci1) in
if (if PrimInt63.ltb h 16%uint63 then PrimInt63.ltb l 16%uint63 else false)
then Some (Uint63Axioms.to_Z_rec 8 (PrimInt63.add (PrimInt63.lsl h 4%uint63) l))
else None
else None.
Fixpoint seg_byte_atI (chunks : list PrimString.string) (o : int) : option Z :=
match chunks with
| [] => None
| c :: rest =>
let cb := PrimInt63.lsr (PrimString.length c) 1%uint63 in
if PrimInt63.ltb o cb then hex_byte_atI c o else seg_byte_atI rest (PrimInt63.sub o cb)
end.
Fixpoint img_goI (chunks : list PrimString.string) (o : int) (n : nat) : option (list Z) :=
match n with
| O => Some []
| S n' => match seg_byte_atI chunks o with
| Some b => match img_goI chunks (PrimInt63.add o 1%uint63) n' with Some r => Some (b :: r) | None => None end
| None => None
end
end.
Record sgi : Type := SGI { sg_lo : int; sg_hi : int; sg_r : bool; sg_seg : Segment }.
Fixpoint mk_stab (segs : list Segment) : option (list sgi) :=
match segs with
| [] => Some []
| s :: r => match z61 (Z.of_N (seg_base s)), z61 (Z.of_N (seg_size s)), mk_stab r with
| Some b, Some z, Some t => Some (SGI b (PrimInt63.add b z) (seg_readable s) s :: t)
| _, _, _ => None
end
end.
Fixpoint find_sgi (t : list sgi) (a e : int) : option sgi :=
match t with
| [] => None
| g :: r => if (if PrimInt63.leb (sg_lo g) a then PrimInt63.leb e (sg_hi g) else false) then Some g
else if (if PrimInt63.leb (sg_hi g) a then true else PrimInt63.leb e (sg_lo g)) then find_sgi r a e
else None
end.
Definition img_bytesFF (ot : option (list sgi)) (segs : list Segment) (a : Z) (n : nat) : option (list Z) :=
match n with
| O => Some []
| S _ =>
match ot with
| Some t =>
match z61 a, z61 (Z.of_nat n) with
| Some a63, Some n63 =>
match find_sgi t a63 (PrimInt63.add a63 n63) with
| Some g => if sg_r g then img_goI (seg_bytes (sg_seg g)) (PrimInt63.sub a63 (sg_lo g)) n else None
| None => img_bytes segs a n
end
| _, _ => img_bytes segs a n
end
| None => img_bytes segs a n
end
end.
Definition img_bytesI (segs : list Segment) (a : Z) (n : nat) : option (list Z) := img_bytesFF (mk_stab segs) segs a n.
Lemma to_Z_rec_small : ltac2:(TCodec.tc2 tcn__FxImg "G'3&>&QA&Ar1%211&QF+2&QEr2%211%5241%:271'8';&Br3%2218%?19%63521p081pTLD1pT2F1").
Proof.
induction n as [|n IH]; intros x H.
- pose proof (Uint63.to_Z_bounded x). change (2 ^ Z.of_nat 0) with 1 in H. cbn [Uint63Axioms.to_Z_rec]. lia.
- cbn [Uint63Axioms.to_Z_rec].
assert (PN : 2 ^ Z.of_nat (S n) = 2 * 2 ^ Z.of_nat n) by (rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia; reflexivity).
pose proof (Uint63.to_Z_bounded x) as Bx.
assert (E : φ (PrimInt63.lsr x 1%uint63) = φ x / 2) by (rewrite Uint63.lsr_spec; reflexivity).
rewrite IH by (rewrite E; apply Z.div_lt_upper_bound; lia).
rewrite E. pose proof (Uint63.is_even_spec x) as Hev. pose proof (Z.div_mod (φ x) 2 ltac:(lia)) as DM.
destruct (Uint63Axioms.is_even x); [change (IntDef.Z.double (φ x / 2)) with (Z.double (φ x / 2)); rewrite Z.double_spec|change (IntDef.Z.succ_double (φ x / 2)) with (Z.succ_double (φ x / 2)); rewrite Z.succ_double_spec]; lia.
Qed.
Lemma leb_iff : ltac2:(TCodec.tc2 tcn__FxImg "B&>&9'8'1&?r2r1%3221(6%73621&Q?&A%117%217%4221%>261pTN@1pTLA1"). Proof. exact Uint63.leb_spec. Qed.
Lemma ltb_iff : ltac2:(TCodec.tc2 tcn__FxImg "B&>&9'8'1&@r2r1%3221(6%73621&QA&A%117%217%4221%>261pTN@1pTLA1"). Proof. exact Uint63.ltb_spec. Qed.
Lemma leb_b : ltac2:(TCodec.tc2 tcn__FxImg "?&>'8'1&?r2r1%3221&Q@&A%115%215%4221%;3:61pTN=1pTL>1").
Proof. intros. destruct (Z.leb_spec (φ x) (φ y)) as [H|H]; [apply leb_iff; exact H|]. destruct (PrimInt63.leb x y) eqn:E; [apply leb_iff in E; lia|reflexivity]. Qed.
Lemma ltb_b : ltac2:(TCodec.tc2 tcn__FxImg "?&>'8'1&@r2r1%3221&QB&A%115%215%4221%;3:61pTN=1pTL>1").
Proof. intros. destruct (Z.ltb_spec (φ x) (φ y)) as [H|H]; [apply ltb_iff; exact H|]. destruct (PrimInt63.ltb x y) eqn:E; [apply ltb_iff in E; lia|reflexivity]. Qed.
Lemma nybI_spec : ltac2:(TCodec.tc2 tcn__FxImg ">&>'8';&A&Q4r1%211%411&QD&K%115%311%;3:51pSH=1").
Proof.
intros c. unfold nybI, hex_nybble. pose proof (Uint63.to_Z_bounded c) as Bc. rewrite wB63 in Bc.
change (Uint63.leb 48 c) with (PrimInt63.leb 48%uint63 c). change (Uint63.leb c 57) with (PrimInt63.leb c 57%uint63).
change (Uint63.leb 97 c) with (PrimInt63.leb 97%uint63 c). change (Uint63.leb c 102) with (PrimInt63.leb c 102%uint63).
rewrite !leb_b. change (φ 48%uint63) with 48. change (φ 57%uint63) with 57. change (φ 97%uint63) with 97. change (φ 102%uint63) with 102.
destruct (Z.leb_spec 48 (φ c)) as [H1|H1]; cbn [andb].
- destruct (Z.leb_spec (φ c) 57) as [H2|H2].
+ rewrite Uint63.sub_spec, wB63. change (φ 48%uint63) with 48. rewrite Z.mod_small by lia. rewrite Z2N.id by lia. reflexivity.
+ destruct (Z.leb_spec 97 (φ c)) as [H3|H3]; cbn [andb]; [|reflexivity].
destruct (Z.leb_spec (φ c) 102) as [H4|H4]; [|reflexivity].
rewrite Uint63.sub_spec, wB63. change (φ 87%uint63) with 87. rewrite Z.mod_small by lia. rewrite Z2N.id by lia. reflexivity.
- destruct (Z.leb_spec 97 (φ c)) as [H3|H3]; [lia|]. reflexivity.
Qed.
Lemma nybI_le : ltac2:(TCodec.tc2 tcn__FxImg ">&>'7&Q?z&A&Q4r1%211%411%7261+@%9231%;231pSH=1").
Proof.
intros c. rewrite nybI_spec. unfold hex_nybble. pose proof (Uint63.to_Z_bounded c) as Bc.
destruct (Uint63.leb 48 c && Uint63.leb c 57)%bool eqn:E1.
- apply andb_prop in E1. destruct E1 as [A B]. apply Uint63.leb_spec in A, B. change (φ 48%uint63) with 48 in A. change (φ 57%uint63) with 57 in B. rewrite Z2N.id by lia. lia.
- destruct (Uint63.leb 97 c && Uint63.leb c 102)%bool eqn:E2; [|cbn; lia].
apply andb_prop in E2. destruct E2 as [A B]. apply Uint63.leb_spec in A, B. change (φ 97%uint63) with 97 in A. change (φ 102%uint63) with 102 in B. rewrite Z2N.id by lia. lia.
Qed.
Lemma hex_byte_atI_spec : ltac2:(TCodec.tc2 tcn__FxImg "Q:&D&>':'8';&Ar2%211&QDr1%211%83741&QA%517&QF+2+QN%3221%6251'4%11@&Or5r4%3221&5'R9y8%211&R:%123EqSF31&Jr3%22<1%:47O41%Q13@<1p0C1p0K1pT0Q51pT4Q71pT<Q91").
Proof.
intros s o i Ho Hi. unfold hex_byte_atI, hex_byte_at. cbv zeta.
assert (E0 : PrimInt63.add o o = Uint63.of_Z (Z.of_N (2 * i))).
{ apply Uint63.to_Z_inj. rewrite Uint63.add_spec, Uint63.of_Z_spec, Ho, wB63. f_equal. lia. }
assert (E1 : PrimInt63.add (PrimInt63.add o o) 1%uint63 = Uint63.of_Z (Z.of_N (2 * i + 1))).
{ apply Uint63.to_Z_inj. rewrite E0, Uint63.add_spec, !Uint63.of_Z_spec, wB63. change (φ 1%uint63) with 1.
rewrite Zplus_mod_idemp_l. f_equal. lia. }
rewrite E1, E0.
set (ci := Uint63.of_Z (Z.of_N (2 * i))). set (ci1 := Uint63.of_Z (Z.of_N (2 * i + 1))).
destruct (PrimInt63.ltb ci1 (PrimString.length s)) eqn:EL; cbn [orb].
2: destruct (PrimInt63.eqb ci1 (PrimInt63.sub (PrimString.length s) 1%uint63)); [|reflexivity].
all: pose proof (nybI_spec (get s ci)) as Sh; pose proof (nybI_spec (get s ci1)) as Sl;
pose proof (nybI_le (get s ci)) as Bh; pose proof (nybI_le (get s ci1)) as Bl;
set (h := hex_nybble (get s ci)) in *; set (l := hex_nybble (get s ci1)) in *;
rewrite !ltb_b; change (φ 16%uint63) with 16; rewrite Sh, Sl;
replace (N.ltb h 16) with (Z.ltb (Z.of_N h) 16) by (destruct (Z.ltb_spec (Z.of_N h) 16), (N.ltb_spec h 16); try reflexivity; lia);
replace (N.ltb l 16) with (Z.ltb (Z.of_N l) 16) by (destruct (Z.ltb_spec (Z.of_N l) 16), (N.ltb_spec l 16); try reflexivity; lia);
destruct (Z.ltb_spec (Z.of_N h) 16) as [H1|H1]; cbn [andb]; [|reflexivity];
destruct (Z.ltb_spec (Z.of_N l) 16) as [H2|H2]; [|reflexivity];
cbn [option_map]; f_equal;
(assert (E4 : φ (PrimInt63.add (PrimInt63.lsl (nybI (get s ci)) 4%uint63) (nybI (get s ci1))) = Z.of_N (h * 16 + l))
by (rewrite Uint63.add_spec, Uint63.lsl_spec, Sh, Sl, wB63; change (φ 4%uint63) with 4;
rewrite (Z.mod_small (Z.of_N h * 2 ^ 4)) by lia; rewrite Z.mod_small by lia; lia));
rewrite to_Z_rec_small by (rewrite E4; change (2 ^ Z.of_nat 8) with 256; lia);
rewrite E4, Z_to_bv_unsigned, bv_wrap_small by (change (bv_modulus 8) with 256; lia); reflexivity.
Qed.
Lemma seg_byte_atI_spec : ltac2:(TCodec.tc2 tcn__FxImg "Q<'2&D%211&>':'8';&Ar2%211&QDr1%211%83741&QA%517&QF+2+QN%3221%6251'4%11@&Q6r5r4%3221&5'R9y8%211&R:%123EqSF31&Lr3%22<1%:47O41%Q13@<1p0C1p0K1pT6Q51pT4Q71pSJQ91").
Proof.
induction chunks as [|c rest IH]; intros o off Ho Hoff; [reflexivity|].
cbn [seg_byte_atI segment_byte_at]. cbv zeta.
pose proof (Uint63.to_Z_bounded (PrimString.length c)) as Bl. rewrite wB63 in Bl.
assert (E : φ (PrimInt63.lsr (PrimString.length c) 1%uint63) = φ (PrimString.length c) / 2) by (rewrite Uint63.lsr_spec; reflexivity).
assert (D : 0 <= φ (PrimString.length c) / 2) by (apply Z.div_pos; lia).
rewrite ltb_b, E, Ho.
replace (N.ltb off (Z.to_N (φ (PrimString.length c) / 2))) with (Z.ltb (Z.of_N off) (φ (PrimString.length c) / 2))
by (destruct (Z.ltb_spec (Z.of_N off) (φ (PrimString.length c) / 2)), (N.ltb_spec off (Z.to_N (φ (PrimString.length c) / 2))); try reflexivity; lia).
destruct (Z.ltb_spec (Z.of_N off) (φ (PrimString.length c) / 2)) as [H|H].
- apply hex_byte_atI_spec; assumption.
- apply IH; [|lia]. rewrite Uint63.sub_spec, E, Ho, wB63. rewrite Z.mod_small by lia. lia.
Qed.
Definition sgi_ok (s : Segment) (g : sgi) : Prop :=
sg_seg g = s /\ φ (sg_lo g) = Z.of_N (seg_base s) /\ φ (sg_hi g) = Z.of_N (seg_base s) + Z.of_N (seg_size s) /\ sg_r g = seg_readable s.
Lemma mk_stab_spec : ltac2:(TCodec.tc2 tcn__FxImg "F'2'E%211'Q:%411'8'4%113&Q3r2%211(0r1%2291%93741'Q=&Q;r3%35A?219p051pTH@1pT@C1").
Proof.
induction segs as [|s r IH]; intros t H; cbn [mk_stab] in H; [injection H as <-; constructor|].
destruct (z61 (Z.of_N (seg_base s))) as [b|] eqn:Eb; [|discriminate].
destruct (z61 (Z.of_N (seg_size s))) as [z|] eqn:Ez; [|discriminate].
destruct (mk_stab r) as [t'|]; [|discriminate]. injection H as <-.
constructor; [|apply IH; reflexivity].
destruct (z61_spec _ _ Eb) as [B1 B2]. destruct (z61_spec _ _ Ez) as [Z1 Z2].
unfold sgi_ok. cbn [sg_seg sg_lo sg_hi sg_r]. repeat split; [exact B1|].
rewrite Uint63.add_spec, B1, Z1, wB63. apply Z.mod_small. lia.
Qed.
Lemma find_sgi_spec : ltac2:(TCodec.tc2 tcn__FxImg "R;'2'E%211'Q:%411&>'Q=&Q;r5r4%4597321'8'4%11:&Nr3%23871(0r2%22@1%93741&QA&A%11?%21?%4221'7';&Q?r7%811r1%4221r6%<11%>241%:241%I1Q4&Ir:+1%332G1&Q9%11:%K2Q;1%Q23841p0:1pTJD1&Q7%11Q8%L11&QD&F%;1Q<%211%411%Q=3M61%M27G'1&Q8%11QC&H%119%QD3531%Q6271%Q7291%Q82C1p0Q:1p0Q@1p0QK1pSNR31pSLR21pSBR31pTHR51pT@R81").
Proof.
intros segs t a e g F. induction F as [|s g0 segs t [S1 [S2 [S3 S4]]] F IH]; intros H Hae; cbn [find_sgi] in H; [discriminate|].
rewrite !leb_b in H.
destruct (Z.leb_spec (φ (sg_lo g0)) (φ a)) as [H1|H1].
- destruct (Z.leb_spec (φ e) (φ (sg_hi g0))) as [H2|H2].
+ injection H as <-. split; [|rewrite S1; repeat split; assumption].
intros u Hu. cbn [find_segment]. rewrite S1.
destruct (Z.leb_spec (Z.of_N (seg_base s)) u) as [A|A]; [|lia].
destruct (Z.leb_spec (u + 1) (Z.of_N (seg_base s) + Z.of_N (seg_size s))) as [B|B]; [reflexivity|lia].
+ destruct (Z.leb_spec (φ (sg_hi g0)) (φ a)) as [H3|H3]; [|destruct (Z.leb_spec (φ e) (φ (sg_lo g0))); [lia|discriminate]].
destruct (IH H Hae) as [I1 I2]. split; [|exact I2].
intros u Hu. cbn [find_segment].
destruct (Z.leb_spec (Z.of_N (seg_base s)) u) as [A|A]; cbn [andb]; [|apply I1; exact Hu].
destruct (Z.leb_spec (u + 1) (Z.of_N (seg_base s) + Z.of_N (seg_size s))) as [B|B]; [lia|apply I1; exact Hu].
- destruct (Z.leb_spec (φ (sg_hi g0)) (φ a)) as [H3|H3].
+ destruct (IH H Hae) as [I1 I2]. split; [|exact I2].
intros u Hu. cbn [find_segment].
destruct (Z.leb_spec (Z.of_N (seg_base s)) u) as [A|A]; cbn [andb]; [|apply I1; exact Hu].
destruct (Z.leb_spec (u + 1) (Z.of_N (seg_base s) + Z.of_N (seg_size s))) as [B|B]; [lia|apply I1; exact Hu].
+ destruct (Z.leb_spec (φ e) (φ (sg_lo g0))) as [H4|H4]; [|discriminate].
destruct (IH H Hae) as [I1 I2]. split; [|exact I2].
intros u Hu. cbn [find_segment].
destruct (Z.leb_spec (Z.of_N (seg_base s)) u) as [A|A]; cbn [andb]; [lia|apply I1; exact Hu].
Qed.
Lemma img_goI_eq : ltac2:(TCodec.tc2 tcn__FxImg "RD'2'E%211'3';&>'7&Q?r3r1%3221&QA&Q>&QEr4%211%4281%6281%<281'8'4%11D&Ir7r2+1%43321(0r6%22L1%;3941p0=1pTJL1'1&Hr5%211(6%C3521z%Q121J%L1=%N271&QF+2+QN%3221%Q4251&A%11>&QG&QD&Fr8%211%411%62L1%Q63QE81r9%711%911%QF21Q6%QN1QJ%Q;11&Q2&Gr:%211%431Q=:&Mr;%231B=%QE3941p0<1p0A1p0L1p0Q41p0Q71p0Q>1pT4R:1pSBR<1pT2R>1pT>RA1pT@RA1").
Proof.
intros segs seg n. induction n as [|n IH]; intros a o Hf Hr Ha Hn Ho Hb; [reflexivity|].
cbn [img_goI img_bytes]. unfold seg_rom, memory_read.
rewrite Z_to_bv_unsigned, bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64); lia).
change (Z.of_N 1) with 1. rewrite (Hf a) by lia. rewrite Hr.
change (N.to_nat 1) with 1%nat. cbn [segment_read_bytes].
rewrite (seg_byte_atI_spec (seg_bytes seg) o (Z.to_N (a - Z.of_N (seg_base seg)))) by (rewrite Z2N.id by lia; lia).
destruct (segment_byte_at (seg_bytes seg) (Z.to_N (a - Z.of_N (seg_base seg)))) as [b|]; cbn [option_map]; [|reflexivity].
rewrite (IH (a + 1) (PrimInt63.add o 1%uint63)); [reflexivity| | | | | |].
- intros u Hu. apply Hf. lia.
- exact Hr.
- lia.
- lia.
- rewrite Uint63.add_spec, Ho, wB63. change (φ 1%uint63) with 1. rewrite Z.mod_small by lia. lia.
- lia.
Qed.
Theorem img_bytesFF_eq : ltac2:(TCodec.tc2 tcn__FxImg "F'2'E%211';'3'8'4%714%211&Q0&Q3r3%211r2r1%643421&M%13643%=3:31pT2?1pSBA1pT@C1").
Proof.
intros segs a n. unfold img_bytesFF. destruct n as [|n']; [reflexivity|]. set (n := S n').
destruct (mk_stab segs) as [t|] eqn:Et; [|reflexivity].
destruct (z61 a) as [a63|] eqn:Ea; [|reflexivity]. destruct (z61 (Z.of_nat n)) as [n63|] eqn:En; [|reflexivity].
destruct (z61_spec _ _ Ea) as [A1 A2]. destruct (z61_spec _ _ En) as [N1 N2].
assert (EE : φ (PrimInt63.add a63 n63) = a + Z.of_nat n) by (rewrite Uint63.add_spec, A1, N1, wB63; apply Z.mod_small; lia).
destruct (find_sgi t a63 (PrimInt63.add a63 n63)) as [g|] eqn:Ef; [|reflexivity].
destruct (find_sgi_spec segs t _ _ g (mk_stab_spec _ _ Et) Ef) as [F1 [F2 [F3 F4]]]; [rewrite EE, A1; unfold n; lia|].
rewrite EE, A1 in F1. rewrite A1 in F3. rewrite F4.
destruct (seg_readable (sg_seg g)) eqn:Hr.
- apply img_goI_eq; try assumption; try lia.
rewrite Uint63.sub_spec, A1, F2, wB63. apply Z.mod_small. lia.
- unfold n. cbn [img_bytes]. unfold seg_rom, memory_read.
rewrite Z_to_bv_unsigned, bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64); lia).
change (Z.of_N 1) with 1. rewrite (F1 a) by (unfold n; lia). rewrite Hr. reflexivity.
Qed.
Theorem img_bytesI_eq : ltac2:(TCodec.tc2 tcn__FxImg "D'2'E%211';'3'8'4%714%211&Q1r3r2r1%43321&M%13543%;3831pT2=1pSB?1pT@A1").
Proof. intros. apply img_bytesFF_eq. Qed.
End IMGF.

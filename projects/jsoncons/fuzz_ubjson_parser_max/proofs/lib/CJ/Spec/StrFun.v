(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import MState Mem Cells Step Arr Bytes.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Spec_StrFun () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Nat."; "Corelib.Init.Peano."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.BvBase."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Arr."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Bytes."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Cells."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Mem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Step."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.StrFun."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A"; "1None"; "1O"; "1S"; "1Some"; "1app"; "1bool"; "1cons"; "1length"; "1list"; "1nat"; "1nil"; "1option"; "1true"; "2False"; "2and"]; ["2eq"; "2ex"; "2iff"; "2not"; "2or"; "3add"; "3sub"; "4le"; "4lt"; "5firstn"; "5map"; "5repeat"; "5skipn"; "6Z"; "0F"; "7Z_to_le_bytes"]; ["7bytes_le_to_Z"; "7le_bytes_to_word"; "8store_ok"; "8write_to_mem"; "9sext"; "0P"; "0Q"; "0Q'"; ":u8arr"; ";le_val"; "<CB"; "<cell"; "=le1"; "=le4"; "=le8"; "=upd_bytes"]; ["=wa"; ">rw_cells"; "?BC4"; "?BC8"; "?copied"; "?filled"; "?find_byte"; "?list_Z_eqb"; "?memchr_ok"; "?memcmp_model"; "?strnlen_res"; "?zseq"; "@In"; "@forallb"; "@nth_error"; "Aadd"]; ["Adiv"; "Aeqb"; "Aland"; "Ale"; "Alor"; "Alt"; "Amin"; "Amodulo"; "Amul"; "Aof_nat"; "Apow"; "Asub"; "Ato_nat"; "0a"; "0b"; "0b'"]; ["0b0"; "0b1"; "0b2"; "0b3"; "0base"; "0bs"; "0c"; "0f"; "0hi"; "0i"; "0j"; "0k"; "0l"; "0l1"; "0l2"; "0lo"]; ["0m"; "0n"; "0p"; "0r"; "0rest"; "0segs"; "0slack"; "0src"; "BZ_to_bv"; "Bbv"; "Bbv_extract"; "Bbv_swrap"; "Bbv_unsigned"; "Bbv_wrap"; "0str"; "0v"]; ["0w"; "0x"; "0xs"; "0y"; "0z"]]).
Fixpoint find_byte (c : Z) (l : list byte) : option nat :=
match l with
| [] => None
| b :: l' => if bv_unsigned b =? c then Some 0%nat
else match find_byte c l' with Some i => Some (S i) | None => None end
end.
Lemma find_byte_Some : ltac2:(TCodec.tc2 tcn__CJ_Spec_StrFun "QI'M'9'S9y8%211%411':'@'<%113&QFr3r2%3221(4r1%22:1%:3841'?&H&8%12A:%32:1'A%@1D&QNr4%23G1@%>2H=%F3521&S<%12L@r5%J3Q121%@251qTNO1%=2Q01%B2I;r6%>3Q31L%J2Q4L%Q23A21&C%=2Q8Q0r8%Q63Q=21%411p061p0;1pTNQ=1pUFQ<1%Q12?1%Q22N1p0Q41pUDQ@1pUJQB1pU>QH1").
Proof.
intros c l; induction l as [|b l IH]; intros i H; cbn in H; [discriminate|].
destruct (Z.eqb_spec (bv_unsigned b) c) as [E|NE].
- injection H as <-. cbn. split; [lia|]. split. { exists b. auto. } intros; lia.
- destruct (find_byte c l) as [i'|] eqn:F; [|discriminate]. injection H as <-.
destruct (IH i' eq_refl) as (Hl & (b' & Hn & Hb') & Hmin). cbn. split; [lia|]. split. { exists b'. auto. }
intros [|j] b2 Hj Hn2; cbn in Hn2. { injection Hn2 as <-. exact NE. } eapply Hmin; [|exact Hn2]. lia.
Qed.
Lemma find_byte_None : ltac2:(TCodec.tc2 tcn__CJ_Spec_StrFun "Q4'M'9'S9y8%211%411'@'<':%211&QFr2r1%3221(1%117%:3731%:1=&QNr4%23@19(4%12B:%A3631&C&S<%12G?r6%F3L21%511p071pTNK1pUFH1p0A1pUJM1pU>Q31").
Proof.
intros c l; induction l as [|b l IH]; intros H j b2 Hn; [destruct j; discriminate|].
cbn in H. destruct (Z.eqb_spec (bv_unsigned b) c) as [E|NE]; [discriminate|].
destruct (find_byte c l) eqn:F; [discriminate|].
destruct j as [|j]; cbn in Hn. { injection Hn as <-. exact NE. } eapply IH; eauto.
Qed.
Lemma find_byte_app_l : ltac2:(TCodec.tc2 tcn__CJ_Spec_StrFun "N'M'9'S9y8%211%411':'@'<%113&QFr4r3%3221(4r1%22:1%:3841r5&5%13@98%;231r2%92A1%A3?31p081pUDD1pUNF1pULG1pU>M1").
Proof.
intros c l1; induction l1 as [|b l1 IH]; intros l2 i H; cbn in *; [discriminate|].
destruct (bv_unsigned b =? c); [exact H|]. destruct (find_byte c l1) eqn:F; [|discriminate].
rewrite (IH l2 n eq_refl). exact H.
Qed.
Lemma find_byte_app_r : forall c l1 l2, find_byte c l1 = None ->
find_byte c (l1 ++ l2) = match find_byte c l2 with Some i => Some (length l1 + i)%nat | None => None end.
Proof.
intros c l1; induction l1 as [|b l1 IH]; intros l2 H; cbn in *. { destruct (find_byte c l2); reflexivity. }
destruct (bv_unsigned b =? c); [discriminate|]. destruct (find_byte c l1) eqn:F; [discriminate|].
rewrite (IH l2 eq_refl). destruct (find_byte c l2); reflexivity.
Qed.
Lemma find_byte_firstn : ltac2:(TCodec.tc2 tcn__CJ_Spec_StrFun "N'M'9'S9y8%211%411':'@'<%113&QFr4&Ir2r3%33;21%6251(4r1%22=1%=3;41r5%<21;%62A:%A3?21p051pUDD1pV4E1pUJG1pU>M1").
Proof.
intros c l n i H. rewrite <- (firstn_skipn n l). apply find_byte_app_l. exact H.
Qed.
Lemma find_byte_charact : ltac2:(TCodec.tc2 tcn__CJ_Spec_StrFun "QC'M'9'S9y8%211%411':'@'<%115&QNr3r2%33921(4r1%22<1%:3841&S<%12@7r5%>3E21&Hr6%22<1r8%@3F1?%=2G?%E3C21&C%<2KCr:%I3Q021%411p061p0;1pU0Q01pUFO1%N1Q0&QFr7%221B%L2Q4F%Q43521p071p0H1p0M1pTNQ;1pUDQ:1pUJQ<1pU>QB1").
Proof.
intros c l i b Hn Hb Hmin. destruct (find_byte c l) as [i'|] eqn:F.
- destruct (find_byte_Some _ _ _ F) as (Hl & (b' & Hn' & Hb') & Hmin').
destruct (Nat.lt_trichotomy i i') as [Hlt|[->|Hgt]].
+ exfalso. exact (Hmin' _ _ Hlt Hn Hb).
+ reflexivity.
+ exfalso. exact (Hmin _ _ Hgt Hn' Hb').
- exfalso. exact (find_byte_None _ _ F _ _ Hn Hb).
Qed.
Lemma find_byte_None_intro : ltac2:(TCodec.tc2 tcn__CJ_Spec_StrFun "Q4'M'9'S9y8%211%411':'@'<%115&QNr3r2%33921(4r1%22<1%:3841&C&S<%12A8r5%?3F21%511p071pTNE1pUFD1%C1E&QF%12BA(1%11I%I3531p071pUJM1pU>Q31").
Proof.
intros c l H. destruct (find_byte c l) as [i|] eqn:F; [|reflexivity].
destruct (find_byte_Some _ _ _ F) as (_ & (b & Hn & Hb) & _). exfalso. exact (H _ _ Hn Hb).
Qed.
Lemma find_byte_notin : ltac2:(TCodec.tc2 tcn__CJ_Spec_StrFun "O'M'9'S9y8%211%411&QLr1r2%33521&C'@&S<%12:5r4%43?21%611p081pTN>1'<':%211&QFr3%221@(1%116%@3631p0:1pUJH1pU>N1").
Proof.
intros c l H. apply find_byte_None_intro. intros j b Hn. apply H. eapply nth_error_In; eauto.
Qed.
Lemma find_byte_hit : ltac2:(TCodec.tc2 tcn__CJ_Spec_StrFun "Q<'M'9'S9y8%211%411&QLr1r4%33521&C'@&S<r2%22;1r6%53@21%711p091pU0?1r3%92B1r5%<3G21'<':%211&QF&5(7%13JF:%33K91%52A1(4&8%12O=%32;1%J3;51p0?1p0D1pV:Q31pTNQ51pUJQ51pU>Q;1").
Proof.
intros c l b rest Hl Hb. rewrite find_byte_app_r by (apply find_byte_notin; exact Hl).
cbn. rewrite (proj2 (Z.eqb_eq _ _) Hb). f_equal. lia.
Qed.
Definition memchr_res (A : Z) (c : Z) (n : Z) (buf : list byte) : Z :=
match find_byte c (firstn (Z.to_nat n) buf) with Some i => A + Z.of_nat i | None => 0 end.
Definition memchr_ok (A c n : Z) (buf : list byte) : Prop :=
match find_byte c (firstn (Z.to_nat n) buf) with
| Some j => (n <= Z.of_nat (length buf) \/
Z.of_nat j + 1 + (- (A + Z.of_nat j + 1)) mod 8 <= Z.of_nat (length buf))%Z
| None => (n <= Z.of_nat (length buf))%Z
end.
Definition strnlen_res (n : Z) (buf : list byte) : Z :=
match find_byte 0 (firstn (Z.to_nat n) buf) with Some i => Z.of_nat i | None => n end.
Section NulTerminated.
Variables (A n : Z) (str slack : list byte).
Hypothesis NONUL : ~ In (Z_to_bv 8 0) str.
Hypothesis PAD : ((- (A + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack))%Z.
Lemma str_bytes_nz : ltac2:(TCodec.tc2 tcn__CJ_Spec_StrFun "B'S9y8%211&QLr1vS>%33421&C'@'M&S<r2%22;1z%63521%811p0:1pTN?1").
Proof. intros b Hb E. apply NONUL. replace (Z_to_bv 8 0) with b; [exact Hb|]. apply bv_eq. rewrite E. reflexivity. Qed.
Lemma find_byte_cstr : ltac2:(TCodec.tc2 tcn__CJ_Spec_StrFun "Q1&R5&R9&8'S9y8%211vS>%5221%711vS1%:221'@'<':%211&QFz&I&R<%11:&5(7&S8%12C7vS6%43D21%63ED1%:3F81%=2<1(4%12AG%D3A31p0F1").
Proof.
intros Hn. rewrite firstn_app. rewrite firstn_all2 by lia.
destruct (Z.to_nat n - length str)%nat as [|k] eqn:E; [lia|]. cbn [firstn].
apply find_byte_hit; [apply str_bytes_nz| reflexivity].
Qed.
Lemma find_byte_cstr_short : ltac2:(TCodec.tc2 tcn__CJ_Spec_StrFun "Q1&R3vS1&R9&8'S9y8%211vS>%5221%711%:291'@'<':%211&QFz&I&R<%11B&5(7&S8%12B7vS6%43C21%63DC1%:3E81%=2<1(1%11A%D3A31p0F1").
Proof.
intros Hn. rewrite firstn_app. replace (Z.to_nat n - length str)%nat with 0%nat by lia. cbn [firstn]. rewrite app_nil_r.
apply find_byte_notin. intros b Hb. apply str_bytes_nz. rewrite <- (firstn_skipn (Z.to_nat n) str). apply in_or_app. left. exact Hb.
Qed.
Lemma memchr_ok_cstr : ltac2:(TCodec.tc2 tcn__CJ_Spec_StrFun "@&QHv0zvS1&5'S9y8%211vS>(7&S8%1259vS6%43621%:3761%?4>=<1").
Proof.
unfold memchr_ok. destruct (Z.lt_ge_cases (Z.of_nat (length str)) n) as [Hn|Hn].
- rewrite find_byte_cstr by lia. right. rewrite length_app. cbn [length]. lia.
- rewrite find_byte_cstr_short by lia. rewrite length_app. cbn [length]. lia.
Qed.
Lemma memchr_res_cstr :
memchr_res A 0 n (str ++ Z_to_bv 8 0 :: slack) = (if Z.of_nat (length str) <? n then A + Z.of_nat (length str) else 0)%Z.
Proof.
unfold memchr_res. destruct (Z.ltb_spec0 (Z.of_nat (length str)) n).
- rewrite find_byte_cstr by lia. reflexivity.
- rewrite find_byte_cstr_short by lia. reflexivity.
Qed.
Lemma strnlen_res_cstr : ltac2:(TCodec.tc2 tcn__CJ_Spec_StrFun "H'@'M&QJvS1&5'S9y8%211vS>(7&S8z%2261vS6%53721%;3871%>2=1&R6&R9&8%12=<%311%521C%G3F71").
Proof.
unfold strnlen_res. destruct (Z.lt_ge_cases (Z.of_nat (length str)) n).
- rewrite find_byte_cstr by lia. lia.
- rewrite find_byte_cstr_short by lia. lia.
Qed.
End NulTerminated.
Fixpoint strncmp_walk (l r : list byte) (k : nat) {struct l} : option Z :=
match l, r with
| a :: l', b :: r' =>
if ((bv_unsigned a =? 0) || (bv_unsigned b =? 0) || Nat.eqb k 0 || negb (bv_unsigned a =? bv_unsigned b))%bool
then Some (bv_unsigned a - bv_unsigned b)
else match k with O => Some (bv_unsigned a - bv_unsigned b) | S k' => strncmp_walk l' r' k' end
| _, _ => None
end.
Definition strncmp_model (l r : list byte) (n : Z) : option Z :=
if n =? 0 then Some 0 else strncmp_walk l r (Z.to_nat (n - 1)).
Lemma skipn_cons_nth : forall {X} (l : list X) i a l', skipn i l = a :: l' -> nth_error l i = Some a /\ l' = skipn (S i) l.
Proof.
intros X l i a l' H. split.
- rewrite <- (firstn_skipn i l), H. rewrite nth_error_app2 by (rewrite firstn_length; pose proof (skipn_length i l) as L; rewrite H in L; cbn in L; lia).
rewrite firstn_length. replace (i - _)%nat with 0%nat by (pose proof (skipn_length i l) as L; rewrite H in L; cbn in L; lia). reflexivity.
- replace (S i) with (1 + i)%nat by lia. rewrite <- skipn_skipn, H. reflexivity.
Qed.
Fixpoint memcmp_model (l r : list byte) (n : nat) {struct n} : option Z :=
match n with
| O => Some 0
| S n' =>
match l, r with
| a :: l', b :: r' => if bv_unsigned a =? bv_unsigned b then memcmp_model l' r' n' else Some (bv_unsigned a - bv_unsigned b)
| _, _ => None
end
end.
Lemma memcmp_model_total : ltac2:(TCodec.tc2 tcn__CJ_Spec_StrFun "Q2'9'S9y8%211%411':'Gr1&8r3%2271%5241r2%7213'A'M'@'<%113&QIr6r5r4%43321(4%12:B%:3831qW0<1%>2=1p0@1p0C1pV4J1pV8L1pUJM1").
Proof.
intros l r n; revert l r; induction n as [|n IH]; intros [|a l] [|b r] Hl Hr; cbn in *; try lia; try (eexists; reflexivity).
destruct (bv_unsigned a =? bv_unsigned b); [apply IH; lia| eexists; reflexivity].
Qed.
Lemma memcmp_model_zero : ltac2:(TCodec.tc2 tcn__CJ_Spec_StrFun "Q5'9'S9y8%211%411':'Gr1&8r3%2271%5241r2%7213&B'@'<'M%211&QIr5r4%3321=(4z%2281%;3841&I%13IC8%23JD8%?3J21%A251p0C1p0F1pV4M1pV8O1pUJQ01").
Proof.
intros l r n; revert l r; induction n as [|n IH]; intros [|a l] [|b r] Hl Hr; cbn in *; try lia; try (split; reflexivity).
destruct (Z.eqb_spec (bv_unsigned a) (bv_unsigned b)) as [E|NE].
+ rewrite IH by lia. assert (Hab : a = b) by (apply bv_eq; exact E). rewrite Hab. split; [intros ->; reflexivity| intros H; injection H; auto].
+ split. { intros H. exfalso. apply NE. injection H. pose proof (bv_unsigned_in_range 8 a). pose proof (bv_unsigned_in_range 8 b). lia. }
intros H. injection H as Hab _. subst. lia.
Qed.
Section WithSegs.
Variable segs : list MemImageType.Segment.
Lemma u8arr_write_bytes : ltac2:(TCodec.tc2 tcn__CJ_Spec_StrFun "QB'S9yR0%211'<y8%511%311p051'M'9%115&Q8vS5r5r4r3%544321&R3z%2214'G&E&R<%119&8%12D:%5231%32F>%8221&Q3r8&Q@&QOr7%221E%411%7361F&Q?r6%A1J%3321J%N4M581p0>1p0H1p0L1pW6Q31pUDQ61pU<Q51p2Q81pV2Q:1").
Proof.
intros m A bs i xs [Hb Hw] Hi Hl. split.
- apply bytes_at_write_inside; assumption.
- rewrite upd_bytes_length by lia. apply wr_at_write. exact Hw.
Qed.
Lemma u8arr_store_ok_n : ltac2:(TCodec.tc2 tcn__CJ_Spec_StrFun "QC'S9yR0%211'<y8%511%311p051'M'9%115':&Q8vS5r6r5r4%544321&R3z%2214&QO&R9%117%3291&8%12E<%511%:241'@&Q@r8%;21B%311%53Q0B1'6&Q2r:%24I1GH(=%;3521p071p0>1p0G1p0K1pTLQ;1pV4Q31pUDQ71pU<Q61p2Q91pV2Q;1").
Proof. intros m A bs i n a [_ Hw] Hi Hn ->. eapply wr_at_store_ok; eauto; lia. Qed.
Lemma rw_cells_CB_length : ltac2:(TCodec.tc2 tcn__CJ_Spec_StrFun "Q3'S9yR0%211'<y8%511%311p051'M':'9%116&QAvS5r4r3(7'Q;(Q:r2r1%3221(;%116%83731%=4<;:1'@&8%12G9%33D1>p051pU<D1pV4G1p2I1pV2K1").
Proof. intros m A n bs [[H _] _]. cbn in H. tauto. Qed.
End WithSegs.
Definition filled (c : byte) (bs : list byte) (Q : Z -> Prop) : Prop :=
forall j, (0 <= j < Z.of_nat (length bs))%Z -> Q j -> nth_error bs (Z.to_nat j) = Some c.
Lemma filled_init : ltac2:(TCodec.tc2 tcn__CJ_Spec_StrFun ">'S9y8%211'9%112&QEr2r1'M'>q021%63541pU<81pU>;1").
Proof. intros c bs j _ []. Qed.
Lemma filled_mono : ltac2:(TCodec.tc2 tcn__CJ_Spec_StrFun "K'S9y8%211'9%112'M!p021&QEr4r3r2%43321r1%411r5%115p031pUF=1r6%<315:p031p0:1pR@@1pR>A1pU<E1pU>H1").
Proof. intros c bs Q Q' H HQ j Hj Hq. apply H; auto. Qed.
Lemma nth_error_repeat' : forall {X} (x : X) k i, (i < k)%nat -> nth_error (repeat x k) i = Some x.
Proof. intros X x k; induction k as [|k IH]; intros [|i] H; cbn; try lia; auto. apply IH. lia. Qed.
Lemma filled_upd : ltac2:(TCodec.tc2 tcn__CJ_Spec_StrFun "QC'S9y8%211'9%112'M!p021':&QEr5r4r3%43321'G&Er2%2251&8%12A9%6231r7&Q?r6&K%13G4=%433?1'Dr1%611'?&R3&R9%11G%3216&R5&QO%51J%2251%42;1%:261%>2<1qUFQ51%Q23FA1p0H1p0Q01pUHQ61pUDQ71pR>Q91pU<Q=1pU>Q@1").
Proof.
intros c bs Q i k HF Hk j Hj HQ. rewrite upd_bytes_length in Hj by (rewrite repeat_length; lia).
rewrite upd_bytes_nth by (rewrite ?repeat_length; lia). rewrite repeat_length.
destruct (Nat.leb_spec0 i (Z.to_nat j)); destruct (Nat.ltb_spec0 (Z.to_nat j) (i + k)); cbn [andb];
first [ apply nth_error_repeat'; lia | destruct HQ as [HQ|HQ]; [apply HF; [lia| exact HQ] | exfalso; lia] ].
Qed.
Lemma filled_updZ : ltac2:(TCodec.tc2 tcn__CJ_Spec_StrFun "QH'S9y8%211'9%112'M!p021':&QEr5r4r3%43321&R3z%2214'G&E&R<%119%3219&8r6%22F1%8241r8&Q?r7%:1C&K%13M5D%53431'Dr1%711'?%G2>3&R5&QO&R9%11O%32C1%5291%8271%<2:1qUFQ91%Q63E?1p0G1p0Q11p0Q51pUHQ;1pUDQ?1pR>Q>1pU<QB1pU>QE1").
Proof.
intros c bs Q i k HF Hi Hk j Hj HQ. apply (filled_upd c bs Q (Z.to_nat i) k HF Hk j Hj). destruct HQ; [left; assumption| right; lia].
Qed.
Lemma filled_all : ltac2:(TCodec.tc2 tcn__CJ_Spec_StrFun "Q6'S9y8%211'9%112'M!p021&QEr3r2r1%43321'?&R3z%2215&R5&R9&8r4%22C1%411%62<1%;281%51?p021pUFF1'@&Kr5%23M1:%43L<1p061p0F1pR>L1pU<Q01pU>Q31").
Proof.
intros c bs Q HF HQ. apply nth_error_ext. intros i.
destruct (Nat.lt_ge_cases i (length bs)) as [Hi|Hi].
- rewrite nth_error_repeat' by lia. replace i with (Z.to_nat (Z.of_nat i)) by lia. apply HF; [lia|]. apply HQ. lia.
- rewrite (proj2 (nth_error_None _ _)) by lia. rewrite (proj2 (nth_error_None _ _)) by (rewrite repeat_length; lia). reflexivity.
Qed.
Lemma Z_to_bv8_mod : ltac2:(TCodec.tc2 tcn__CJ_Spec_StrFun ">'M'@'S9y8%211&S8r1%2241&R7+X0%2241%6281%;3851pW:=1").
Proof. intros z. apply bv_eq. rewrite !Z_to_bv_unsigned. change (bv_wrap 8 ?x) with (x mod 256)%Z. rewrite Z.mod_mod by lia. reflexivity. Qed.
Lemma land_align_down : ltac2:(TCodec.tc2 tcn__CJ_Spec_StrFun "O'M'?&R3zr2%3221&R5&R:+2+R0%3221%5271%;271%;294%=291'@&R2r4&R;r3%=2<1%32;1%6251&R7%1274%7281%;3J41p0=1p0@1pUFM1pW4N1").
Proof.
intros x j Hx Hj.
replace (2^64 - 2^j)%Z with (Z.ldiff (Z.ones 64) (Z.ones j)).
2:{ rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia.
unfold Z.ones. rewrite Z.shiftl_mul_pow2 by lia.
replace (2^64)%Z with (2^j * 2^(64-j))%Z by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
replace (Z.pred (1 * (2 ^ j * 2 ^ (64 - j))))%Z with ((2^(64-j) - 1) * 2^j + (2^j - 1))%Z by lia.
rewrite Z.div_add_l by lia. rewrite Z.div_small by (split; [lia| apply Z.lt_pred_l || lia]). lia. }
rewrite Z.ldiff_land, Z.land_assoc. rewrite <- Z.ldiff_land.
rewrite Z.land_ones by lia. rewrite Z.mod_small by lia.
rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia.
pose proof (Z.div_mod x (2^j)%Z ltac:(lia)). lia.
Qed.
Definition zseq (n : nat) : list Z := map Z.of_nat (seq 0 n).
Lemma forallb_zseq : ltac2:(TCodec.tc2 tcn__CJ_Spec_StrFun "N':'M'6p021'@&QMr1&QKr2%211%53941(=%83:21'?&R3z%221:&R5&R9r4%211%42?1%9261%41?%D3F1=p031pU>I1p0?1pU@I1pV4M1").
Proof.
intros n f H c Hc. rewrite forallb_forall in H. apply H. unfold zseq. apply in_map_iff.
exists (Z.to_nat c). split; [lia|]. apply in_seq. lia.
Qed.
Lemma brute256_ok : ltac2:(TCodec.tc2 tcn__CJ_Spec_StrFun "L'M'6p021'@&QMr1&QKuX0%211%53941(=%83:21'?&R3z%221:&R5+X0%22=1%7241r4r2%211%D3F1=p051pU>I1p0?1pR<I1").
Proof. intros P H c Hc. exact (forallb_zseq 256 P H c Hc). Qed.
Lemma word_eq_of_eqb : ltac2:(TCodec.tc2 tcn__CJ_Spec_StrFun "K'M'@'6&R1&R7r2&R:+2+R0%3221%6251r1%8213%:231(=%>3=21'S9yR0%211&S8r3%2241%325A%F3521p091pW8I1pW4J1").
Proof. intros x y H. apply Z.eqb_eq in H. apply bv_eq. rewrite !Z_to_bv_unsigned. exact H. Qed.
Lemma map_unsigned_inj : ltac2:(TCodec.tc2 tcn__CJ_Spec_StrFun "E'9'S9y8%211%411'@'M%711&J&S<%118r2%449621r1%64;841%:3831r3%<3=16p031pUN?1pUL@1").
Proof.
induction l1 as [|x l1 IH]; intros [|y l2] H; cbn in H; try discriminate; [reflexivity|].
injection H as Hx Hl. f_equal; [apply bv_eq; exact Hx| apply IH; exact Hl].
Qed.
Definition list_Z_eqb (l1 l2 : list Z) : bool := if list_eq_dec Z.eq_dec l1 l2 then true else false.
Lemma list_Z_eqb_eq : ltac2:(TCodec.tc2 tcn__CJ_Spec_StrFun "@'9'M%211'@'6&QGr2r1%3221(=%73621r3%93:16p031pUN<1pUL=1").
Proof. intros l1 l2. unfold list_Z_eqb. destruct (list_eq_dec Z.eq_dec l1 l2); [auto|discriminate]. Qed.
Lemma bcast_ok : ltac2:(TCodec.tc2 tcn__CJ_Spec_StrFun "QB'M'9'S9y8%211%411p061':'@'6&QM&QG&J&S<%11;r3r1%211%64>B41&Kr2%23E51%;241qU>G1&QKuX0%211%A3K41(=%E3D21'?&R3z%221A&R5+X0%22D1%7241r5%11C&S8%12Q6Er4%H3Q721%Q43Q751p081pU>Q>1p0B1pUHQ91pQNQ;1").
Proof.
intros F k H c Hc. apply map_unsigned_inj.
pose proof (forallb_zseq 256 _ H c Hc) as E. cbn beta in E. apply list_Z_eqb_eq in E. rewrite E.
rewrite map_repeat. f_equal. rewrite Z_to_bv_unsigned. symmetry. apply bv_wrap_small. unfold bv_modulus. cbn. lia.
Qed.
Definition BC4 := 16843009.
Definition BC8 := 72340172838076673.
Lemma le4_bcast_s : ltac2:(TCodec.tc2 tcn__CJ_Spec_StrFun "Q3'M'?&R3zr1%3221&R5+X0%2241%8241'@'9'S9y8%211%411&Q=&S8yR0&S;yQ0&R8r2&QB%3221%6251%9281%;11&K%<2@7u4%33A21%F3A51p0H1pU>Q21").
Proof. apply (bcast_ok (fun c => le4 (Z_to_bv 64 (bv_swrap 32 (c * BC4)))) 4). vm_compute. reflexivity. Qed.
Lemma le4_bcast : ltac2:(TCodec.tc2 tcn__CJ_Spec_StrFun "Q0'M'?&R3zr1%3221&R5+X0%2241%8241'@'9'S9y8%211%411&Q=&S8yR0&R8r2&QB%3221%6251%811&K%92=6u4%33>21%C3>51p0E1pU>O1").
Proof. apply (bcast_ok (fun c => le4 (Z_to_bv 64 (c * BC4))) 4). vm_compute. reflexivity. Qed.
Lemma le8_bcast : ltac2:(TCodec.tc2 tcn__CJ_Spec_StrFun "Q0'M'?&R3zr1%3221&R5+X0%2241%8241'@'9'S9y8%211%411&Q>&S8yR0&R8r2&QC%3221%6251%811&K%92=6u8%33>21%C3>51p0E1pU>O1").
Proof. apply (bcast_ok (fun c => le8 (Z_to_bv 64 (c * BC8))) 8). vm_compute. reflexivity. Qed.
Lemma le1_byte : ltac2:(TCodec.tc2 tcn__CJ_Spec_StrFun "H'S9yR0%211'@'9y8%611%311&Q<r1%211(7&S8&R7&S<%12>6+X0%4221%62=1(;%11>%:3?31%C3?<1pW4E1").
Proof. intros x. cbn. rewrite <- Z_to_bv8_mod. reflexivity. Qed.
Definition copied (src bs : list byte) (k : nat) : Prop :=
length bs = length src /\ firstn k bs = firstn k src.
Lemma copied_0 : ltac2:(TCodec.tc2 tcn__CJ_Spec_StrFun "D'9'S9y8%211%411'@':&8r1%2261r2%4281%73631&QDr3(2%33261p051pU<>1pV@?1").
Proof. intros src bs H. split; [exact H| reflexivity]. Qed.
Lemma copied_all : ltac2:(TCodec.tc2 tcn__CJ_Spec_StrFun "H'9'S9y8%211%411':&QDr3r2r1%43321'G&8r4%22;1%4217'@r5%23>51p041p0:1pUH@1pU<B1pV@C1").
Proof.
intros src bs k [Hl Hf] Hk. rewrite <- (firstn_all2 (n:=k) bs) by lia. rewrite <- (firstn_all2 (n:=k) src) by lia. exact Hf.
Qed.
Lemma firstn_app_len : forall {X} (a b : list X) k, k = length a -> firstn k (a ++ b) = a.
Proof. intros X a b k ->. rewrite firstn_app, firstn_all, Nat.sub_diag. cbn. apply app_nil_r. Qed.
Lemma app_firstn_mid_skipn : forall {X} (l : list X) p k,
firstn p l ++ firstn k (skipn p l) ++ skipn (p + k) l = l.
Proof.
intros X l p k. rewrite <- (firstn_skipn p l) at 4. f_equal.
replace (skipn (p + k) l) with (skipn k (skipn p l)) by (rewrite skipn_skipn; f_equal; lia). apply firstn_skipn.
Qed.
Lemma copied_upd : ltac2:(TCodec.tc2 tcn__CJ_Spec_StrFun "Q8'9'S9y8%211%411':&QDr4r3r2%43321'@&I&8%12;5&Lr5%23>91%63?41%83?1:'G&E%92C>%22@1r6%<2F1%6231r7&Q?%135=F%A2KG%:2?1%J3531p071p0?1p0I1pW6Q01pV6Q01pU<Q21pV@Q31").
Proof.
intros src bs p xs [Hl Hf] Hx Hp. split.
- rewrite upd_bytes_length by lia. exact Hl.
- unfold upd_bytes. rewrite app_assoc.
assert (L1 : length (firstn p bs ++ xs) = (p + length xs)%nat) by (rewrite app_length, firstn_length; lia).
rewrite (firstn_app_len (firstn p bs ++ xs)) by lia.
transitivity (firstn (p + length xs) (firstn p src ++ xs ++ skipn (p + length xs) src)).
+ assert (L2 : length (firstn p src ++ xs) = (p + length xs)%nat) by (rewrite app_length, firstn_length; lia).
rewrite app_assoc, (firstn_app_len (firstn p src ++ xs)) by lia. rewrite Hf. reflexivity.
+ f_equal. etransitivity; [ | apply (app_firstn_mid_skipn src p (length xs))]. rewrite Hx. reflexivity.
Qed.
Lemma copied_updZ : ltac2:(TCodec.tc2 tcn__CJ_Spec_StrFun "QF'9'S9y8%211%411'M&QDr4r3&R<r2%211%63541&R3z%2217'@&I&8%12@;&L%<1>r6%33D21%73E51%93E1A'G&Er5%D11%<2KG%4221r7%?2N1%8231r8&Q?%L1?%2361:&QO&R9%G2Q6=%211%42E1%Q311%Q73:71p0<1p0F1p0Q11p0Q51pW6Q>1pR<Q>1pU<Q@1pV@QA1").
Proof.
intros src bs P xs HC HP Hx Hl. replace (Z.to_nat (P + Z.of_nat (length xs))) with (Z.to_nat P + length xs)%nat by lia.
apply copied_upd; assumption.
Qed.
Lemma window_ex : ltac2:(TCodec.tc2 tcn__CJ_Spec_StrFun "Q6'9'S9y8%211%411'M':'G&E&R<r2%211r1%5221&8r3%22=1%:241'A'?'@&I&Lr4%?11r5%43G21%63H<1%83H1@%?2JA%:3H1?%<231qW6L1%?2M1p0A1pUHM1pUDO1pUJQ11").
Proof. intros l i k H. eexists. split; [reflexivity|]. rewrite firstn_length, skipn_length. lia. Qed.
Lemma window_nth : ltac2:(TCodec.tc2 tcn__CJ_Spec_StrFun "QA'9'S9y8%211%411'M':'@&Ir3&L&R<r4%211r6%53<21%83=71r5%;3>21&R3z%2214&H%12;6&QOr7&R9%11:%4231%F3HA1'<%11L&QNr:%G1A%33Q021r9%53Q21G%O3731p0:1p0A1p0D1p0H1pUDQ61pU>Q61pUHQ71pU:Q91pW6Q;1pUJQ<1").
Proof.
intros l xs base k c i H Hb Hc ->. rewrite <- H. rewrite nth_error_firstn.
replace (Nat.ltb c k) with true by (symmetry; apply Nat.ltb_lt; lia).
rewrite nth_error_skipn. f_equal. lia.
Qed.
Lemma window_sub : ltac2:(TCodec.tc2 tcn__CJ_Spec_StrFun "QB'9'S9y8%211%411'M':'@&Ir4&L&R<r5%211r7%53<21%83=71r6%;3>21&R3z%2214'G&E%12<?%3218&QOr8&R9%11<%4231%H3JF1r;%G3ND1%J3OA1r:%J3Q1F1%M3Q2D1%O3Q241p081p0?1p0D1p0H1pUDQ61pUFQ61pU>Q71pUHQ81pU:Q:1pW6Q<1pUJQ=1").
Proof.
intros l xs base k c j i H Hb Hc ->. rewrite <- H.
rewrite skipn_firstn_comm, firstn_firstn, skipn_skipn by lia. f_equal; [lia|]. f_equal. lia.
Qed.
Lemma window_shift : ltac2:(TCodec.tc2 tcn__CJ_Spec_StrFun "QA'9'S9y8%211%411'M':'@&Ir3&L&R<r4%211r6%53<21%83=71r5%;3>21&R3z%2214'G%12;6&QOr7&R9%11:%4231%F3HA1&F%126A%E1?r:%H3O21%K3Q041r9%K3Q2G1%O3Q231p0:1p0A1p0D1p0H1pUDQ61pU>Q61pUHQ71pU:Q91pW6Q;1pUJQ<1").
Proof.
intros l xs base k c i H Hb Hc ->. rewrite <- H.
rewrite skipn_firstn_comm, skipn_skipn. f_equal. f_equal. lia.
Qed.
Lemma nth_error_first1 : ltac2:(TCodec.tc2 tcn__CJ_Spec_StrFun "Q0'9'S9y8%211%411':'@'<%115&QNr3r2%33921(4r1%22<1%:3841&Iu1&Lr4%23B;1%53C41(7(;%11F%33G?1%E3G51p0<1pW4J1pUDI1pUJK1").
Proof.
intros l i x H. destruct (nth_error_split _ _ _ H) as (pre & post & E & Hlen). rewrite E at 1.
rewrite skipn_app, skipn_all2, Hlen, Nat.sub_diag by lia. reflexivity.
Qed.
Lemma byte_range : ltac2:(TCodec.tc2 tcn__CJ_Spec_StrFun "?'S9y8%211'?&R3z&S<r1%2271%5241&R5+X0%2241%:241pTN<1").
Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as H. unfold bv_modulus in H. cbn in H. cbn. lia. Qed.
Lemma bv_wrap32_eq : ltac2:(TCodec.tc2 tcn__CJ_Spec_StrFun ">'M'@&S=yQ0r1%3221&R7&R:+2+Q0%3221%5271%;3<71pW:=1").
Proof. reflexivity. Qed.
Lemma bv_swrap32_eq : ltac2:(TCodec.tc2 tcn__CJ_Spec_StrFun "D'M'@&S;yQ0r1%3221&R;&R7&QO&R:+2+O%3221%5291+Q0%6251%9231%;215%A3B=1pW:C1").
Proof. reflexivity. Qed.
Lemma le_bytes_to_word4 : ltac2:(TCodec.tc2 tcn__CJ_Spec_StrFun "Q9'S9y8%211'@'M&S<yR0&Q1(7r4r3r2r1(;%11<%73=31%83>51%93?71%:3@91%<11%?2>1&QO%A2E=&R8+X0%D2H?%3221%6251+RPP0%H2LB%7221%:241+`PPP0%L2Q0E%;221%>241%Q13Q0@1pU8Q31pU6Q41pU4Q51pU2Q61").
Proof.
intros. unfold le_bytes_to_word. rewrite bytes_le_to_Z_le_val. cbn [map le_val].
pose proof (byte_range b0). pose proof (byte_range b1). pose proof (byte_range b2). pose proof (byte_range b3).
rewrite unsigned_lit by lia. lia.
Qed.
Lemma lw_unsigned4 : ltac2:(TCodec.tc2 tcn__CJ_Spec_StrFun "QL'S9y8%211'@'M&S<yR0&Q4yQ0&S:w&Q1(7r4r3r2r1(;%11@%73A31%83B51%93C71%:3D91%<11%?4B>@1%B3AC1%E2D1&QO%G2K?&R8+X0%J2NA%3221%6251+RPP0%N2Q2D%7221%:241+`PPP0%Q22Q6G%;221%>241&R;&R:+2+R0%3221+Q0%5241%7231&R0+T0%22=1%H241%K2=1%QD3QCM1pU8QF1pU6QG1pU4QH1pU2QI1").
Proof.
intros. rewrite sext_small, Z_to_bv_unsigned, signed_of_extract, le_bytes_to_word4 by reflexivity.
pose proof (byte_range b0). pose proof (byte_range b1). pose proof (byte_range b2). pose proof (byte_range b3).
rewrite bv_swrap32_eq. change (bv_wrap 64 ?x) with (x mod 2^64).
Z.div_mod_to_equations. lia.
Qed.
Lemma Z_to_le_bytes_to_Z : ltac2:(TCodec.tc2 tcn__CJ_Spec_StrFun "?'9'S9y8%211%411'@&O&8r1%2261&Q0%113%6231%83915pU<:1").
Proof.
induction bs as [|b bs IH]; [reflexivity|]. cbn [length Z_to_le_bytes bytes_le_to_Z].
pose proof (byte_range b) as Hb.
assert (HR : 0 <= bytes_le_to_Z bs). { rewrite bytes_le_to_Z_le_val. apply (proj1 (le_val_range _ (bytes_ok_map bs))). }
rewrite lor_shiftl8_add by lia.
f_equal.
- apply bv_eq. rewrite Z_to_bv_unsigned. change (bv_wrap 8 ?z) with (z mod 2^8)%Z. change (2^8) with 256.
replace (bv_unsigned b + 256 * bytes_le_to_Z bs) with (bv_unsigned b + bytes_le_to_Z bs * 256) by lia.
rewrite Z.mod_add by lia. apply Z.mod_small. lia.
- rewrite Z.shiftr_div_pow2 by lia. change (2^8) with 256.
replace (bv_unsigned b + 256 * bytes_le_to_Z bs) with (bv_unsigned b + bytes_le_to_Z bs * 256) by lia.
rewrite Z.div_add, Z.div_small by lia. cbn [Z.add]. exact IH.
Qed.
Lemma le4_of_mod32 : ltac2:(TCodec.tc2 tcn__CJ_Spec_StrFun "Q7'S9yR0%211'9y8%511%311'@':&8r1%2261u4%63521'M&R7&S<r3%22A1&R:+2+Q0%3221%8251&Q9&J%:1Fr2%34G>21%511%G3@71&Q=r4%211%K3L1Ap051p0G1pU<O1pW0Q41").
Proof.
intros v bs Hl Hv. unfold le4.
rewrite <- (Z_to_le_bytes_mod 4 _ 32) by (cbn; lia). change (2 ^ 32) with (2^32) in *. rewrite Hv.
rewrite <- bytes_le_to_Z_le_val, <- Hl. apply Z_to_le_bytes_to_Z.
Qed.
Lemma le1_of_mod8 : ltac2:(TCodec.tc2 tcn__CJ_Spec_StrFun "Q0'S9yR0%211y8%411'@'M&R7&S<r2%2291&R:+2+8%3221%8251r1%92>1%=3<31'9%11@&Q<r3%211(7(;%11F%33GB1%G3851p0;1pTNJ1pW0M1").
Proof.
intros v b Hv. unfold le1. rewrite <- (Z_to_le_bytes_mod 1 _ 8) by (cbn; lia). change (2^8) with (2^8) in *. rewrite Hv.
cbn. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.
Lemma le1_zxb : ltac2:(TCodec.tc2 tcn__CJ_Spec_StrFun "D'S9y8%211'@'9%113&Q<&S8yR0&S<r1%22:1%5241%711(7(;%11>%33?71%?3=51pTNA1").
Proof. intros b. apply le1_of_mod8. pose proof (byte_range b). rewrite unsigned_lit by lia. apply Z.mod_small. cbn. lia. Qed.
Lemma le4_lw : ltac2:(TCodec.tc2 tcn__CJ_Spec_StrFun "K'9'S9y8%211%411'@':&8r1%2261u4%63521&Q=&Q4yQ0yR0&S:w&Q1r2%211%546471%93871%;11%C3D15p0>1pW2F1").
Proof.
intros w Hl. destruct w as [|b0 [|b1 [|b2 [|b3 [|]]]]]; try (cbn in Hl; discriminate).
apply le4_of_mod32; [reflexivity|]. rewrite lw_unsigned4. cbn [map le_val].
pose proof (byte_range b0). pose proof (byte_range b1). pose proof (byte_range b2). pose proof (byte_range b3).
Z.div_mod_to_equations. lia.
Qed.
Lemma lor_add : ltac2:(TCodec.tc2 tcn__CJ_Spec_StrFun "Q1'M&R3zr1%3221'?r3%6251&R5&R:+2r2%3221%5271%9271'@&R7r5%928<%3221%53D1B&R4r6%2216&QO%1238%;3J31p071p0>1p0I1pUHN1pV0O1pUBQ01").
Proof.
intros hi lo k Hk Hlo Hhi.
assert (HL : Z.land hi lo = 0).
{ rewrite <- (Z.mod_small lo (2^k)) by lia. rewrite <- Z.land_ones by lia.
rewrite (Z.land_comm lo), Z.land_assoc, Z.land_ones, Hhi by lia. apply Z.land_0_l. }
pose proof (Z.add_lor_land hi lo). lia.
Qed.
Lemma lor_add' : ltac2:(TCodec.tc2 tcn__CJ_Spec_StrFun "Q2'M&R3zr1%3221'?r4%6251&R5&R:+2r2%3221%5271%9271'@&R7r3%9281%32=1%53D1B&R4r6r5%3221&QO%1243%<3K31p081p0?1p0J1pUHO1pUBQ01pV0Q11").
Proof. intros. rewrite Z.lor_comm, (lor_add hi lo k); lia. Qed.
Lemma land_single_bit : forall x k, 0 <= x -> 0 <= k ->
Z.land x (2^k) = if x mod 2^(k+1) <? 2^k then 0 else 2^k.
Proof.
intros x k Hx Hk.
assert (Hpk : 0 < 2^k < 2^(k+1)). { split; [apply Z.pow_pos_nonneg; lia| apply Z.pow_lt_mono_r; lia]. }
rewrite (Z.land_comm x), <- (land_mod_pow2_r (2^k) x (k+1)) by lia.
set (r := x mod 2^(k+1)).
assert (Hr : 0 <= r < 2^(k+1)) by (subst r; apply Z.mod_pos_bound; lia).
rewrite Z.pow_add_r in Hr by lia. change (2^1) with 2 in Hr.
destruct (Z.ltb_spec0 r (2^k)) as [Hl|Hl].
- rewrite Z.land_comm. apply zb_land_pow2_small; lia.
- replace r with (Z.lor (2^k) (r - 2^k)).
2:{ rewrite lor_add with (k := k); try lia. rewrite Z.mod_same; lia. }
rewrite Z.land_lor_distr_r, Z.land_diag, (Z.land_comm (2^k)), zb_land_pow2_small by lia. apply Z.lor_0_r.
Qed.
Lemma land_bit_2 : forall x, 0 <= x -> Z.land x 2 = if x mod 4 <? 2 then 0 else 2.
Proof. intros x Hx. exact (land_single_bit x 1 Hx ltac:(lia)). Qed.
Lemma land_bit_4 : forall x, 0 <= x -> Z.land x 4 = if x mod 8 <? 4 then 0 else 4.
Proof. intros x Hx. exact (land_single_bit x 2 Hx ltac:(lia)). Qed.
Lemma land_bit_8 : forall x, 0 <= x -> Z.land x 8 = if x mod 16 <? 8 then 0 else 8.
Proof. intros x Hx. exact (land_single_bit x 3 Hx ltac:(lia)). Qed.
Lemma land_bit_16 : forall x, 0 <= x -> Z.land x 16 = if x mod 32 <? 16 then 0 else 16.
Proof. intros x Hx. exact (land_single_bit x 4 Hx ltac:(lia)). Qed.
Lemma land_1 : ltac2:(TCodec.tc2 tcn__CJ_Spec_StrFun ";'M'@&R2r1+1%3221&R7+2%2251%83941pW4:1").
Proof. intros x. change 1 with (2^1 - 1) at 1. rewrite zb_land_mask by lia. reflexivity. Qed.
Lemma land_3 : ltac2:(TCodec.tc2 tcn__CJ_Spec_StrFun ";'M'@&R2r1+3%3221&R7+4%2251%83941pW4:1").
Proof. intros x. change 3 with (2^2 - 1). rewrite zb_land_mask by lia. reflexivity. Qed.
Lemma land_7 : ltac2:(TCodec.tc2 tcn__CJ_Spec_StrFun ";'M'@&R2r1+7%3221&R7+8%2251%83941pW4:1").
Proof. intros x. change 7 with (2^3 - 1). rewrite zb_land_mask by lia. reflexivity. Qed.
Lemma copied_upd_other : ltac2:(TCodec.tc2 tcn__CJ_Spec_StrFun "Q1'9'S9y8%211%411':&QDr5r4r3%43321'G%1243&E&8%12<6%3281r6%42?1%8231r8&Q?r7%231@?%B3417p061p0>1p0A1pW6H1pUDH1pV6I1pU<K1pV@L1").
Proof.
intros src bs p i xs [Hl Hf] Hi Hx. split.
- rewrite upd_bytes_length by lia. exact Hl.
- unfold upd_bytes. rewrite firstn_app, firstn_firstn by lia. replace (Nat.min p i) with p by lia.
rewrite firstn_length. replace (p - Nat.min i (length bs))%nat with 0%nat by lia. cbn. rewrite app_nil_r. exact Hf.
Qed.
Lemma firstn_S_nth : forall {X} (l : list X) p x, nth_error l p = Some x -> firstn (S p) l = firstn p l ++ [x].
Proof.
intros X l; induction l as [|a l IH]; intros [|p] x H; cbn in *; try discriminate.
- injection H as ->. reflexivity.
- rewrite (IH p x H). reflexivity.
Qed.
Lemma copied_S : ltac2:(TCodec.tc2 tcn__CJ_Spec_StrFun "Q3'9'S9y8%211%411':&QDr4r3r2%43321'@'<%11:&QN%13<87(4%12>8%73531r6%63A1=%52B=%;3921r7(3r5%211%E3481p061p0;1p0D1pW4L1pV6K1pU<M1pV@N1").
Proof.
intros src bs p x [Hl Hf] Hb Hs. split; [exact Hl|].
rewrite (firstn_S_nth bs p x Hb), (firstn_S_nth src p x Hs), Hf. reflexivity.
Qed.
Lemma upd_bytes_nth_same1 : ltac2:(TCodec.tc2 tcn__CJ_Spec_StrFun "O'9'S9y8%211%411':&Hr2&8r3%2271%5241'@'<%11;&QN&Q?r4(7(;%11A%33B>1%635=1%83D1>(4%12FB%>3<31p0@1pW4I1pUDH1pU<J1").
Proof.
intros bs i x Hi. rewrite upd_bytes_nth by (cbn; lia). cbn [length].
replace (Nat.leb i i && Nat.ltb i (i + 1))%bool with true. 2:{ symmetry. apply andb_true_iff. split; [apply Nat.leb_le| apply Nat.ltb_lt]; lia. }
rewrite Nat.sub_diag. reflexivity.
Qed.
Lemma upd_bytes_nth_after : ltac2:(TCodec.tc2 tcn__CJ_Spec_StrFun "Q4'9'S9y8%211%411':'G&Er1&8r3%2281%5241r2%8221&Hr5%82>1%3281'@'<%11B&QN&Q?r6%231?9r4%53H21%63I42%:3821p0<1p0A1pUFK1pUDL1pW6N1pU<O1").
Proof.
intros bs xs i j Hj Hi. rewrite upd_bytes_nth by lia.
replace (Nat.leb j i && Nat.ltb i (j + length xs))%bool with false; [reflexivity|].
symmetry. apply andb_false_iff. right. apply Nat.ltb_ge. lia.
Qed.

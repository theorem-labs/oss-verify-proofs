(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YM06 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0i YO0f YO0x YO0d YO0e.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UH00 UH03 UH02 UN3b YI06 UI5b YI09 YI08 YI0r UI1w UI5o UI21 UI5l
YI00 YI05 YI5a UIZs.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require UN0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Section t. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition hdr_src (i : Z) : Z * Z :=
if i =? 16 then (0, 2) else if i =? 17 then (1, 2) else if i =? 20 then (2, 4) else if i =? 21 then (3, 4)
else if i =? 24 then (4, 6) else if i =? 25 then (5, 6) else if i =? 28 then (6, 7)
else if i =? 26 then (7, 9) else if i =? 27 then (8, 9) else (0, 0).
Definition hdr_valk (ek : Z) (memc : word -> option byte) (pdata nb cur i : Z) : Z :=
let '(j, e) := hdr_src i in
if (0 <? e) && (e <=? ek) && (cur + e <=? nb) then byte_at memc (pdata + cur + j) else 0.
Definition hdr_val (memc : word -> option byte) (pdata nb cur i : Z) : Z := hdr_valk 9 memc pdata nb cur i.
Definition hdr_rv (nb cur e : Z) : Z := if cur + e <=? nb then 0 else 2 ^ 64 - 1.
Definition hdr_cur (nb cur e : Z) : Z := if cur + e <=? nb then cur + e else nb.
Definition hdr_pc (memc : word -> option byte) (pdata nb cur : Z) : Z :=
if Z.land (hdr_val memc pdata nb cur 16) 1 =? 0 then IMGPC else PALPC.
Definition ss_rh : sstate :=
mkSS ubs0_A_read_frameconfig sr_atoms
[ YP09.mkRegion (Some 2%nat) (-RFC_FRAME) 0 (-RFC_FRAME) 0 [] ;
YP09.mkRegion (Some 11%nat) 0 32 0 32 [] ]
None
(mkFacts [ (2%nat, mkAF (CEIL_MIN + ALLOC_STACK) (2^63) 4); (11%nat, mkAF CEIL_MIN (2^63) 3) ] [] []).
Definition rh_reads : list (Z * Z * Z * Z) := [(16, 2, 0, 2); (20, 2, 2, 4); (24, 2, 4, 6); (28, 1, 6, 7); (26, 2, 7, 9)].
Lemma rh_reads_shape : forall off n ep ek, In (off, n, ep, ek) rh_reads ->
ek = ep + n /\ 0 < n /\ 0 <= ep /\ 16 <= off /\ off + n <= 32.
Proof using.
intros off n ep ek Hin. cbv [rh_reads In] in Hin.
destruct Hin as [Hq|[Hq|[Hq|[Hq|[Hq|[]]]]]]; injection Hq as <- <- <- <-; lia.
Qed.
Lemma rh_win : forall off n ep ek, In (off, n, ep, ek) rh_reads -> forall memc pdata nb cur i, 0 <= i < 32 ->
(off <= i < off + n -> hdr_valk ek memc pdata nb cur i = (if cur + ek <=? nb then byte_at memc (pdata + cur + (ep + (i - off))) else 0) /\
hdr_valk ep memc pdata nb cur i = 0) /\
(~ (off <= i < off + n) -> hdr_valk ek memc pdata nb cur i = hdr_valk ep memc pdata nb cur i).
Proof using.
intros off n ep ek Hin memc pdata nb cur i Hi. cbv [rh_reads In] in Hin.
destruct Hin as [Hq|[Hq|[Hq|[Hq|[Hq|[]]]]]]; injection Hq as <- <- <- <-;
unfold hdr_valk, hdr_src;
repeat match goal with |- context [if ?x =? ?c then _ else _] => is_var x; destruct (Z.eqb_spec x c); cbv beta iota end;
subst; (split; [intro Hw; split | intro Hw]); cbn; first [reflexivity | exfalso; lia].
Qed.
Definition rh_inv (memc m : word -> option byte) (Bb : list (Z * Z)) (sp st dst pdata nb cur ek : Z) : Prop :=
(forall i, 0 <= i < 32 -> mbyte ubs0segs m (dst + i) = Some (Z_to_bv 8 (hdr_valk ek memc pdata nb cur i))) /\
word_mem ubs0segs m (st + 16) (hdr_cur nb cur ek) /\
(forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp - RFC_DEPTH <= a < sp) -> ~ (dst <= a < dst + 32) ->
~ (st + 16 <= a < st + 24) -> mbyte ubs0segs m a = mbyte ubs0segs memc a) /\
(forall b n i, In (b, n) Bb -> 0 <= i < n -> mbyte ubs0segs m (b + i) = mbyte ubs0segs memc (b + i)).
Lemma rh_mbyte_keep : forall (m m' : word -> option byte) a, 0 <= a < 2 ^ 64 ->
(forall x : word, bv_unsigned x = a -> m' x = m x) -> mbyte ubs0segs m' a = mbyte ubs0segs m a.
Proof using.
intros m m' a Ha H. unfold mbyte. rewrite (H (Z_to_bv 64 a)) by (apply unsigned_lit_small; lia). reflexivity.
Qed.
Lemma rh_word_keep : forall (m m' : word -> option byte) a v,
(forall k, 0 <= k < 8 -> mbyte ubs0segs m' (a + k) = mbyte ubs0segs m (a + k)) ->
word_mem ubs0segs m a v -> word_mem ubs0segs m' a v.
Proof using.
intros m m' a v H W k Hk. rewrite H by lia. apply W. exact Hk.
Qed.
Lemma rh_inv_frame : forall memc m m' Bb sp st dst pdata nb cur ek lo,
rh_inv memc m Bb sp st dst pdata nb cur ek ->
(forall x : word, ~ (lo <= bv_unsigned x < sp) -> m' x = m x) ->
sp - RFC_DEPTH <= lo -> alloc_ceiling <= lo -> lo <= sp -> sp <= dst -> sp <= st -> dst + 32 < 2 ^ 64 -> st + 24 < 2 ^ 64 ->
(forall b n i, In (b, n) Bb -> 0 <= i < n -> 0 <= b + i < alloc_ceiling) ->
rh_inv memc m' Bb sp st dst pdata nb cur ek.
Proof using.
intros memc m m' Bb sp st dst pdata nb cur ek lo (HD & HC & HF & HB) Hfr H1 H2 H0 H3 H4 H5 H6 HBr.
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HRDv : RD_FRAME = 32) by reflexivity. assert (HDPv : RFC_DEPTH = 8256) by reflexivity.
split; [|split; [|split]].
- intros i Hi. rewrite <- (HD i Hi). apply rh_mbyte_keep; [lia|]. intros x Hx. apply Hfr. lia.
- eapply rh_word_keep; [|exact HC]. intros k Hk. apply rh_mbyte_keep; [lia|]. intros x Hx. apply Hfr. lia.
- intros a Ha Hn1 Hn2 Hn3. rewrite <- (HF a Ha Hn1 Hn2 Hn3). apply rh_mbyte_keep; [lia|]. intros x Hx. apply Hfr. lia.
- intros b n i Hb Hi. rewrite <- (HB b n i Hb Hi). specialize (HBr b n i Hb Hi). apply rh_mbyte_keep; [lia|]. intros x Hx. apply Hfr. lia.
Qed.
Lemma rh_payload_byte : forall (memc m : word -> option byte) Bb pdata nb x,
(forall b n i, In (b, n) Bb -> 0 <= i < n -> mbyte ubs0segs m (b + i) = mbyte ubs0segs memc (b + i)) ->
In (pdata, nb) Bb -> present memc (pdata + x) -> 0 <= x < nb ->
mbyte ubs0segs m (pdata + x) = Some (Z_to_bv 8 (byte_at memc (pdata + x))).
Proof using.
intros memc m Bb pdata nb x HB Hpd [b Hb] Hx. rewrite (HB pdata nb x Hpd Hx). unfold byte_at, mbyte. rewrite Hb.
rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.
Lemma rh_inv_rd : forall memc m m2 Bb sp st dst pdata nb cur spc off n ep ek r10,
rh_inv memc m Bb sp st dst pdata nb cur ep ->
(forall x : word, ~ (spc - RD_FRAME <= bv_unsigned x < spc) -> ~ (dst + off <= bv_unsigned x < dst + off + n) ->
~ (st + 16 <= bv_unsigned x < st + 24) -> m2 x = m x) ->
((hdr_cur nb cur ep + n <= nb /\ r10 = Z_to_bv 64 0 /\ word_mem ubs0segs m2 (st + 16) (hdr_cur nb cur ep + n) /\
(forall i, 0 <= i < n -> mbyte ubs0segs m2 (dst + off + i) = mbyte ubs0segs m (pdata + hdr_cur nb cur ep + i))) \/
(nb < hdr_cur nb cur ep + n /\ r10 = Z_to_bv 64 (2 ^ 64 - 1) /\ word_mem ubs0segs m2 (st + 16) nb /\
(forall i, 0 <= i < n -> mbyte ubs0segs m2 (dst + off + i) = mbyte ubs0segs m (dst + off + i)))) ->
In (off, n, ep, ek) rh_reads ->
(forall x, 0 <= x < nb -> present memc (pdata + x)) -> In (pdata, nb) Bb ->
sp - RFC_DEPTH <= spc - RD_FRAME -> alloc_ceiling <= spc - RD_FRAME -> spc <= sp -> sp <= dst -> sp <= st ->
(st + 24 <= dst \/ dst + 32 <= st) -> dst + 32 < 2 ^ 64 -> st + 24 < 2 ^ 64 -> 0 <= cur <= nb ->
(forall b n i, In (b, n) Bb -> 0 <= i < n -> 0 <= b + i < alloc_ceiling) ->
rh_inv memc m2 Bb sp st dst pdata nb cur ek /\ r10 = Z_to_bv 64 (hdr_rv nb cur ek).
Proof using.
intros memc m m2 Bb sp st dst pdata nb cur spc off n ep ek r10 (HD & HC & HF & HB) Hout Hcase Hin Hpres Hpd
H1 H2 H3 H4 H5 Hsd H6 H7 Hcur HBr.
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HRDv : RD_FRAME = 32) by reflexivity. assert (HDPv : RFC_DEPTH = 8256) by reflexivity.
destruct (rh_reads_shape off n ep ek Hin) as (-> & Hn & Hep & Hoff & Hoffn).
assert (Hk : forall a, 0 <= a < 2 ^ 64 -> ~ (spc - RD_FRAME <= a < spc) -> ~ (dst + off <= a < dst + off + n) ->
~ (st + 16 <= a < st + 24) -> mbyte ubs0segs m2 a = mbyte ubs0segs m a).
{ intros a Ha Hn1 Hn2 Hn3. apply rh_mbyte_keep; [exact Ha|]. intros x Hx. apply Hout; lia. }
unfold hdr_cur, hdr_rv in *.
destruct Hcase as [(Hok & -> & Wc & Hby) | (Hbad & -> & Wc & Hby)].
- assert (Hle : cur + ep <= nb) by (destruct (Z.leb_spec (cur + ep) nb); lia).
rewrite (proj2 (Z.leb_le _ _) Hle) in Hok, Wc, Hby.
assert (Hle2 : cur + (ep + n) <= nb) by lia.
rewrite (proj2 (Z.leb_le _ _) Hle2).
split; [|reflexivity]. split; [|split; [|split]].
+ intros i Hi. destruct (rh_win off n ep (ep + n) Hin memc pdata nb cur i Hi) as [Hw1 Hw2].
destruct (Z_le_gt_dec off i) as [Hlo|Hlo]; [destruct (Z_lt_ge_dec i (off + n)) as [Hhi|Hhi]|].
* destruct (Hw1 (conj Hlo Hhi)) as [-> _]. rewrite (proj2 (Z.leb_le _ _) Hle2).
replace (dst + i) with (dst + off + (i - off)) by lia. rewrite (Hby (i - off)) by lia.
replace (pdata + (cur + ep) + (i - off)) with (pdata + (cur + (ep + (i - off)))) by lia.
replace (pdata + cur + (ep + (i - off))) with (pdata + (cur + (ep + (i - off)))) by lia.
apply (rh_payload_byte memc m Bb pdata nb); [exact HB | exact Hpd | apply Hpres; lia | lia].
* rewrite (Hw2 ltac:(lia)). rewrite <- (HD i Hi). apply Hk; lia.
* rewrite (Hw2 ltac:(lia)). rewrite <- (HD i Hi). apply Hk; lia.
+ unfold hdr_cur. rewrite (proj2 (Z.leb_le _ _) Hle2). replace (cur + ep + n) with (cur + (ep + n)) in Wc by lia. exact Wc.
+ intros a Ha Hn1 Hn2 Hn3. rewrite <- (HF a Ha Hn1 Hn2 Hn3). apply Hk; lia.
+ intros b k i Hb Hi. rewrite <- (HB b k i Hb Hi). specialize (HBr b k i Hb Hi). apply Hk; lia.
- assert (Hgt : nb < cur + (ep + n)) by (destruct (Z.leb_spec (cur + ep) nb); lia).
rewrite (proj2 (Z.leb_gt _ _) Hgt).
split; [|reflexivity]. split; [|split; [|split]].
+ intros i Hi. destruct (rh_win off n ep (ep + n) Hin memc pdata nb cur i Hi) as [Hw1 Hw2].
destruct (Z_le_gt_dec off i) as [Hlo|Hlo]; [destruct (Z_lt_ge_dec i (off + n)) as [Hhi|Hhi]|].
* destruct (Hw1 (conj Hlo Hhi)) as [-> Hz]. rewrite (proj2 (Z.leb_gt _ _) Hgt).
replace (dst + i) with (dst + off + (i - off)) by lia. rewrite (Hby (i - off)) by lia.
replace (dst + off + (i - off)) with (dst + i) by lia. rewrite (HD i Hi), Hz. reflexivity.
* rewrite (Hw2 ltac:(lia)). rewrite <- (HD i Hi). apply Hk; lia.
* rewrite (Hw2 ltac:(lia)). rewrite <- (HD i Hi). apply Hk; lia.
+ unfold hdr_cur. rewrite (proj2 (Z.leb_gt _ _) Hgt). exact Wc.
+ intros a Ha Hn1 Hn2 Hn3. rewrite <- (HF a Ha Hn1 Hn2 Hn3). apply Hk; lia.
+ intros b k i Hb Hi. rewrite <- (HB b k i Hb Hi). specialize (HBr b k i Hb Hi). apply Hk; lia.
Qed.
Lemma rh_valk0 : forall memc pdata nb cur i, hdr_valk 0 memc pdata nb cur i = 0.
Proof using.
intros memc pdata nb cur i. unfold hdr_valk. destruct (hdr_src i) as [j e].
destruct (0 <? e) eqn:H1; [|reflexivity]. destruct (e <=? 0) eqn:H2; [|rewrite andb_false_r; reflexivity].
apply Z.ltb_lt in H1. apply Z.leb_le in H2. lia.
Qed.
Lemma rh_word0_byte : forall (m : word -> option byte) a j, word_mem ubs0segs m a 0 -> 0 <= j < 8 ->
mbyte ubs0segs m (a + j) = Some (Z_to_bv 8 0).
Proof using.
intros m a j W Hj. specialize (W (Z.to_nat j) ltac:(lia)). rewrite Z2Nat.id in W by lia. rewrite W.
unfold le_byte. rewrite Z.mod_0_l by (apply Z.pow_nonzero; lia). rewrite Z.shiftr_0_l. reflexivity.
Qed.
Lemma rh_inv_words : forall memc m Bb sp st dst pdata nb cur ek,
rh_inv memc m Bb sp st dst pdata nb cur ek -> word_mem ubs0segs memc st pdata -> word_mem ubs0segs memc (st + 8) nb ->
sp <= st -> st + 24 < 2 ^ 64 -> (st + 24 <= dst \/ dst + 32 <= st) -> alloc_ceiling <= sp ->
word_mem ubs0segs m st pdata /\ word_mem ubs0segs m (st + 8) nb.
Proof using.
intros memc m Bb sp st dst pdata nb cur ek (HD & HC & HF & HB) Wp Wn H1 H2 H3 H4.
assert (HDPv : RFC_DEPTH = 8256) by reflexivity.
split; (eapply rh_word_keep; [|eassumption]); intros k Hk; apply HF; lia.
Qed.
Lemma rh_add_region : forall segs E ss ms r,
st_ok segs E ss ms -> region_wf r = true -> region_ok segs E (ms_mem ms) r -> all_disjoint E r (ss_mem ss) ->
st_ok segs E (mkSS (ss_pc ss) (ss_regs ss) (r :: ss_mem ss) (ss_resv ss) (ss_facts ss)) ms.
Proof using.
intros segs E ss ms r (H1 & H2 & H3 & H4 & H5 & H6 & H7 & (Hwf & Hok & Hpd) & H9) Hrwf Hr Hd.
unfold st_ok; cbn. repeat (split; [assumption|]). split; [|exact H9].
split; [cbn; rewrite Hrwf, Hwf; reflexivity|]. split; [constructor; assumption|]. split; assumption.
Qed.
Definition rh_b16r : YP09.region := YP09.mkRegion (Some 11%nat) 16 17 16 16 [mkChunk 16 (CVal 1 (SOff 32 0))].
Lemma rh_valk_range : forall ek memc pdata nb cur i, 0 <= hdr_valk ek memc pdata nb cur i < 256.
Proof using.
intros ek memc pdata nb cur i. unfold hdr_valk. destruct (hdr_src i) as [j e].
destruct ((0 <? e) && (e <=? ek) && (cur + e <=? nb)); [apply byte_at_range | lia].
Qed.
Lemma rh_le_byte1 : forall v, 0 <= v < 256 -> le_byte v 1 0 = v.
Proof using.
intros v Hv. unfold le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite (Z.mod_small v 256) by lia. rewrite (Z.mod_small v 256) by lia. reflexivity.
Qed.
Lemma rh_attr_U : forall E b, ew E 32 = Z_to_bv 64 b -> 0 <= b < 256 ->
U E (SAlu ALU_AND (SExt false 8 (SOff 32 0)) (SLit 1)) = Z.land b 1.
Proof using.
intros E b Hb Hr. rewrite U_SAlu, U_SExt, U_SLit, (U_atom E 32 b Hb) by lia. cbv beta iota.
change (2 ^ Z.of_N 8) with 256. rewrite (Z.mod_small b 256) by lia.
change (zcanon 1) with 1. rewrite (zcanon_id b) by (unfold M64; lia).
cbn [zalu_raw].
pose proof (Z.land_ones b 1 ltac:(lia)) as Hl. change (Z.ones 1) with 1 in Hl. change (2 ^ 1) with 2 in Hl.
rewrite Hl. apply zcanon_id. unfold M64. pose proof (Z.mod_pos_bound b 2 ltac:(lia)). lia.
Qed.
Section S.
Variable API : AllocAPI ubs0_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs0_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs0_msyms MR.
Definition hdr_post (regs : bvmap 5 word) (STK sp0 : Z) (FP : list (Z * Z)) L A mem md Lc Ac
(Bb : list (Z * Z)) (st dst N pdata nb cur : Z) (memc : word -> option byte) (mdc : Model) (c' : config) : Prop :=
exists (regs1 : bvmap 5 word) (mem1 : word -> option byte),
c' = mkCfg (mkst regs1 (Z_to_bv 64 (hdr_pc memc pdata nb cur)) mem1 (seg_rom ubs0segs)) mdc /\
journal ubs0_msyms MR STK sp0 FP L A mem md Lc Ac mem1 mdc /\
getr regs1 2 = Z_to_bv 64 (spZ regs - RFC_FRAME) /\ getr regs1 3 = getr regs 3 /\ getr regs1 4 = getr regs 4 /\
getr regs1 8 = Z_to_bv 64 dst /\ getr regs1 9 = Z_to_bv 64 N /\ getr regs1 18 = Z_to_bv 64 st /\
getr regs1 19 = Z_to_bv 64 (dst + 26) /\ getr regs1 20 = Z_to_bv 64 (hdr_rv nb cur 9) /\
getr regs1 22 = getr regs 22 /\ getr regs1 23 = getr regs 23 /\ getr regs1 24 = getr regs 24 /\
getr regs1 25 = getr regs 25 /\ getr regs1 26 = getr regs 26 /\ getr regs1 27 = getr regs 27 /\
word_mem ubs0segs mem1 (spZ regs - 8) (bv_unsigned (getr regs 1)) /\
word_mem ubs0segs mem1 (spZ regs - 16) (bv_unsigned (getr regs 8)) /\
word_mem ubs0segs mem1 (spZ regs - 24) (bv_unsigned (getr regs 9)) /\
word_mem ubs0segs mem1 (spZ regs - 32) (bv_unsigned (getr regs 18)) /\
word_mem ubs0segs mem1 (spZ regs - 40) (bv_unsigned (getr regs 19)) /\
word_mem ubs0segs mem1 (spZ regs - 48) (bv_unsigned (getr regs 20)) /\
word_mem ubs0segs mem1 (spZ regs - 56) (bv_unsigned (getr regs 21)) /\
word_mem ubs0segs mem1 st pdata /\ word_mem ubs0segs mem1 (st + 8) nb /\
word_mem ubs0segs mem1 (st + 16) (hdr_cur nb cur 9) /\
(forall i, 0 <= i < 32 -> mbyte ubs0segs mem1 (dst + i) = Some (Z_to_bv 8 (hdr_val memc pdata nb cur i))) /\
(forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (spZ regs - RFC_DEPTH <= a < spZ regs) -> ~ (dst <= a < dst + 32) ->
~ (st + 16 <= a < st + 24) -> mbyte ubs0segs mem1 a = mbyte ubs0segs memc a) /\
(forall b m i, In (b, m) Bb -> 0 <= i < m -> mbyte ubs0segs mem1 (b + i) = mbyte ubs0segs memc (b + i)).
Lemma rfc_hdr_x : forall STK sp0 FP L A mem md Lc Ac memc mdc (regs : bvmap 5 word) (Bb : list (Z * Z)) (st dst N pdata nb cur : Z),
journal ubs0_msyms MR STK sp0 FP L A mem md Lc Ac memc mdc ->
Permutation (blocks Lc Ac) Bb -> In (pdata, nb) Bb ->
YK0s.ret_ok (getr regs 1) ->
getr regs 10 = Z_to_bv 64 st -> getr regs 11 = Z_to_bv 64 dst -> getr regs 12 = Z_to_bv 64 N ->
spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - RFC_STK -> spZ regs <= st -> st + 24 <= sp0 ->
spZ regs <= dst -> dst + 32 <= sp0 -> (st + 24 <= dst \/ dst + 32 <= st) -> st mod 8 = 0 -> dst mod 8 = 0 -> sp0 < 2 ^ 63 ->
0 <= cur <= nb -> 0 < nb ->
word_mem ubs0segs memc st pdata -> word_mem ubs0segs memc (st + 8) nb -> word_mem ubs0segs memc (st + 16) cur ->
SR ubs0segs (mkCfg (mkst regs (Z_to_bv 64 ubs0_A_read_frameconfig) memc (seg_rom ubs0segs)) mdc)
(hdr_post regs STK sp0 FP L A mem md Lc Ac Bb st dst N pdata nb cur memc mdc).
Proof using IMG LAWS.
intros STK sp0 FP L A mem md Lc Ac memc mdc regs Bb st dst N pdata nb cur HJ HBc Hpd Hra G10 G11 G12
Hal16 Hwlo Hst1 Hst2 Hdst1 Hdst2 Hsd Hst8 Hdst8 H63 Hcur Hnb Wp Wn Wc.
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HASv : ALLOC_STACK = 8192) by reflexivity.
assert (HFRv : RFC_FRAME = 64) by reflexivity. assert (HDPv : RFC_DEPTH = 8256) by reflexivity.
assert (HSTv : RFC_STK = 8272) by reflexivity. assert (HRDv : RD_FRAME = 32) by reflexivity.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HH.
pose proof HJ as (_ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _).
set (sp := spZ regs) in *.
assert (Hsp0 : 0 <= sp) by (unfold sp, spZ; apply bv_unsigned_in_range).
set (b16 := hdr_val memc pdata nb cur 16).
set (E := Ereg regs [Z_to_bv 64 b16]).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HE32 : ew E 32 = Z_to_bv 64 b16) by reflexivity.
assert (HE2 : bv_unsigned (ew E 2) = sp) by (rewrite (HE 2%nat 2%bv eq_refl); reflexivity).
assert (HE11 : bv_unsigned (ew E 11) = dst) by (rewrite (HE 11%nat 11%bv eq_refl), G11; apply unsigned_lit_small; lia).
assert (HE10 : bv_unsigned (ew E 10) = st) by (rewrite (HE 10%nat 10%bv eq_refl), G10; apply unsigned_lit_small; lia).
assert (HS : st_ok ubs0segs E ss_rh (mkst regs (Z_to_bv 64 ubs0_A_read_frameconfig) memc (seg_rom ubs0segs))).
{ unfold ss_rh. subst E. apply entry_st_ok_full.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor]].
+ apply (region_ok_stack ubs0segs _ memc 2 sp); [exact HE2 | lia | lia |].
intros a Ha. apply (journal_stack_w _ _ _ _ _ _ _ _ _ _ _ _ _ HJ). lia.
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HE11.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (journal_stack_w _ _ _ _ _ _ _ _ _ _ _ _ _ HJ). lia. }
apply Forall_nil.
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val].
rewrite HE2, HE11. repeat split; lia.
- split; [|split; exact I].
cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite HE2, HE11. change (2 ^ 4) with 16. change (2 ^ 3) with 8.
repeat split; lia. }
change memc with (ms_mem (mkst regs (Z_to_bv 64 ubs0_A_read_frameconfig) memc (seg_rom ubs0segs))) in HJ.
jrun_to LAWS ubs0tbl_ok HS HJ ubs0_A_readdata.
{ wr_norm. eapply wr_ok_cons_win; [reflexivity | exact HE2 | cbn [r_wlo r_whi]; intros _; lia |].
eapply wr_ok_cons_win; [reflexivity | exact HE11 | cbn [r_wlo r_whi]; intros _; lia |]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF. rename HF into HF0.
assert (HBr : forall b n i, In (b, n) Bb -> 0 <= i < n -> 0 <= b + i < alloc_ceiling).
{ intros b n i Hb Hi. assert (Hbc : In (b, n) (blocks Lc Ac)) by (eapply Permutation_in; [apply Permutation_sym; exact HBc | exact Hb]).
destruct (heap_blocks _ _ LAWS Lc Ac memc mdc b n i HH Hbc Hi) as (_ & Hb0 & Hb1 & _). lia. }
assert (Hpdc : In (pdata, nb) (blocks Lc Ac)) by (eapply Permutation_in; [apply Permutation_sym; exact HBc | exact Hpd]).
destruct (heap_blocks_range _ _ LAWS Lc Ac memc mdc pdata nb HH Hpdc ltac:(lia)) as (Hp0 & Hp1 & _).
assert (Hpres : forall x, 0 <= x < nb -> present memc (pdata + x)).
{ intros x Hx. exact (proj1 (heap_blocks _ _ LAWS Lc Ac memc mdc pdata nb x HH Hpdc Hx)). }
lazymatch type of HS with st_ok _ _ _ ?ms1 =>
assert (HF0' : forall x : word, ~ (sp - 64 <= bv_unsigned x < sp) -> ~ (dst <= bv_unsigned x < dst + 32) -> ms_mem ms1 x = memc x);
[ intros x Hx1 Hx2; apply HF0; intros (r & Hr & Hw); cbv [In] in Hr;
destruct Hr as [<-|[<-|[]]]; cbn [r_base r_wlo r_whi base_val] in Hw; rewrite ?HE2, ?HE11 in Hw; lia |];
assert (HI1 : rh_inv memc (ms_mem ms1) Bb sp st dst pdata nb cur 0);
[| assert (Wpn : word_mem ubs0segs (ms_mem ms1) st pdata /\ word_mem ubs0segs (ms_mem ms1) (st + 8) nb)
by (apply (rh_inv_words memc _ Bb sp st dst pdata nb cur 0 HI1 Wp Wn); lia) ] end.
{ split; [|split; [|split]].
- intros i Hi. rewrite rh_valk0.
assert (W0 : forall off, In off [0; 8; 16; 24] -> word_mem ubs0segs (ms_mem ms) (dst + off) 0).
{ intros off Hoff. cbv [In] in Hoff.
destruct Hoff as [<-|[<-|[<-|[<-|[]]]]];
eapply (st_chunk_word _ _ _ 1%nat _ 11%nat _ (SLit 0) dst 0 HS);
first [reflexivity | exact HE11 | lia | solve [cbv; auto 12]]. }
destruct (Z_lt_ge_dec i 8); [|destruct (Z_lt_ge_dec i 16); [|destruct (Z_lt_ge_dec i 24)]].
+ replace (dst + i) with (dst + 0 + i) by lia. apply rh_word0_byte; [apply W0; cbv; auto 8 | lia].
+ replace (dst + i) with (dst + 8 + (i - 8)) by lia. apply rh_word0_byte; [apply W0; cbv; auto 8 | lia].
+ replace (dst + i) with (dst + 16 + (i - 16)) by lia. apply rh_word0_byte; [apply W0; cbv; auto 8 | lia].
+ replace (dst + i) with (dst + 24 + (i - 24)) by lia. apply rh_word0_byte; [apply W0; cbv; auto 8 | lia].
- unfold hdr_cur. rewrite Z.add_0_r, (proj2 (Z.leb_le _ _) (proj2 Hcur)).
eapply rh_word_keep; [|exact Wc]. intros k Hk. apply rh_mbyte_keep; [lia|]. intros x Hx. apply HF0'; lia.
- intros a Ha Hn1 Hn2 Hn3. apply rh_mbyte_keep; [lia|]. intros x Hx. apply HF0'; lia.
- intros b n i Hb Hi. specialize (HBr b n i Hb Hi). apply rh_mbyte_keep; [lia|]. intros x Hx. apply HF0'; lia. }
jreg HS (10%bv:reg) as M10. rewrite (HE 10%nat 10%bv eq_refl), G10 in M10.
jreg HS (11%bv:reg) as M11. rewrite HE11 in M11.
jreg HS (12%bv:reg) as M12.
jreg HS (2%bv:reg) as M2. rewrite HE2 in M2. replace (sp + -64) with (sp - 64) in M2 by lia.
jreg HS (1%bv:reg) as M1.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HHk.
eapply SR_bind.
{ eapply (jreaddata API IMG _ _ _ STK sp0 FP L A mem md Lc Ac mdc st (dst + 16) 2 pdata nb (hdr_cur nb cur 0) (sp - 64)).
- exact HS. - reflexivity. - reflexivity. - exact HJ.
- exact M10. - exact M11. - exact M12. - exact M2.
- replace (sp - 64) with (sp + (-4) * 16) by lia. rewrite Z.mod_add by lia. exact Hal16.
- rewrite HRDv; lia. - lia. - exact H63.
- exact M1. - apply ret_ok_even; vm_compute; reflexivity.
- lia. - lia. - exact Hst8.
- exact (proj1 Wpn). - exact (proj2 Wpn). - exact (proj1 (proj2 HI1)).
- lia. - unfold hdr_cur; destruct (Z.leb_spec (cur + 0) nb); lia. - lia. - lia. - lia. - intros; lia.
- intros j Hj. exact (proj1 (heap_blocks _ _ LAWS Lc Ac _ mdc pdata nb j HHk Hpdc Hj)).
- lia. - lia.
- intros i Hi. apply UN0d.writable_off_img_present; [lia | unfold UN0d.in_img1; lia |].
apply (journal_stack_w _ _ _ _ _ _ _ _ _ _ _ _ _ HJ). lia.
- intros a Ha. unfold wr_byte. left. lia.
- intros a Ha. unfold wr_byte. left. lia.
- right. lia. - right. lia. - intros _. left. rewrite HRDv. lia. - intros _. left. lia.
- destruct Hsd; [right|left]; lia. - intros _. right. lia. }
cbv beta. intros c' (regs2 & mem2 & -> & HJ2 & HP2 & Hout2 & Hgr2 & Hcase2).
destruct (rh_inv_rd memc _ mem2 Bb sp st dst pdata nb cur (sp - 64) 16 2 0 2 (getr regs2 10) HI1 Hout2 Hcase2
ltac:(cbv; auto 8) Hpres Hpd ltac:(rewrite HRDv; lia) ltac:(rewrite HRDv; lia) ltac:(lia) Hdst1 Hst1 Hsd ltac:(lia) ltac:(lia) Hcur HBr)
as [HI2 Hr2].
jafter_call2 HS 33%nat regs2 mem2 HP2 (-64) (@nil nat) HS2.
match type of HS2 with ?P -> _ => assert (HK : P); [|specialize (HS2 HK)] end.
{ constructor; [|constructor].
eapply region_kept_rd; [exact Hout2 | exact Hgr2 | ..]; cbn [r_base r_lo r_hi r_wlo r_whi base_val]; ew_havocF; rewrite ?HE2, ?HRDv; lia. }
clear HS HK. rename HS2 into HS.
jreg HS (10%bv:reg) as Q2. cbn [ms_regs mkst] in Q2. rewrite Hr2 in Q2.
jrun_to LAWS ubs0tbl_ok HS HJ2 ubs0_A_readdata.
{ wr_norm. eapply wr_ok_cons_win; [reflexivity | ew_havocF; exact HE2 | cbn [r_wlo r_whi]; intros _; lia |]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF. rename HF into HF2.
lazymatch type of HS with st_ok _ _ _ ?ms1 =>
assert (HIc2 : rh_inv memc (ms_mem ms1) Bb sp st dst pdata nb cur 2)
by (apply (rh_inv_frame memc mem2 _ Bb sp st dst pdata nb cur 2 (sp - 64) HI2);
[ intros x Hx; apply HF2; intros (r & Hr & Hw); cbv [In] in Hr; destruct Hr as [<-|[]];
cbn [r_base r_wlo r_whi base_val] in Hw; revert Hw; ew_havocF; rewrite HE2; intro Hw; lia
| lia | lia | lia | exact Hdst1 | exact Hst1 | lia | lia | exact HBr ]);
assert (Wpn2 : word_mem ubs0segs (ms_mem ms1) st pdata /\ word_mem ubs0segs (ms_mem ms1) (st + 8) nb)
by (apply (rh_inv_words memc _ Bb sp st dst pdata nb cur 2 HIc2 Wp Wn); lia) end.
jreg HS (10%bv:reg) as M10_2. rewrite (HE 10%nat 10%bv eq_refl), G10 in M10_2.
jreg HS (11%bv:reg) as M11_2. rewrite HE11 in M11_2.
jreg HS (12%bv:reg) as M12_2.
jreg HS (2%bv:reg) as M2_2. rewrite HE2 in M2_2. replace (sp + -64) with (sp - 64) in M2_2 by lia.
jreg HS (1%bv:reg) as M1_2.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HHk2.
eapply SR_bind.
{ eapply (jreaddata API IMG _ _ _ STK sp0 FP L A mem md Lc Ac mdc st (dst + 20) 2 pdata nb (hdr_cur nb cur 2) (sp - 64)).
- exact HS. - reflexivity. - reflexivity. - exact HJ2.
- exact M10_2. - exact M11_2. - exact M12_2. - exact M2_2.
- replace (sp - 64) with (sp + (-4) * 16) by lia. rewrite Z.mod_add by lia. exact Hal16.
- rewrite HRDv; lia. - lia. - exact H63.
- exact M1_2. - apply ret_ok_even; vm_compute; reflexivity.
- lia. - lia. - exact Hst8.
- exact (proj1 Wpn2). - exact (proj2 Wpn2). - exact (proj1 (proj2 HIc2)).
- lia. - unfold hdr_cur; destruct (Z.leb_spec (cur + 2) nb); lia. - lia. - lia. - lia. - intros; lia.
- intros j Hj. exact (proj1 (heap_blocks _ _ LAWS Lc Ac _ mdc pdata nb j HHk2 Hpdc Hj)).
- lia. - lia.
- intros i Hi. apply UN0d.writable_off_img_present; [lia | unfold UN0d.in_img1; lia |].
apply (journal_stack_w _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2). lia.
- intros a Ha. unfold wr_byte. left. lia.
- intros a Ha. unfold wr_byte. left. lia.
- right. lia. - right. lia. - intros _. left. rewrite HRDv. lia. - intros _. left. lia.
- destruct Hsd; [right|left]; lia. - intros _. right. lia. }
cbv beta. intros c' (regs3 & mem3 & -> & HJ3 & HP3 & Hout3 & Hgr3 & Hcase3).
destruct (rh_inv_rd memc _ mem3 Bb sp st dst pdata nb cur (sp - 64) 20 2 2 4 (getr regs3 10) HIc2 Hout3 Hcase3
ltac:(cbv; auto 8) Hpres Hpd ltac:(rewrite HRDv; lia) ltac:(rewrite HRDv; lia) ltac:(lia) Hdst1 Hst1 Hsd ltac:(lia) ltac:(lia) Hcur HBr)
as [HI3 Hr3].
jafter_call2 HS 49%nat regs3 mem3 HP3 (-64) (@nil nat) HS2.
match type of HS2 with ?P -> _ => assert (HK : P); [|specialize (HS2 HK)] end.
{ constructor; [|constructor].
eapply region_kept_rd; [exact Hout3 | exact Hgr3 | ..]; cbn [r_base r_lo r_hi r_wlo r_whi base_val]; ew_havocF; rewrite ?HE2, ?HRDv; lia. }
clear HS HK. rename HS2 into HS.
jreg HS (10%bv:reg) as Q3. cbn [ms_regs mkst] in Q3. rewrite Hr3 in Q3.
jrun_to LAWS ubs0tbl_ok HS HJ3 ubs0_A_readdata.
{ wr_norm. eapply wr_ok_cons_win; [reflexivity | ew_havocF; exact HE2 | cbn [r_wlo r_whi]; intros _; lia |]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF. rename HF into HF3.
lazymatch type of HS with st_ok _ _ _ ?ms1 =>
assert (HIc3 : rh_inv memc (ms_mem ms1) Bb sp st dst pdata nb cur 4)
by (apply (rh_inv_frame memc mem3 _ Bb sp st dst pdata nb cur 4 (sp - 64) HI3);
[ intros x Hx; apply HF3; intros (r & Hr & Hw); cbv [In] in Hr; destruct Hr as [<-|[]];
cbn [r_base r_wlo r_whi base_val] in Hw; revert Hw; ew_havocF; rewrite HE2; intro Hw; lia
| lia | lia | lia | exact Hdst1 | exact Hst1 | lia | lia | exact HBr ]);
assert (Wpn3 : word_mem ubs0segs (ms_mem ms1) st pdata /\ word_mem ubs0segs (ms_mem ms1) (st + 8) nb)
by (apply (rh_inv_words memc _ Bb sp st dst pdata nb cur 4 HIc3 Wp Wn); lia) end.
jreg HS (10%bv:reg) as M10_3. rewrite (HE 10%nat 10%bv eq_refl), G10 in M10_3.
jreg HS (11%bv:reg) as M11_3. rewrite HE11 in M11_3.
jreg HS (12%bv:reg) as M12_3.
jreg HS (2%bv:reg) as M2_3. rewrite HE2 in M2_3. replace (sp + -64) with (sp - 64) in M2_3 by lia.
jreg HS (1%bv:reg) as M1_3.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as HHk3.
eapply SR_bind.
{ eapply (jreaddata API IMG _ _ _ STK sp0 FP L A mem md Lc Ac mdc st (dst + 24) 2 pdata nb (hdr_cur nb cur 4) (sp - 64)).
- exact HS. - reflexivity. - reflexivity. - exact HJ3.
- exact M10_3. - exact M11_3. - exact M12_3. - exact M2_3.
- replace (sp - 64) with (sp + (-4) * 16) by lia. rewrite Z.mod_add by lia. exact Hal16.
- rewrite HRDv; lia. - lia. - exact H63.
- exact M1_3. - apply ret_ok_even; vm_compute; reflexivity.
- lia. - lia. - exact Hst8.
- exact (proj1 Wpn3). - exact (proj2 Wpn3). - exact (proj1 (proj2 HIc3)).
- lia. - unfold hdr_cur; destruct (Z.leb_spec (cur + 4) nb); lia. - lia. - lia. - lia. - intros; lia.
- intros j Hj. exact (proj1 (heap_blocks _ _ LAWS Lc Ac _ mdc pdata nb j HHk3 Hpdc Hj)).
- lia. - lia.
- intros i Hi. apply UN0d.writable_off_img_present; [lia | unfold UN0d.in_img1; lia |].
apply (journal_stack_w _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3). lia.
- intros a Ha. unfold wr_byte. left. lia.
- intros a Ha. unfold wr_byte. left. lia.
- right. lia. - right. lia. - intros _. left. rewrite HRDv. lia. - intros _. left. lia.
- destruct Hsd; [right|left]; lia. - intros _. right. lia. }
cbv beta. intros c' (regs4 & mem4 & -> & HJ4 & HP4 & Hout4 & Hgr4 & Hcase4).
destruct (rh_inv_rd memc _ mem4 Bb sp st dst pdata nb cur (sp - 64) 24 2 4 6 (getr regs4 10) HIc3 Hout4 Hcase4
ltac:(cbv; auto 8) Hpres Hpd ltac:(rewrite HRDv; lia) ltac:(rewrite HRDv; lia) ltac:(lia) Hdst1 Hst1 Hsd ltac:(lia) ltac:(lia) Hcur HBr)
as [HI4 Hr4].
jafter_call2 HS 65%nat regs4 mem4 HP4 (-64) (@nil nat) HS2.
match type of HS2 with ?P -> _ => assert (HK : P); [|specialize (HS2 HK)] end.
{ constructor; [|constructor].
eapply region_kept_rd; [exact Hout4 | exact Hgr4 | ..]; cbn [r_base r_lo r_hi r_wlo r_whi base_val]; ew_havocF; rewrite ?HE2, ?HRDv; lia. }
clear HS HK. rename HS2 into HS.
jreg HS (10%bv:reg) as Q4. cbn [ms_regs mkst] in Q4. rewrite Hr4 in Q4.
jrun_to LAWS ubs0tbl_ok HS HJ4 ubs0_A_readdata.
{ wr_norm. eapply wr_ok_cons_win; [reflexivity | ew_havocF; exact HE2 | cbn [r_wlo r_whi]; intros _; lia |]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF. rename HF into HF4.
lazymatch type of HS with st_ok _ _ _ ?ms1 =>
assert (HIc4 : rh_inv memc (ms_mem ms1) Bb sp st dst pdata nb cur 6)
by (apply (rh_inv_frame memc mem4 _ Bb sp st dst pdata nb cur 6 (sp - 64) HI4);
[ intros x Hx; apply HF4; intros (r & Hr & Hw); cbv [In] in Hr; destruct Hr as [<-|[]];
cbn [r_base r_wlo r_whi base_val] in Hw; revert Hw; ew_havocF; rewrite HE2; intro Hw; lia
| lia | lia | lia | exact Hdst1 | exact Hst1 | lia | lia | exact HBr ]);
assert (Wpn4 : word_mem ubs0segs (ms_mem ms1) st pdata /\ word_mem ubs0segs (ms_mem ms1) (st + 8) nb)
by (apply (rh_inv_words memc _ Bb sp st dst pdata nb cur 6 HIc4 Wp Wn); lia) end.
jreg HS (10%bv:reg) as M10_4. rewrite (HE 10%nat 10%bv eq_refl), G10 in M10_4.
jreg HS (11%bv:reg) as M11_4. rewrite HE11 in M11_4.
jreg HS (12%bv:reg) as M12_4.
jreg HS (2%bv:reg) as M2_4. rewrite HE2 in M2_4. replace (sp + -64) with (sp - 64) in M2_4 by lia.
jreg HS (1%bv:reg) as M1_4.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ4) as HHk4.
eapply SR_bind.
{ eapply (jreaddata API IMG _ _ _ STK sp0 FP L A mem md Lc Ac mdc st (dst + 28) 1 pdata nb (hdr_cur nb cur 6) (sp - 64)).
- exact HS. - reflexivity. - reflexivity. - exact HJ4.
- exact M10_4. - exact M11_4. - exact M12_4. - exact M2_4.
- replace (sp - 64) with (sp + (-4) * 16) by lia. rewrite Z.mod_add by lia. exact Hal16.
- rewrite HRDv; lia. - lia. - exact H63.
- exact M1_4. - apply ret_ok_even; vm_compute; reflexivity.
- lia. - lia. - exact Hst8.
- exact (proj1 Wpn4). - exact (proj2 Wpn4). - exact (proj1 (proj2 HIc4)).
- lia. - unfold hdr_cur; destruct (Z.leb_spec (cur + 6) nb); lia. - lia. - lia. - lia. - intros; lia.
- intros j Hj. exact (proj1 (heap_blocks _ _ LAWS Lc Ac _ mdc pdata nb j HHk4 Hpdc Hj)).
- lia. - lia.
- intros i Hi. apply UN0d.writable_off_img_present; [lia | unfold UN0d.in_img1; lia |].
apply (journal_stack_w _ _ _ _ _ _ _ _ _ _ _ _ _ HJ4). lia.
- intros a Ha. unfold wr_byte. left. lia.
- intros a Ha. unfold wr_byte. left. lia.
- right. lia. - right. lia. - intros _. left. rewrite HRDv. lia. - intros _. left. lia.
- destruct Hsd; [right|left]; lia. - intros _. right. lia. }
cbv beta. intros c' (regs5 & mem5 & -> & HJ5 & HP5 & Hout5 & Hgr5 & Hcase5).
destruct (rh_inv_rd memc _ mem5 Bb sp st dst pdata nb cur (sp - 64) 28 1 6 7 (getr regs5 10) HIc4 Hout5 Hcase5
ltac:(cbv; auto 8) Hpres Hpd ltac:(rewrite HRDv; lia) ltac:(rewrite HRDv; lia) ltac:(lia) Hdst1 Hst1 Hsd ltac:(lia) ltac:(lia) Hcur HBr)
as [HI5 Hr5].
jafter_call2 HS 81%nat regs5 mem5 HP5 (-64) (@nil nat) HS2.
match type of HS2 with ?P -> _ => assert (HK : P); [|specialize (HS2 HK)] end.
{ constructor; [|constructor].
eapply region_kept_rd; [exact Hout5 | exact Hgr5 | ..]; cbn [r_base r_lo r_hi r_wlo r_whi base_val]; ew_havocF; rewrite ?HE2, ?HRDv; lia. }
clear HS HK. rename HS2 into HS.
jreg HS (10%bv:reg) as Q5. cbn [ms_regs mkst] in Q5. rewrite Hr5 in Q5.
jrun_to LAWS ubs0tbl_ok HS HJ5 ubs0_A_readdata.
{ wr_norm. eapply wr_ok_cons_win; [reflexivity | ew_havocF; exact HE2 | cbn [r_wlo r_whi]; intros _; lia |]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF. rename HF into HF5.
lazymatch type of HS with st_ok _ _ _ ?ms1 =>
assert (HIc5 : rh_inv memc (ms_mem ms1) Bb sp st dst pdata nb cur 7)
by (apply (rh_inv_frame memc mem5 _ Bb sp st dst pdata nb cur 7 (sp - 64) HI5);
[ intros x Hx; apply HF5; intros (r & Hr & Hw); cbv [In] in Hr; destruct Hr as [<-|[]];
cbn [r_base r_wlo r_whi base_val] in Hw; revert Hw; ew_havocF; rewrite HE2; intro Hw; lia
| lia | lia | lia | exact Hdst1 | exact Hst1 | lia | lia | exact HBr ]);
assert (Wpn5 : word_mem ubs0segs (ms_mem ms1) st pdata /\ word_mem ubs0segs (ms_mem ms1) (st + 8) nb)
by (apply (rh_inv_words memc _ Bb sp st dst pdata nb cur 7 HIc5 Wp Wn); lia) end.
jreg HS (10%bv:reg) as M10_5. rewrite (HE 10%nat 10%bv eq_refl), G10 in M10_5.
jreg HS (11%bv:reg) as M11_5. rewrite HE11 in M11_5.
jreg HS (12%bv:reg) as M12_5.
jreg HS (2%bv:reg) as M2_5. rewrite HE2 in M2_5. replace (sp + -64) with (sp - 64) in M2_5 by lia.
jreg HS (1%bv:reg) as M1_5.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ5) as HHk5.
eapply SR_bind.
{ eapply (jreaddata API IMG _ _ _ STK sp0 FP L A mem md Lc Ac mdc st (dst + 26) 2 pdata nb (hdr_cur nb cur 7) (sp - 64)).
- exact HS. - reflexivity. - reflexivity. - exact HJ5.
- exact M10_5. - exact M11_5. - exact M12_5. - exact M2_5.
- replace (sp - 64) with (sp + (-4) * 16) by lia. rewrite Z.mod_add by lia. exact Hal16.
- rewrite HRDv; lia. - lia. - exact H63.
- exact M1_5. - apply ret_ok_even; vm_compute; reflexivity.
- lia. - lia. - exact Hst8.
- exact (proj1 Wpn5). - exact (proj2 Wpn5). - exact (proj1 (proj2 HIc5)).
- lia. - unfold hdr_cur; destruct (Z.leb_spec (cur + 7) nb); lia. - lia. - lia. - lia. - intros; lia.
- intros j Hj. exact (proj1 (heap_blocks _ _ LAWS Lc Ac _ mdc pdata nb j HHk5 Hpdc Hj)).
- lia. - lia.
- intros i Hi. apply UN0d.writable_off_img_present; [lia | unfold UN0d.in_img1; lia |].
apply (journal_stack_w _ _ _ _ _ _ _ _ _ _ _ _ _ HJ5). lia.
- intros a Ha. unfold wr_byte. left. lia.
- intros a Ha. unfold wr_byte. left. lia.
- right. lia. - right. lia. - intros _. left. rewrite HRDv. lia. - intros _. left. lia.
- destruct Hsd; [right|left]; lia. - intros _. right. lia. }
cbv beta. intros c' (regs6 & mem6 & -> & HJ6 & HP6 & Hout6 & Hgr6 & Hcase6).
destruct (rh_inv_rd memc _ mem6 Bb sp st dst pdata nb cur (sp - 64) 26 2 7 9 (getr regs6 10) HIc5 Hout6 Hcase6
ltac:(cbv; auto 8) Hpres Hpd ltac:(rewrite HRDv; lia) ltac:(rewrite HRDv; lia) ltac:(lia) Hdst1 Hst1 Hsd ltac:(lia) ltac:(lia) Hcur HBr)
as [HI6 Hr6].
jafter_call2 HS 97%nat regs6 mem6 HP6 (-64) (@nil nat) HS2.
match type of HS2 with ?P -> _ => assert (HK : P); [|specialize (HS2 HK)] end.
{ constructor; [|constructor].
eapply region_kept_rd; [exact Hout6 | exact Hgr6 | ..]; cbn [r_base r_lo r_hi r_wlo r_whi base_val]; ew_havocF; rewrite ?HE2, ?HRDv; lia. }
clear HS HK. rename HS2 into HS.
jreg HS (10%bv:reg) as Q6. cbn [ms_regs mkst] in Q6. rewrite Hr6 in Q6.
lazymatch type of HS with st_ok _ ?E6 ?ss6 ?ms6 =>
assert (HSb : st_ok ubs0segs E6 (mkSS (ss_pc ss6) (ss_regs ss6) (rh_b16r :: ss_mem ss6) (ss_resv ss6) (ss_facts ss6)) ms6);
[ apply rh_add_region; [exact HS | vm_compute; reflexivity | |];
[ unfold region_ok, rh_b16r; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val ms_mem mkst]; ew_havocF; rewrite HE11;
split; [lia|]; split; [lia|]; split; [intros o Ho; lia|];
apply Forall_cons; [|apply Forall_nil];
eapply (chunk_ok_val _ _ _ _ _ _ _ b16);
[ cbn [sv_denot]; ew_havocF; rewrite Z.add_0_r, HE32, Z_to_bv_bv_unsigned; reflexivity
| pose proof (rh_valk_range 9 memc pdata nb cur 16) as Hb; change (hdr_valk 9 memc pdata nb cur 16) with b16 in Hb; change (2 ^ (8 * Z.of_N 1)) with 256; lia | cbn; lia
| intros kk Hkk; assert (kk = 0%nat) by lia; subst kk; cbn [Z.of_nat N.to_nat]; rewrite Z.add_0_r;
rewrite (proj1 HI6 16 ltac:(lia)), rh_le_byte1 by (pose proof (rh_valk_range 9 memc pdata nb cur 16) as Hb; change (hdr_valk 9 memc pdata nb cur 16) with b16 in Hb; lia);
reflexivity ]
| unfold rh_b16r; cbn [ss_mem all_disjoint]; unfold extent_disjoint; cbn [r_base r_lo r_hi base_val]; ew_havocF; rewrite ?HE2, ?HE11;
repeat split; lia ]
| clear HS; cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HSb; rename HSb into HS ] end.
jrun LAWS ubs0tbl_ok HS HJ6.
{ wr_norm. apply wr_ok_cons_ro; [cbn; lia|].
eapply wr_ok_cons_win; [reflexivity | ew_havocF; exact HE2 | cbn [r_wlo r_whi]; intros _; lia |]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF. rename HF into HF6.
lazymatch type of HS with st_ok _ _ _ ?msf =>
assert (HIb : rh_inv memc (ms_mem msf) Bb sp st dst pdata nb cur 9)
by (apply (rh_inv_frame memc mem6 _ Bb sp st dst pdata nb cur 9 (sp - 64) HI6);
[ intros x Hx; apply HF6; intros (r & Hr & Hw); cbv [In] in Hr; destruct Hr as [<-|[<-|[]]];
cbn [r_base r_wlo r_whi base_val] in Hw; revert Hw; ew_havocF; rewrite ?HE2, ?HE11; intro Hw; lia
| lia | lia | lia | exact Hdst1 | exact Hst1 | lia | lia | exact HBr ]) end.
assert (HA : forall Ex, ew Ex 32 = Z_to_bv 64 b16 -> U Ex (SAlu ALU_AND (SExt false 8 (SOff 32 0)) (SLit 1)) = Z.land b16 1).
{ intros Ex HEx. apply rh_attr_U; [exact HEx|]. pose proof (rh_valk_range 9 memc pdata nb cur 16) as Hb.
change (hdr_valk 9 memc pdata nb cur 16) with b16 in Hb. exact Hb. }
jbranch ubs0tbl HS.
- rewrite branch_eq_U, HA, U_SLit in Hc by (ew_havocF; exact HE32). change (zcanon 0) with 0 in Hc.
assert (Hpc : hdr_pc memc pdata nb cur = IMGPC) by (unfold hdr_pc; change (hdr_val memc pdata nb cur 16) with b16; rewrite Hc; reflexivity).
jrun_to LAWS ubs0tbl_ok HS HJ6 IMGPC.
{ wr_norm. apply wr_ok_cons_ro; [cbn; lia|].
eapply wr_ok_cons_win; [reflexivity | ew_havocF; exact HE2 | cbn [r_wlo r_whi]; intros _; lia |]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF. rename HF into HF7.
lazymatch type of HS with st_ok _ ?Ef ?ssf ?msf =>
assert (HIf : rh_inv memc (ms_mem msf) Bb sp st dst pdata nb cur 9)
by (apply (rh_inv_frame memc _ _ Bb sp st dst pdata nb cur 9 (sp - 64) HIb);
[ intros x Hx; apply HF7; intros (r & Hr & Hw); cbv [In] in Hr; destruct Hr as [<-|[<-|[]]];
cbn [r_base r_wlo r_whi base_val] in Hw; revert Hw; ew_havocF; rewrite ?HE2, ?HE11; intro Hw; lia
| lia | lia | lia | exact Hdst1 | exact Hst1 | lia | lia | exact HBr ]);
assert (Wpnf : word_mem ubs0segs (ms_mem msf) st pdata /\ word_mem ubs0segs (ms_mem msf) (st + 8) nb)
by (apply (rh_inv_words memc _ Bb sp st dst pdata nb cur 9 HIf Wp Wn); lia);
assert (SW : forall off (rr : reg) (n : nat), Z.of_nat n = bv_unsigned rr -> (n < 32)%nat ->
In (mkChunk off (CVal 8 (SOff n 0))) [mkChunk (-56) (CVal 8 (SOff 21 0)); mkChunk (-48) (CVal 8 (SOff 20 0));
mkChunk (-40) (CVal 8 (SOff 19 0)); mkChunk (-32) (CVal 8 (SOff 18 0)); mkChunk (-24) (CVal 8 (SOff 9 0));
mkChunk (-16) (CVal 8 (SOff 8 0)); mkChunk (-8) (CVal 8 (SOff 1 0))] ->
word_mem ubs0segs (ms_mem msf) (sp + off) (bv_unsigned (getr regs rr)))
by (intros off rr n Hn Hn32 Hin; eapply (st_chunk_word _ _ _ 1%nat _ 2%nat off (SOff n 0) sp _ HS);
[ reflexivity | reflexivity | revert Hin; vm_compute; tauto | ew_havocF; exact HE2
| cbn [sv_denot]; repeat (rewrite ew_havoc_old; [|lia]); rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (HE n rr Hn), Z_to_bv_bv_unsigned; reflexivity
| apply bv_unsigned_in_range ]);
assert (A37 : ew Ef 37 = Z_to_bv 64 (hdr_rv nb cur 2)) by (rewrite Q2; repeat (rewrite ew_havoc_old; [|nat_lt_lit]); reflexivity);
assert (A53 : ew Ef 53 = Z_to_bv 64 (hdr_rv nb cur 4)) by (rewrite Q3; repeat (rewrite ew_havoc_old; [|nat_lt_lit]); reflexivity);
assert (A69 : ew Ef 69 = Z_to_bv 64 (hdr_rv nb cur 6)) by (rewrite Q4; repeat (rewrite ew_havoc_old; [|nat_lt_lit]); reflexivity);
assert (A85 : ew Ef 85 = Z_to_bv 64 (hdr_rv nb cur 7)) by (rewrite Q5; repeat (rewrite ew_havoc_old; [|nat_lt_lit]); reflexivity);
assert (A101 : ew Ef 101 = Z_to_bv 64 (hdr_rv nb cur 9)) by (rewrite Q6; reflexivity);
pose proof (st_ok_reg _ _ _ _ 20%bv HS) as R20; eval_sr_get_in R20; cbn [sv_denot] in R20;
rewrite ?A37, ?A53, ?A69, ?A85, ?A101, ?Z.add_0_r, ?Z_to_bv_bv_unsigned in R20;
assert (R20f : getr (ms_regs msf) 20 = Z_to_bv 64 (hdr_rv nb cur 9))
by (rewrite R20; unfold hdr_rv; destruct (Z.leb_spec (cur + 2) nb); destruct (Z.leb_spec (cur + 4) nb);
destruct (Z.leb_spec (cur + 6) nb); destruct (Z.leb_spec (cur + 7) nb); destruct (Z.leb_spec (cur + 9) nb);
first [exfalso; lia | apply bv_eq; vm_compute; reflexivity]);
rewrite (st_ok_mkst ubs0segs Ef ssf msf HS eq_refl) end.
jreg HS (2%bv:reg) as R2. rewrite HE2 in R2. replace (sp + -64) with (sp - RFC_FRAME) in R2 by lia.
jreg HS (19%bv:reg) as R19. rewrite HE11 in R19.
jreg HS (3%bv:reg) as R3. rewrite (HE 3%nat 3%bv eq_refl) in R3.
jreg HS (4%bv:reg) as R4. rewrite (HE 4%nat 4%bv eq_refl) in R4.
jreg HS (8%bv:reg) as R8. rewrite (HE 11%nat 11%bv eq_refl), G11 in R8.
jreg HS (9%bv:reg) as R9. rewrite (HE 12%nat 12%bv eq_refl), G12 in R9.
jreg HS (18%bv:reg) as R18. rewrite (HE 10%nat 10%bv eq_refl), G10 in R18.
jreg HS (22%bv:reg) as R22. rewrite (HE 22%nat 22%bv eq_refl) in R22.
jreg HS (23%bv:reg) as R23. rewrite (HE 23%nat 23%bv eq_refl) in R23.
jreg HS (24%bv:reg) as R24. rewrite (HE 24%nat 24%bv eq_refl) in R24.
jreg HS (25%bv:reg) as R25. rewrite (HE 25%nat 25%bv eq_refl) in R25.
jreg HS (26%bv:reg) as R26. rewrite (HE 26%nat 26%bv eq_refl) in R26.
jreg HS (27%bv:reg) as R27. rewrite (HE 27%nat 27%bv eq_refl) in R27.
apply SR_ret. eexists _, _.
split; [rewrite Hpc; reflexivity|]. split; [exact HJ6|].
split; [exact R2|]. split; [exact R3|]. split; [exact R4|]. split; [exact R8|]. split; [exact R9|]. split; [exact R18|].
split; [exact R19|]. split; [exact R20f|].
split; [exact R22|]. split; [exact R23|]. split; [exact R24|]. split; [exact R25|]. split; [exact R26|]. split; [exact R27|].
split; [replace (sp - 8) with (sp + -8) by lia; exact (SW (-8) 1%bv 1%nat eq_refl ltac:(lia) ltac:(cbv; tauto))|].
split; [replace (sp - 16) with (sp + -16) by lia; exact (SW (-16) 8%bv 8%nat eq_refl ltac:(lia) ltac:(cbv; tauto))|].
split; [replace (sp - 24) with (sp + -24) by lia; exact (SW (-24) 9%bv 9%nat eq_refl ltac:(lia) ltac:(cbv; tauto))|].
split; [replace (sp - 32) with (sp + -32) by lia; exact (SW (-32) 18%bv 18%nat eq_refl ltac:(lia) ltac:(cbv; tauto))|].
split; [replace (sp - 40) with (sp + -40) by lia; exact (SW (-40) 19%bv 19%nat eq_refl ltac:(lia) ltac:(cbv; tauto))|].
split; [replace (sp - 48) with (sp + -48) by lia; exact (SW (-48) 20%bv 20%nat eq_refl ltac:(lia) ltac:(cbv; tauto))|].
split; [replace (sp - 56) with (sp + -56) by lia; exact (SW (-56) 21%bv 21%nat eq_refl ltac:(lia) ltac:(cbv; tauto))|].
split; [exact (proj1 Wpnf)|]. split; [exact (proj2 Wpnf)|].
split; [exact (proj1 (proj2 HIf))|]. split; [exact (proj1 HIf)|].
split; [exact (proj1 (proj2 (proj2 HIf)))|]. exact (proj2 (proj2 (proj2 HIf))).
- rewrite branch_eq_U, HA, U_SLit in Hc by (ew_havocF; exact HE32). change (zcanon 0) with 0 in Hc.
assert (Hpc : hdr_pc memc pdata nb cur = PALPC) by (unfold hdr_pc; change (hdr_val memc pdata nb cur 16) with b16; rewrite Hc; reflexivity).
jrun_to LAWS ubs0tbl_ok HS HJ6 PALPC.
{ wr_norm. apply wr_ok_cons_ro; [cbn; lia|].
eapply wr_ok_cons_win; [reflexivity | ew_havocF; exact HE2 | cbn [r_wlo r_whi]; intros _; lia |]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF. rename HF into HF7.
lazymatch type of HS with st_ok _ ?Ef ?ssf ?msf =>
assert (HIf : rh_inv memc (ms_mem msf) Bb sp st dst pdata nb cur 9)
by (apply (rh_inv_frame memc _ _ Bb sp st dst pdata nb cur 9 (sp - 64) HIb);
[ intros x Hx; apply HF7; intros (r & Hr & Hw); cbv [In] in Hr; destruct Hr as [<-|[<-|[]]];
cbn [r_base r_wlo r_whi base_val] in Hw; revert Hw; ew_havocF; rewrite ?HE2, ?HE11; intro Hw; lia
| lia | lia | lia | exact Hdst1 | exact Hst1 | lia | lia | exact HBr ]);
assert (Wpnf : word_mem ubs0segs (ms_mem msf) st pdata /\ word_mem ubs0segs (ms_mem msf) (st + 8) nb)
by (apply (rh_inv_words memc _ Bb sp st dst pdata nb cur 9 HIf Wp Wn); lia);
assert (SW : forall off (rr : reg) (n : nat), Z.of_nat n = bv_unsigned rr -> (n < 32)%nat ->
In (mkChunk off (CVal 8 (SOff n 0))) [mkChunk (-56) (CVal 8 (SOff 21 0)); mkChunk (-48) (CVal 8 (SOff 20 0));
mkChunk (-40) (CVal 8 (SOff 19 0)); mkChunk (-32) (CVal 8 (SOff 18 0)); mkChunk (-24) (CVal 8 (SOff 9 0));
mkChunk (-16) (CVal 8 (SOff 8 0)); mkChunk (-8) (CVal 8 (SOff 1 0))] ->
word_mem ubs0segs (ms_mem msf) (sp + off) (bv_unsigned (getr regs rr)))
by (intros off rr n Hn Hn32 Hin; eapply (st_chunk_word _ _ _ 1%nat _ 2%nat off (SOff n 0) sp _ HS);
[ reflexivity | reflexivity | revert Hin; vm_compute; tauto | ew_havocF; exact HE2
| cbn [sv_denot]; repeat (rewrite ew_havoc_old; [|lia]); rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (HE n rr Hn), Z_to_bv_bv_unsigned; reflexivity
| apply bv_unsigned_in_range ]);
assert (A37 : ew Ef 37 = Z_to_bv 64 (hdr_rv nb cur 2)) by (rewrite Q2; repeat (rewrite ew_havoc_old; [|nat_lt_lit]); reflexivity);
assert (A53 : ew Ef 53 = Z_to_bv 64 (hdr_rv nb cur 4)) by (rewrite Q3; repeat (rewrite ew_havoc_old; [|nat_lt_lit]); reflexivity);
assert (A69 : ew Ef 69 = Z_to_bv 64 (hdr_rv nb cur 6)) by (rewrite Q4; repeat (rewrite ew_havoc_old; [|nat_lt_lit]); reflexivity);
assert (A85 : ew Ef 85 = Z_to_bv 64 (hdr_rv nb cur 7)) by (rewrite Q5; repeat (rewrite ew_havoc_old; [|nat_lt_lit]); reflexivity);
assert (A101 : ew Ef 101 = Z_to_bv 64 (hdr_rv nb cur 9)) by (rewrite Q6; reflexivity);
pose proof (st_ok_reg _ _ _ _ 20%bv HS) as R20; eval_sr_get_in R20; cbn [sv_denot] in R20;
rewrite ?A37, ?A53, ?A69, ?A85, ?A101, ?Z.add_0_r, ?Z_to_bv_bv_unsigned in R20;
assert (R20f : getr (ms_regs msf) 20 = Z_to_bv 64 (hdr_rv nb cur 9))
by (rewrite R20; unfold hdr_rv; destruct (Z.leb_spec (cur + 2) nb); destruct (Z.leb_spec (cur + 4) nb);
destruct (Z.leb_spec (cur + 6) nb); destruct (Z.leb_spec (cur + 7) nb); destruct (Z.leb_spec (cur + 9) nb);
first [exfalso; lia | apply bv_eq; vm_compute; reflexivity]);
rewrite (st_ok_mkst ubs0segs Ef ssf msf HS eq_refl) end.
jreg HS (2%bv:reg) as R2. rewrite HE2 in R2. replace (sp + -64) with (sp - RFC_FRAME) in R2 by lia.
jreg HS (19%bv:reg) as R19. rewrite HE11 in R19.
jreg HS (3%bv:reg) as R3. rewrite (HE 3%nat 3%bv eq_refl) in R3.
jreg HS (4%bv:reg) as R4. rewrite (HE 4%nat 4%bv eq_refl) in R4.
jreg HS (8%bv:reg) as R8. rewrite (HE 11%nat 11%bv eq_refl), G11 in R8.
jreg HS (9%bv:reg) as R9. rewrite (HE 12%nat 12%bv eq_refl), G12 in R9.
jreg HS (18%bv:reg) as R18. rewrite (HE 10%nat 10%bv eq_refl), G10 in R18.
jreg HS (22%bv:reg) as R22. rewrite (HE 22%nat 22%bv eq_refl) in R22.
jreg HS (23%bv:reg) as R23. rewrite (HE 23%nat 23%bv eq_refl) in R23.
jreg HS (24%bv:reg) as R24. rewrite (HE 24%nat 24%bv eq_refl) in R24.
jreg HS (25%bv:reg) as R25. rewrite (HE 25%nat 25%bv eq_refl) in R25.
jreg HS (26%bv:reg) as R26. rewrite (HE 26%nat 26%bv eq_refl) in R26.
jreg HS (27%bv:reg) as R27. rewrite (HE 27%nat 27%bv eq_refl) in R27.
apply SR_ret. eexists _, _.
split; [rewrite Hpc; reflexivity|]. split; [exact HJ6|].
split; [exact R2|]. split; [exact R3|]. split; [exact R4|]. split; [exact R8|]. split; [exact R9|]. split; [exact R18|].
split; [exact R19|]. split; [exact R20f|].
split; [exact R22|]. split; [exact R23|]. split; [exact R24|]. split; [exact R25|]. split; [exact R26|]. split; [exact R27|].
split; [replace (sp - 8) with (sp + -8) by lia; exact (SW (-8) 1%bv 1%nat eq_refl ltac:(lia) ltac:(cbv; tauto))|].
split; [replace (sp - 16) with (sp + -16) by lia; exact (SW (-16) 8%bv 8%nat eq_refl ltac:(lia) ltac:(cbv; tauto))|].
split; [replace (sp - 24) with (sp + -24) by lia; exact (SW (-24) 9%bv 9%nat eq_refl ltac:(lia) ltac:(cbv; tauto))|].
split; [replace (sp - 32) with (sp + -32) by lia; exact (SW (-32) 18%bv 18%nat eq_refl ltac:(lia) ltac:(cbv; tauto))|].
split; [replace (sp - 40) with (sp + -40) by lia; exact (SW (-40) 19%bv 19%nat eq_refl ltac:(lia) ltac:(cbv; tauto))|].
split; [replace (sp - 48) with (sp + -48) by lia; exact (SW (-48) 20%bv 20%nat eq_refl ltac:(lia) ltac:(cbv; tauto))|].
split; [replace (sp - 56) with (sp + -56) by lia; exact (SW (-56) 21%bv 21%nat eq_refl ltac:(lia) ltac:(cbv; tauto))|].
split; [exact (proj1 Wpnf)|]. split; [exact (proj2 Wpnf)|].
split; [exact (proj1 (proj2 HIf))|]. split; [exact (proj1 HIf)|].
split; [exact (proj1 (proj2 (proj2 HIf)))|]. exact (proj2 (proj2 (proj2 HIf))).
Qed.
End S.
End t.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

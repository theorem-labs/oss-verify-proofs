(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import FseNCount FseLemmas.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Lemma shl32_inv : forall x n v, shl32 x n = Ok v -> 0 <= n < 32 /\ v = u32 (x * 2^n).
Proof.
intros x n v H. unfold shl32 in H.
destruct (Z.leb_spec 0 n); destruct (Z.ltb_spec n 32); cbn in H; try discriminate.
injection H as <-. split; [lia| reflexivity].
Qed.
Lemma load_inv : forall l i c, load l i = Ok c -> 0 <= i < Zlength l /\ c = Znth i l.
Proof.
intros l i c H. unfold load in H.
destruct (Z.leb_spec 0 i); destruct (Z.ltb_spec i (Zlength l)); cbn in H; try discriminate.
injection H as <-. split; [lia| reflexivity].
Qed.
Lemma store_inv : forall l i v l', store l i v = Ok l' -> 0 <= i < Zlength l /\ l' = Zupd i v l.
Proof.
intros l i v l' H. unfold store in H.
destruct (Z.leb_spec 0 i); destruct (Z.ltb_spec i (Zlength l)); cbn in H; try discriminate.
injection H as <-. split; [lia| reflexivity].
Qed.
Lemma bind_inv : forall {A B} (m : res A) (k : A -> res B) b, bind m k = Ok b -> exists a, m = Ok a /\ k a = Ok b.
Proof. intros A B [a| | |] k b H; cbn in H; try discriminate. exists a. split; [reflexivity| exact H]. Qed.
Lemma Zlength_Zupd : forall i v l, Zlength (Zupd i v l) = Zlength l.
Proof. intros. unfold Zlength. rewrite Zupd_length. reflexivity. Qed.
Section Inv.
Variable nc : list Z.
Variable asz bsz : Z.
Variable safe : bool.
#[using="Type"] Lemma wflush_inv : forall dec16 s s', wflush bsz safe dec16 s = Ok s' ->
(safe = true \/ w_out s <= bsz - 2) /\ 0 <= w_out s /\ w_out s + 1 < Zlength (w_buf s) /\
s' = mkW (Zupd (w_out s + 1) (to_byte (w_bitStream s / 2^8)) (Zupd (w_out s) (to_byte (w_bitStream s)) (w_buf s)))
(w_out s + 2) (w_bitStream s / 2^16) (if dec16 then w_bitCount s - 16 else w_bitCount s)
(w_symbol s) (w_remaining s) (w_threshold s) (w_nbBits s) (w_previousIs0 s).
Proof.
intros dec16 s s' H. unfold wflush in H.
destruct (negb safe && (bsz - 2 <? w_out s)) eqn:C; [discriminate|].
apply bind_inv in H. destruct H as (b1 & S1 & H). apply bind_inv in H. destruct H as (b2 & S2 & H).
apply store_inv in S1. destruct S1 as [R1 ->]. apply store_inv in S2. destruct S2 as [R2 ->].
rewrite Zlength_Zupd in R2. injection H as <-.
split; [|split; [lia| split; [lia| reflexivity]]].
destruct safe; [left; reflexivity| right]. cbn in C. apply Z.ltb_ge in C. lia.
Qed.
#[using="Type"] Lemma wflush_if_inv : forall s s', wflush_if bsz safe s = Ok s' ->
(16 < w_bitCount s /\ wflush bsz safe true s = Ok s') \/ (w_bitCount s <= 16 /\ s' = s).
Proof.
intros s s' H. unfold wflush_if in H. destruct (Z.ltb_spec 16 (w_bitCount s)).
- left. split; [lia| exact H].
- right. injection H as <-. split; [lia| reflexivity].
Qed.
#[using="Type"] Lemma skip_zeros_S : forall f symbol,
skip_zeros nc asz (S f) symbol =
if symbol <? asz then bind (load nc symbol) (fun c => if c =? 0 then skip_zeros nc asz f (symbol + 1) else Ok symbol)
else Ok symbol.
Proof. reflexivity. Qed.
#[using="Type"] Lemma run24_S : forall f s start,
run24 bsz safe (S f) s start =
if start + 24 <=? w_symbol s then
bind (shl32 65535 (w_bitCount s)) (fun v =>
bind (wflush bsz safe false (mkW (w_buf s) (w_out s) (u32 (w_bitStream s + v)) (w_bitCount s)
(w_symbol s) (w_remaining s) (w_threshold s) (w_nbBits s) (w_previousIs0 s)))
(fun s2 => run24 bsz safe f s2 (start + 24)))
else Ok (s, start).
Proof. reflexivity. Qed.
#[using="Type"] Lemma run3_S : forall f s start,
run3 (S f) s start =
if start + 3 <=? w_symbol s then
bind (shl32 3 (w_bitCount s)) (fun v =>
run3 f (mkW (w_buf s) (w_out s) (u32 (w_bitStream s + v)) (w_bitCount s + 2)
(w_symbol s) (w_remaining s) (w_threshold s) (w_nbBits s) (w_previousIs0 s)) (start + 3))
else Ok (s, start).
Proof. reflexivity. Qed.
#[using="Type"] Lemma shrink_S : forall f remaining threshold nbBits,
shrink (S f) remaining threshold nbBits =
if remaining <? threshold then shrink f remaining (threshold / 2) (nbBits - 1) else Ok (threshold, nbBits).
Proof. reflexivity. Qed.
#[using="Type"] Lemma wloop_S : forall f s,
wloop nc asz bsz safe (S f) s =
if (w_symbol s <? asz) && (1 <? w_remaining s) then
bind (wbody nc asz bsz safe s) (fun fl => match fl with Brk s' => Ok s' | Cont s' => wloop nc asz bsz safe f s' end)
else Ok s.
Proof. reflexivity. Qed.
End Inv.
Section Fields.
Variable nc : list Z.
Variable asz bsz : Z.
Variable safe : bool.
Definition same_ctl (s s' : wstate) : Prop :=
w_remaining s' = w_remaining s /\ w_threshold s' = w_threshold s
/\ w_nbBits s' = w_nbBits s /\ w_previousIs0 s' = w_previousIs0 s.
Definition winv (s : wstate) : Prop :=
Zlength (w_buf s) = bsz /\ 0 <= w_out s <= bsz /\ 0 <= w_bitStream s < 2^32 /\ 0 <= w_bitCount s <= 32
/\ 0 <= w_symbol s <= asz /\ 1 <= w_remaining s <= 8192 /\ 1 <= w_nbBits s <= 13 /\ w_threshold s = 2^(w_nbBits s - 1).
#[using="Type"] Lemma div16_range : forall x, 0 <= x < 2^32 -> 0 <= x / 2^16 < 2^32.
Proof.
intros x R. change (2^32) with 4294967296 in *. change (2^16) with 65536.
split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; lia.
Qed.
#[using="Type"] Lemma skip_zeros_range : forall f sym sym', 0 <= sym <= asz -> skip_zeros nc asz f sym = Ok sym' -> sym <= sym' <= asz.
Proof.
induction f as [|f IH]; intros sym sym' R H; [discriminate|].
rewrite skip_zeros_S in H. destruct (Z.ltb_spec sym asz).
- apply bind_inv in H. destruct H as (c & _ & H). destruct (c =? 0).
+ apply IH in H; lia.
+ injection H as <-. lia.
- injection H as <-. lia.
Qed.
#[using="Type"] Lemma wflush_facts : forall dec16 s s', wflush bsz safe dec16 s = Ok s' ->
Zlength (w_buf s) = bsz -> 0 <= w_bitStream s < 2^32 ->
same_ctl s s' /\ w_symbol s' = w_symbol s /\ Zlength (w_buf s') = bsz /\ 0 <= w_out s' <= bsz /\ w_out s' = w_out s + 2
/\ 0 <= w_bitStream s' < 2^32 /\ w_bitCount s' = (if dec16 then w_bitCount s - 16 else w_bitCount s).
Proof.
intros dec16 s s' H LB RB. apply wflush_inv in H. destruct H as (_ & O0 & O1 & ->).
cbn [w_buf w_out w_bitStream w_bitCount w_symbol w_remaining w_threshold w_nbBits w_previousIs0].
rewrite !Zlength_Zupd. unfold same_ctl. cbn [w_remaining w_threshold w_nbBits w_previousIs0].
pose proof (div16_range _ RB). repeat split; try reflexivity; try lia.
Qed.
#[using="Type"] Lemma run24_facts : forall f s start s' start', run24 bsz safe f s start = Ok (s', start') ->
Zlength (w_buf s) = bsz -> 0 <= w_bitStream s < 2^32 -> 0 <= w_out s <= bsz ->
same_ctl s s' /\ w_symbol s' = w_symbol s /\ w_bitCount s' = w_bitCount s /\ Zlength (w_buf s') = bsz
/\ 0 <= w_out s' <= bsz /\ 0 <= w_bitStream s' < 2^32
/\ start <= start' /\ (start <= w_symbol s -> start' <= w_symbol s < start' + 24).
Proof.
induction f as [|f IH]; intros s start s' start' H LB RB RO; [discriminate|].
rewrite run24_S in H. destruct (Z.leb_spec (start + 24) (w_symbol s)).
- apply bind_inv in H. destruct H as (v & SH & H). apply bind_inv in H. destruct H as (s2 & FL & H).
apply wflush_facts in FL; [| exact LB | cbn [w_bitStream]; apply u32_range].
unfold same_ctl in FL. cbn [w_buf w_out w_bitStream w_bitCount w_symbol w_remaining w_threshold w_nbBits w_previousIs0] in FL.
destruct FL as ((C1 & C2 & C3 & C4) & SY & LB2 & RO2 & O2 & RB2 & BC2).
apply IH in H; [| exact LB2 | exact RB2 | exact RO2].
destruct H as ((D1 & D2 & D3 & D4) & SY' & BC' & LB' & RO' & RB' & ST' & SR').
unfold same_ctl. cbn [w_remaining w_threshold w_nbBits w_previousIs0] in *.
rewrite SY in SR'. repeat split; try congruence; try lia.
- injection H as <- <-. unfold same_ctl. repeat split; try reflexivity; try lia.
Qed.
#[using="Type"] Lemma run3_facts : forall f s start s' start', run3 f s start = Ok (s', start') ->
0 <= w_bitStream s < 2^32 -> 0 <= w_bitCount s ->
same_ctl s s' /\ w_symbol s' = w_symbol s /\ w_buf s' = w_buf s /\ w_out s' = w_out s
/\ 0 <= w_bitStream s' < 2^32 /\ w_bitCount s <= w_bitCount s'
/\ start <= start' /\ (start <= w_symbol s -> start' <= w_symbol s < start' + 3).
Proof.
induction f as [|f IH]; intros s start s' start' H RB BC; [discriminate|].
rewrite run3_S in H. destruct (Z.leb_spec (start + 3) (w_symbol s)).
- apply bind_inv in H. destruct H as (v & SH & H).
apply IH in H; [| cbn [w_bitStream]; apply u32_range | cbn [w_bitCount]; lia]. unfold same_ctl in H.
cbn [w_buf w_out w_bitStream w_bitCount w_symbol w_remaining w_threshold w_nbBits w_previousIs0] in H.
destruct H as ((D1 & D2 & D3 & D4) & SY' & B' & O' & RB' & BC' & ST' & SR').
unfold same_ctl. repeat split; try congruence; try lia.
- injection H as <- <-. unfold same_ctl. repeat split; try reflexivity; try lia.
Qed.
#[using="Type"] Lemma shrink_facts : forall f rem thr nb thr' nb', shrink f rem thr nb = Ok (thr', nb') ->
1 <= rem -> 1 <= nb -> thr = 2^(nb - 1) ->
1 <= nb' <= nb /\ thr' = 2^(nb' - 1).
Proof.
induction f as [|f IH]; intros rem thr nb thr' nb' H R NB TH; [discriminate|].
rewrite shrink_S in H. destruct (Z.ltb_spec rem thr).
- assert (2 <= nb). { destruct (Z.eq_dec nb 1) as [->|]; [|lia]. change (2^(1-1)) with 1 in TH. lia. }
apply IH in H; [lia | lia | lia |].
rewrite TH. replace (2 ^ (nb - 1)) with (2 ^ (nb - 1 - 1) * 2).
{ rewrite Z.div_mul by lia. reflexivity. }
rewrite Z.mul_comm, <- (Z.pow_succ_r 2 (nb - 1 - 1)) by lia. f_equal. lia.
- injection H as <- <-. split; [lia| exact TH].
Qed.
#[using="Type"] Lemma wzero_block_facts : forall s fl, wzero_block nc asz bsz safe s = Ok fl -> winv s -> w_symbol s < asz ->
match fl with
| Brk s' => w_symbol s' = asz /\ w_buf s' = w_buf s /\ w_out s' = w_out s /\ w_bitStream s' = w_bitStream s
/\ w_bitCount s' = w_bitCount s /\ same_ctl s s'
| Cont s' => winv s' /\ same_ctl s s' /\ w_symbol s <= w_symbol s' < asz /\ w_bitCount s' <= 17
end.
Proof.
intros s fl H (LB & RO & RB & BC & SY & RM & NB & TH) SYA. unfold wzero_block in H.
apply bind_inv in H. destruct H as (sym & SK & H). apply skip_zeros_range in SK; [| lia].
destruct (Z.eqb_spec sym asz) as [E|NE].
- injection H as <-. cbn. unfold same_ctl. cbn. repeat split; try reflexivity; exact E.
- apply bind_inv in H. destruct H as ([s1 start1] & R24 & H).
apply run24_facts in R24; [| exact LB | exact RB | exact RO].
unfold same_ctl in R24. cbn [w_buf w_out w_bitStream w_bitCount w_symbol w_remaining w_threshold w_nbBits w_previousIs0] in R24.
destruct R24 as ((C1 & C2 & C3 & C4) & SY1 & BC1 & LB1 & RO1 & RB1 & ST1 & SR1).
apply bind_inv in H. destruct H as ([s2 start2] & R3 & H).
apply run3_facts in R3; [| exact RB1 | lia].
destruct R3 as ((D1 & D2 & D3 & D4) & SY2 & B2 & O2 & RB2 & BC2 & ST2 & SR2).
apply bind_inv in H. destruct H as (v & SH & H). apply shl32_inv in SH. destruct SH as [BCR ->].
apply bind_inv in H. destruct H as (s4 & FL & H). injection H as <-.
apply wflush_if_inv in FL. cbn [w_bitCount] in FL.
destruct FL as [[G FL]|[G ->]].
+ apply wflush_facts in FL; [| cbn [w_buf]; congruence | cbn [w_bitStream]; apply u32_range].
unfold same_ctl in FL. cbn [w_buf w_out w_bitStream w_bitCount w_symbol w_remaining w_threshold w_nbBits w_previousIs0] in FL.
destruct FL as ((E1 & E2 & E3 & E4) & SY4 & LB4 & RO4 & O4 & RB4 & BC4).
unfold winv, same_ctl. repeat split; try congruence; try lia.
+ unfold winv, same_ctl.
cbn [w_buf w_out w_bitStream w_bitCount w_symbol w_remaining w_threshold w_nbBits w_previousIs0].
pose proof (u32_range (w_bitStream s2 + u32 (u32 (sym - start2) * 2 ^ w_bitCount s2))).
repeat split; try congruence; try lia.
Qed.
#[using="Type"] Lemma wcount_block_inv : forall s s', wcount_block nc s = Ok s' ->
let count := Znth (w_symbol s) nc in
let max := 2 * w_threshold s - 1 - w_remaining s in
let remaining := w_remaining s - (if count <? 0 then - count else count) in
let count1 := count + 1 in
let count2 := if w_threshold s <=? count1 then count1 + max else count1 in
exists thr' nb',
0 <= w_symbol s < Zlength nc /\ 0 <= w_bitCount s < 32 /\ 1 <= remaining
/\ shrink 64 remaining (w_threshold s) (w_nbBits s) = Ok (thr', nb')
/\ s' = mkW (w_buf s) (w_out s) (u32 (w_bitStream s + u32 (u32 count2 * 2 ^ w_bitCount s)))
(w_bitCount s + w_nbBits s - (if count2 <? max then 1 else 0))
(w_symbol s + 1) remaining thr' nb' (count2 =? 1).
Proof.
intros s s' H. unfold wcount_block in H.
apply bind_inv in H. destruct H as (c & LD & H). apply load_inv in LD. destruct LD as [LR ->].
cbv zeta in H |- *.
apply bind_inv in H. destruct H as (v & SH & H). apply shl32_inv in SH. destruct SH as [BC ->].
match type of H with (if ?r <? 1 then _ else _) = _ => destruct (Z.ltb_spec r 1) as [R1|R1]; [discriminate|] end.
apply bind_inv in H. destruct H as ([thr' nb'] & SHR & H). injection H as <-.
exists thr', nb'. repeat split; try assumption; lia.
Qed.
#[using="Type"] Lemma wcount_block_facts : forall s s', wcount_block nc s = Ok s' -> winv s -> w_symbol s < asz ->
Forall (fun c => - 32768 <= c < 32768) nc ->
Zlength (w_buf s') = bsz /\ w_out s' = w_out s /\ 0 <= w_out s' <= bsz /\ 0 <= w_bitStream s' < 2^32
/\ 0 <= w_bitCount s' <= 44 /\ w_symbol s' = w_symbol s + 1 /\ 1 <= w_remaining s' <= w_remaining s
/\ 1 <= w_nbBits s' <= 13 /\ w_threshold s' = 2^(w_nbBits s' - 1).
Proof.
intros s s' H (LB & RO & RB & BC & SY & RM & NB & TH) SYA NCR.
apply wcount_block_inv in H. cbv zeta in H. destruct H as (thr' & nb' & LR & BCR & R1 & SHR & ->).
apply shrink_facts in SHR; [| exact R1 | lia | exact TH].
cbn [w_buf w_out w_bitStream w_bitCount w_symbol w_remaining w_threshold w_nbBits w_previousIs0].
pose proof (u32_range (w_bitStream s + u32 (u32 (if w_threshold s <=? Znth (w_symbol s) nc + 1
then Znth (w_symbol s) nc + 1 + (2 * w_threshold s - 1 - w_remaining s) else Znth (w_symbol s) nc + 1) * 2 ^ w_bitCount s))) as RU.
assert (CR : - 32768 <= Znth (w_symbol s) nc < 32768).
{ unfold Znth. apply (proj1 (Forall_forall _ _) NCR). apply nth_In. unfold Zlength in LR. lia. }
repeat split; try lia.
- match goal with |- context [if ?c <? ?d then 1 else 0] => destruct (c <? d) end; lia.
- match goal with |- context [if ?c <? ?d then 1 else 0] => destruct (c <? d) end; lia.
- destruct (Z.ltb_spec (Znth (w_symbol s) nc) 0); lia.
Qed.
#[using="Type"] Lemma wcount_flush_facts : forall s s2 s3, wcount_block nc s = Ok s2 -> wflush_if bsz safe s2 = Ok s3 ->
winv s -> w_symbol s < asz -> Forall (fun c => - 32768 <= c < 32768) nc ->
winv s3 /\ w_symbol s3 = w_symbol s + 1 /\ same_ctl s2 s3.
Proof.
intros s s2 s3 H FL WI SYA NCR. pose proof WI as (LB & RO & RB & BC & SY & RM & NB & TH).
apply (wcount_block_facts s s2 H WI SYA) in NCR. destruct NCR as (LB2 & O2 & RO2 & RB2 & BC2 & SY2 & RM2 & NB2 & TH2).
apply wflush_if_inv in FL. destruct FL as [[G FL]|[G ->]].
- apply wflush_facts in FL; [| exact LB2 | exact RB2]. unfold same_ctl in *.
destruct FL as ((E1 & E2 & E3 & E4) & SY3 & LB3 & RO3 & O3 & RB3 & BC3).
unfold winv. repeat split; try congruence; try lia.
- unfold winv, same_ctl. repeat split; try congruence; try lia.
Qed.
#[using="Type"] Lemma wloop_winv : forall f s sf, wloop nc asz bsz safe f s = Ok sf -> winv s ->
Forall (fun c => - 32768 <= c < 32768) nc -> winv sf.
Proof.
induction f as [|f IH]; intros s sf WL WI NCR; [discriminate|].
rewrite wloop_S in WL. destruct ((w_symbol s <? asz) && (1 <? w_remaining s)) eqn:CND; [| injection WL as <-; exact WI].
apply andb_true_iff in CND. destruct CND as [CS CR]. apply Z.ltb_lt in CS.
apply bind_inv in WL. destruct WL as (fl & WB & WL). unfold wbody in WB.
apply bind_inv in WB. destruct WB as (fl0 & ZB & WB).
assert (CNT : forall sa, fl0 = Cont sa -> winv sa -> w_symbol sa < asz -> winv sf).
{ intros sa -> WIA SYA. apply bind_inv in WB. destruct WB as (sc & CB & WB). apply bind_inv in WB. destruct WB as (sd & FL & WB).
injection WB as <-. destruct (wcount_flush_facts sa sc sd CB FL WIA SYA NCR) as (WID & _ & _).
eapply IH; eassumption. }
destruct (w_previousIs0 s).
- pose proof (wzero_block_facts s fl0 ZB WI CS) as ZF. destruct fl0 as [sa|sa].
+ destruct ZF as (WIA & _ & SYA & _). eapply CNT; [reflexivity| exact WIA| lia].
+ injection WB as <-. injection WL as <-. destruct ZF as (SYA & BUA & OUA & BSA & BCA & (C1 & C2 & C3 & C4)).
destruct WI as (LB & RO & RB & BC & SY & RM & NBI & TH).
unfold winv. rewrite BUA, OUA, BSA, BCA, SYA, C1, C2, C3. repeat split; try assumption; try lia.
- injection ZB as <-. eapply CNT; [reflexivity| exact WI| exact CS].
Qed.
End Fields.
Lemma write_generic_bsz : forall buf nc msv tl safe buf' n,
write_ncount_generic buf nc msv tl safe = Ok (buf', n) -> 5 <= tl <= 12 -> 0 <= msv ->
Forall (fun c => - 32768 <= c < 32768) nc -> 2 <= Zlength buf.
Proof.
intros buf nc msv tl safe buf' n H TL MSV NCR. unfold write_ncount_generic in H. cbv zeta in H.
apply bind_inv in H. destruct H as (s0 & WI0 & H). apply bind_inv in H. destruct H as (sf & WL & WF).
assert (WINV0 : winv (msv + 1) (Zlength buf) s0).
{ unfold winit, assert in WI0.
replace ((0 <=? tl) && (tl <? 31)) with true in WI0 by (symmetry; apply andb_true_iff; split; [apply Z.leb_le| apply Z.ltb_lt]; lia).
cbn [bind] in WI0. apply bind_inv in WI0. destruct WI0 as (v & _ & WI0). injection WI0 as <-.
assert (P2 : 32 <= 2^tl <= 4096).
{ split; [change 32 with (2^5)| change 4096 with (2^12)]; apply Z.pow_le_mono_r; lia. }
unfold winv. cbn [w_buf w_out w_bitStream w_bitCount w_symbol w_remaining w_threshold w_nbBits w_previousIs0].
pose proof (u32_range v). replace (tl + 1 - 1) with tl by lia.
assert (0 <= Zlength buf) by (unfold Zlength; lia). repeat split; lia. }
pose proof (wloop_winv nc (msv + 1) (Zlength buf) safe _ _ _ WL WINV0 NCR) as (LB & RO & _).
unfold wfinish in WF. destruct (negb (w_remaining sf =? 1)); [discriminate|].
destruct (negb safe && (Zlength buf - 2 <? w_out sf)); [discriminate|].
apply bind_inv in WF. destruct WF as (b1 & S1 & WF). apply bind_inv in WF. destruct WF as (b2 & S2 & _).
apply store_inv in S1. destruct S1 as [O1 ->]. apply store_inv in S2. destruct S2 as [O2 _].
rewrite Zlength_Zupd in O2. lia.
Qed.

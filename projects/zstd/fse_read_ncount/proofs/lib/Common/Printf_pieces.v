(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import PropExec MState Mem Exec ITree Nodes.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import Prelim Monad.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import SoftFloat FmtFp.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import Stdio.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import Printf_model Printf_mlib Printf_fmts.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Lemma impl_post_evt : forall segs {node R} (atn : node -> machine_state -> Prop) (t : itree node R) (Q Q' : R -> machine_state -> Prop) ms,
ITree.impl segs atn t Q ms -> (forall r ms', Q r ms' -> evt segs (Q' r) ms') -> ITree.impl segs atn t Q' ms.
Proof.
intros segs node R atn t. induction t as [r|n k IH]; intros Q Q' ms H HQ; cbn in *.
- eapply evt_cut; [exact H|]. exact (HQ r).
- eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp. eapply IH; [apply Hk | exact HQ].
Qed.
Lemma implM_post_evt : forall segs {St A} (c : M St A) s (Q Q' : A -> St -> machine_state -> Prop) ms,
Monad.implM segs c s Q ms -> (forall a s' ms', Q a s' ms' -> evt segs (Q' a s') ms') -> Monad.implM segs c s Q' ms.
Proof.
intros segs St A c s Q Q' ms H HQ. unfold Monad.implM in *. eapply impl_post_evt; [exact H|].
intros [|[a s']] ms'; cbn; [intros _; apply evt_done; exact I | apply HQ].
Qed.
Section Outs.
Variable segs : list Segment.
Context {St : Type}.
Variable OUT : list Z -> M St unit.
Variable OUTFP : Z -> Z -> Z -> Z -> Z -> M St Z.
Local Notation implM := (Monad.implM segs).
Fixpoint outsk {B} (ps : list (list Z)) (k : M St B) : M St B :=
match ps with
| [] => k
| p :: ps' => OUT p ;;; outsk ps' k
end.
#[using="Type"] Lemma outsk_app : forall {B} ps qs (k : M St B), outsk (ps ++ qs) k = outsk ps (outsk qs k).
Proof. induction ps as [|p ps IH]; intros qs k; [reflexivity|]. cbn [outsk app]. rewrite IH. reflexivity. Qed.
#[using="Type"] Lemma outsk_mono : forall {B} ps (k1 k2 : M St B) Q,
(forall s ms, implM k1 s Q ms -> implM k2 s Q ms) ->
forall s ms, implM (outsk ps k1) s Q ms -> implM (outsk ps k2) s Q ms.
Proof.
induction ps as [|p ps IH]; intros k1 k2 Q HK s ms H; cbn [outsk] in *; [apply HK; exact H|].
eapply implM_bind_ext; [|exact H]. intros x s' ms' H'. eapply IH; [exact HK | exact H'].
Qed.
#[using="Type"] Lemma mpad_outs : forall {B} c w l fl pp (K : unit -> M St B) s Q ms,
pad_pieces c w l fl = Some pp ->
implM (mbind (mpad OUT c w l fl) K) s Q ms -> implM (outsk pp (K tt)) s Q ms.
Proof.
intros B c w l fl pp K s Q ms P H. unfold mpad, pad_pieces in *.
destruct (negb (Z.land fl (Z.lor LEFT_ADJ ZERO_PAD) =? 0) || (w <=? l))%bool.
- inversion P; subst. cbn [outsk]. apply implM_ret_l_rev in H. exact H.
- destruct (256 <=? w - l); [discriminate|]. inversion P; subst. cbn [outsk].
eapply implM_bind_ext; [|exact H]. intros [] s' ms' H'. exact H'.
Qed.
#[using="Type"] Lemma conv_tail_outs : forall {B} cnt fl w p prefix body ps r (K : Z -> M St B) s Q ms,
tail_pieces cnt fl w p prefix body = Some (ps, r) ->
implM (mbind (conv_tail OUT cnt fl w p prefix body) K) s Q ms -> implM (outsk ps (K r)) s Q ms.
Proof.
intros B cnt fl w p prefix body ps r K s Q ms T H. unfold conv_tail, tail_pieces in *. cbv zeta in T. cbv zeta in H.
destruct (INT_MAX - zlength prefix <? Z.max p (zlength body)); [discriminate|].
destruct (INT_MAX - cnt <? Z.max w (zlength prefix + Z.max p (zlength body))); [discriminate|].
destruct (pad_pieces 32 _ _ fl) as [p1|] eqn:P1; [|discriminate].
destruct (pad_pieces 48 _ _ (Z.lxor fl ZERO_PAD)) as [p2|] eqn:P2; [|discriminate].
destruct (pad_pieces 48 _ _ 0) as [p3|] eqn:P3; [|discriminate].
destruct (pad_pieces 32 _ _ (Z.lxor fl LEFT_ADJ)) as [p4|] eqn:P4; [|discriminate].
inversion T; subst. clear T.
match goal with |- implM (outsk ?L (K ?rr)) _ _ _ =>
replace (outsk L (K rr)) with (outsk p1 (OUT prefix ;;; outsk p2 (outsk p3 (OUT body ;;; outsk p4 (K rr)))))
by (rewrite ?outsk_app; cbn [outsk]; rewrite ?outsk_app; cbn [outsk]; reflexivity) end.
apply implM_assoc_rev in H. apply (mpad_outs _ _ _ _ _ _ _ _ _ P1) in H. cbv beta in H.
eapply outsk_mono; [|exact H]. clear H. cbv beta. intros s1 ms1 H.
apply implM_assoc_rev in H. eapply implM_bind_ext; [|exact H]. clear H. cbv beta. intros x2 s2 ms2 H.
apply implM_assoc_rev in H. apply (mpad_outs _ _ _ _ _ _ _ _ _ P2) in H. cbv beta in H.
eapply outsk_mono; [|exact H]. clear H. cbv beta. intros s3 ms3 H.
apply implM_assoc_rev in H. apply (mpad_outs _ _ _ _ _ _ _ _ _ P3) in H. cbv beta in H.
eapply outsk_mono; [|exact H]. clear H. cbv beta. intros s4 ms4 H.
apply implM_assoc_rev in H. eapply implM_bind_ext; [|exact H]. clear H. cbv beta. intros x5 s5 ms5 H.
apply implM_assoc_rev in H. apply (mpad_outs _ _ _ _ _ _ _ _ _ P4) in H. cbv beta in H.
eapply outsk_mono; [|exact H]. clear H. cbv beta. intros s6 ms6 H.
apply implM_ret_l_rev in H. exact H.
Qed.
#[using="Type"] Lemma conv_int_outs : forall {B} cnt fl w p xp argi prefix body ps r (K : Z -> M St B) s Q ms,
int_pieces cnt fl w p xp argi prefix body = Some (ps, r) ->
implM (mbind (conv_int OUT cnt fl w p xp argi prefix body) K) s Q ms -> implM (outsk ps (K r)) s Q ms.
Proof.
intros B cnt fl w p xp argi prefix body ps r K s Q ms T H. unfold conv_int, int_pieces in *.
destruct (xp && (p <? 0))%bool; [discriminate|]. cbv zeta in T. cbv zeta in H.
destruct ((argi =? 0) && (p =? 0))%bool; eapply conv_tail_outs; eassumption.
Qed.
#[using="Type"] Lemma conv_outs : forall {B} cnt d a ps r (K : Z -> M St B) s Q ms,
conv_pieces cnt d a = Some (ps, r) ->
implM (mbind (conv OUT OUTFP cnt d a) K) s Q ms -> implM (outsk ps (K r)) s Q ms.
Proof.
intros B cnt d a ps r K s Q ms T H. unfold conv, conv_pieces in *. cbv zeta in T. cbv zeta in H.
destruct a as [str|i|u|dd].
- destruct (negb (d_ty d =? T_PTR)); [discriminate|].
destruct ((d_p d <? 0) && (INT_MAX <=? zlength str))%bool; [discriminate|].
eapply conv_tail_outs; eassumption.
- destruct (negb (d_ty d =? T_INT)); [discriminate|].
destruct (INTMAX_MAX <? i mod 2 ^ 64);
[|destruct (negb (Z.land _ MARK_POS =? 0)); [|destruct (negb (Z.land _ PAD_POS =? 0))]];
eapply conv_int_outs; eassumption.
- destruct (negb (d_ty d =? T_UINT)); [discriminate|].
destruct (d_t d =? 117); eapply conv_int_outs; eassumption.
- discriminate.
Qed.
#[using="Type"] Lemma printf_loop_outs : forall {B} fuel s args cnt ps r (k : Z -> M St B) st Q ms,
printf_pieces_loop fuel s args cnt = Some (ps, r) ->
implM (mbind (printf_loop OUT OUTFP fuel s args cnt) k) st Q ms -> implM (outsk ps (k r)) st Q ms.
Proof.
induction fuel as [|fuel IH]; intros s args cnt ps r k st Q ms P H; [discriminate|].
cbn [printf_pieces_loop] in P. cbn [printf_loop] in H.
destruct s as [|c s1]; [discriminate|].
destruct (c =? 0). { inversion P; subst. cbn [outsk]. apply implM_ret_l_rev in H. exact H. }
cbv zeta in P. cbv zeta in H. remember (lit_run (c :: s1)) as lit eqn:Hlit. clear Hlit.
destruct (skipn (Datatypes.length lit) (c :: s1)) as [|c1 s2]; [discriminate|].
destruct ((c1 =? 37) && match s2 with [] => true | c2 :: _ => c2 =? 37 end)%bool; [discriminate|].
destruct (0 <? zlength lit).
- destruct (INT_MAX - cnt <? zlength lit); [discriminate|].
destruct (printf_pieces_loop fuel (c1 :: s2) args (cnt + zlength lit)) as [[ps' r']|] eqn:R; [|discriminate].
inversion P; subst. clear P. cbn [outsk].
apply implM_assoc_rev in H. eapply implM_bind_ext; [|exact H]. cbv beta. intros x s' ms' H'.
eapply IH; [exact R | exact H'].
- destruct (parse_dir s2) as [[d s3]|]; [|discriminate]. destruct args as [|a args']; [discriminate|].
destruct (conv_pieces cnt d a) as [[ps1 cnt']|] eqn:C; [|discriminate].
destruct (printf_pieces_loop fuel s3 args' cnt') as [[ps2 r2]|] eqn:R; [|discriminate].
inversion P; subst. clear P.
match goal with |- implM (outsk ?L (k ?rr)) _ _ _ =>
replace (outsk L (k rr)) with (outsk [[]] (outsk ps1 (outsk ps2 (k rr)))) by (rewrite <- !outsk_app; reflexivity) end.
cbn [outsk].
apply implM_assoc_rev in H. eapply implM_bind_ext; [|exact H]. cbv beta. intros x s' ms' H'.
apply implM_assoc_rev in H'. apply (conv_outs _ _ _ _ _ _ _ _ _ C) in H'.
eapply outsk_mono; [|exact H']. cbv beta. intros s'' ms'' H''. eapply IH; [exact R | exact H''].
Qed.
#[using="Type"] Theorem printf_model_outs : forall {B} fmt args ps r (k : Z -> M St B) st Q ms,
printf_pieces fmt args = Some (ps, r) ->
implM (mbind (printf_model OUT OUTFP fmt args) k) st Q ms -> implM (outsk ps (k r)) st Q ms.
Proof. intros B fmt args ps r k st Q ms P H. eapply printf_loop_outs; [exact P | exact H]. Qed.
End Outs.
Lemma zlength_nonneg' : forall {A} (l : list A), 0 <= zlength l.
Proof. intros. unfold zlength. Local Ltac2 Set LiaHints.tbl := fun () => "0010=53421126490.2000001S".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma conv_pieces_s : forall cnt s, 0 <= cnt -> zlength s < INT_MAX - cnt ->
conv_pieces cnt {| d_fl := 0; d_w := 0; d_p := -1; d_xp := false; d_t := 115; d_ty := T_PTR |} (PA_s s)
= Some ([[]; s], cnt + zlength s).
Proof.
intros cnt s Hc Hs. pose proof (zlength_nonneg' s) as H0.
unfold conv_pieces. cbn [d_fl d_w d_p d_xp d_t d_ty]. cbv beta iota zeta delta [Z.eqb Z.land LEFT_ADJ negb T_PTR Pos.eqb andb Z.ltb Z.compare].
Local Ltac2 Set LiaHints.tbl := fun () => "0070=23616751592.537615760183.542718853283.549099695022.553389180807.561992265185.566166185657.500000700>00?00C00G00H00IS2Hc2HsS2Hc2HsSS2H0S2HsSS".
replace (INT_MAX <=? zlength s) with false by (symmetry; apply Z.leb_gt; lia).
unfold tail_pieces. cbv zeta. rewrite firstn_all2 by (unfold zlength; lia).
change (zlength (@nil Z)) with 0.
replace (Z.max (zlength s) (zlength s)) with (zlength s) by lia.
replace (INT_MAX - 0 <? zlength s) with false by (symmetry; apply Z.ltb_ge; lia).
replace (Z.max 0 (0 + zlength s)) with (zlength s) by lia.
replace (INT_MAX - cnt <? zlength s) with false by (symmetry; apply Z.ltb_ge; lia).
unfold pad_pieces.
replace (zlength s <=? 0 + zlength s) with true by (symmetry; apply Z.leb_le; lia).
rewrite Z.leb_refl. cbn [orb negb Z.land Z.lxor Z.lor Z.eqb Z.lnot ZERO_PAD LEFT_ADJ].
reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma ppl_unfold : forall fuel s args cnt,
printf_pieces_loop (S fuel) s args cnt =
match s with
| [] => None
| c :: _ =>
if c =? 0 then Some ([], cnt) else
let lit := lit_run s in
let l := zlength lit in
let s1 := skipn (Datatypes.length lit) s in
match s1 with
| [] => None
| c1 :: s2 =>
if (c1 =? 37) && match s2 with [] => true | c2 :: _ => c2 =? 37 end then None
else if 0 <? l then
(if INT_MAX - cnt <? l then None
else match printf_pieces_loop fuel s1 args (cnt + l) with Some (ps, r) => Some (lit :: ps, r) | None => None end)
else
match parse_dir s2, args with
| Some (d, s3), a :: args' =>
match conv_pieces cnt d a with
| Some (ps1, cnt') =>
match printf_pieces_loop fuel s3 args' cnt' with Some (ps, r) => Some ([] :: ps1 ++ ps, r) | None => None end
| None => None
end
| _, _ => None
end
end
end.
Proof. reflexivity. Qed.
Lemma ppl_noargs_shift_gen : forall fuel s c0 ps r,
printf_pieces_loop fuel s [] c0 = Some (ps, r) ->
c0 <= r /\ (forall k, 0 <= k -> r + k <= INT_MAX -> printf_pieces_loop fuel s [] (c0 + k) = Some (ps, r + k)).
Proof.
induction fuel as [|fuel IH]; intros s c0 ps r P; [discriminate|].
rewrite ppl_unfold in P. setoid_rewrite ppl_unfold.
destruct s as [|c s1]; [discriminate|].
destruct (c =? 0). { inversion P; subst. Local Ltac2 Set LiaHints.tbl := fun () => "0040>21057752940.183532215338.6  3827262817.18 65616394080.1500000700800900?S2LE2HrSSS1H2LE".
split; [lia|]. intros k _ _. reflexivity. }
cbv zeta in P. cbv zeta. remember (lit_run (c :: s1)) as lit eqn:Hlit. clear Hlit.
destruct (skipn (Datatypes.length lit) (c :: s1)) as [|c1 s2]; [discriminate|].
destruct ((c1 =? 37) && match s2 with [] => true | c2 :: _ => c2 =? 37 end)%bool; [discriminate|].
pose proof (zlength_nonneg' lit).
destruct (0 <? zlength lit).
- destruct (Z.ltb_spec (INT_MAX - c0) (zlength lit)); [discriminate|].
destruct (printf_pieces_loop fuel (c1 :: s2) [] (c0 + zlength lit)) as [[ps' r']|] eqn:R; [|discriminate].
inversion P; subst. clear P. destruct (IH _ _ _ _ R) as [LE SH].
split; [lia|]. intros k Hk Hr.
replace (INT_MAX - (c0 + k) <? zlength lit) with false by (symmetry; apply Z.ltb_ge; lia).
replace (c0 + k + zlength lit) with (c0 + zlength lit + k) by lia. rewrite (SH k Hk Hr). reflexivity.
- destruct (parse_dir s2) as [[d s3]|]; discriminate.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma ppl_noargs_shift : forall fuel s cnt ps r,
printf_pieces_loop fuel s [] 0 = Some (ps, r) -> 0 <= cnt -> cnt + r <= INT_MAX ->
printf_pieces_loop fuel s [] cnt = Some (ps, cnt + r).
Proof.
intros fuel s cnt ps r P Hc Hr. destruct (ppl_noargs_shift_gen _ _ _ _ _ P) as [_ SH].
rewrite <- (Z.add_0_l cnt). Local Ltac2 Set LiaHints.tbl := fun () => "0020=17417920673.96715927675.9 000001005SS2Hr".
rewrite (SH cnt Hc ltac:(lia)). f_equal. f_equal. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Ltac ppl_step := rewrite ppl_unfold; match goal with |- ?l = _ => let l' := eval cbv -[printf_pieces_loop conv_pieces] in l in change l with l' end.
Lemma printf_pieces_usage : forall s, zlength s < INT_MAX - 256 ->
printf_pieces FMT_usage [PA_s s] = Some (pieces_usage s, 14 + zlength s).
Proof.
intros s Hs. pose proof (zlength_nonneg' s) as H0. unfold printf_pieces.
change (Datatypes.length FMT_usage) with 17%nat.
ppl_step. ppl_step. change Printf_model.T_PTR with T_PTR. Local Ltac2 Set LiaHints.tbl := fun () => "0050=18377774667.324948812865.328262836163.336381560612.352329333790.300000400800900=00>S2HsS2H0SS2HsS".
rewrite conv_pieces_s by lia.
rewrite (ppl_noargs_shift 15 [32; 73; 78; 80; 85; 84; 10; 0] (7 + zlength s) [[32; 73; 78; 80; 85; 84; 10]] 7 ltac:(vm_compute; reflexivity)) by lia.
unfold pieces_usage. cbv -[zlength Z.add]. do 2 f_equal; try lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma printf_pieces_cannot_open : forall s, zlength s < INT_MAX - 256 ->
printf_pieces FMT_cannot_open [PA_s s] = Some (pieces_cannot_open s, 18 + zlength s).
Proof.
intros s Hs. pose proof (zlength_nonneg' s) as H0. unfold printf_pieces.
change (Datatypes.length FMT_cannot_open) with 21%nat.
ppl_step. ppl_step. change Printf_model.T_PTR with T_PTR. Local Ltac2 Set LiaHints.tbl := fun () => "0050=25814479332.333886658155.346916387587.353989977022.356024884833.300000400800900:00>S2HsS2HsSSS2H0".
rewrite conv_pieces_s by lia.
rewrite (ppl_noargs_shift 19 [10; 0] (17 + zlength s) [[10]] 1 ltac:(vm_compute; reflexivity)) by lia.
unfold pieces_cannot_open. cbv -[zlength Z.add]. do 2 f_equal; try lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma printf_pieces_read_error : forall s, zlength s < INT_MAX - 256 ->
printf_pieces FMT_read_error [PA_s s] = Some (pieces_read_error s, 20 + zlength s).
Proof.
intros s Hs. pose proof (zlength_nonneg' s) as H0. unfold printf_pieces.
change (Datatypes.length FMT_read_error) with 23%nat.
ppl_step. ppl_step. change Printf_model.T_PTR with T_PTR. Local Ltac2 Set LiaHints.tbl := fun () => "0050=11139304900.328746894723.333104299009.337683094923.38290658782.3 00000400500900=00>S2HsSS2H0S2HsS".
rewrite conv_pieces_s by lia.
rewrite (ppl_noargs_shift 21 [10; 0] (19 + zlength s) [[10]] 1 ltac:(vm_compute; reflexivity)) by lia.
unfold pieces_read_error. cbv -[zlength Z.add]. do 2 f_equal; try lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma printf_pieces_too_big : printf_pieces FMT_too_big [PA_u 67108864] = Some (pieces_too_big, 38).
Proof. vm_compute. reflexivity. Qed.
Lemma digits_aux_length : forall fuel b dig x acc, (length (Printf_model.digits_aux fuel b dig x acc) <= fuel + length acc)%nat.
Proof. Local Ltac2 Set LiaHints.tbl := fun () => "0030=15495545192.624928963119.447839791572.6000004005006S2IHSS".
induction fuel as [|fuel IH]; intros; cbn [Printf_model.digits_aux]; [lia|]. destruct (x =? 0); [cbn; lia|]. specialize (IH b dig (x / b) (dig (x mod b) :: acc)). cbn [length] in IH. lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma digits_aux_length_ge : forall fuel b dig x acc, (length acc <= length (Printf_model.digits_aux fuel b dig x acc))%nat.
Proof. Local Ltac2 Set LiaHints.tbl := fun () => "0030=11631307396.650209154892.450209154892.6000004005006S2IHSS".
induction fuel as [|fuel IH]; intros; cbn [Printf_model.digits_aux]; [lia|]. destruct (x =? 0); [lia|]. specialize (IH b dig (x / b) (dig (x mod b) :: acc)). cbn [length] in IH. lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma dec_digits_length : forall x, zlength (dec_digits x) <= 20.
Proof. intros x. unfold zlength, dec_digits. pose proof (digits_aux_length 20 10 (fun v => 48 + v) x []) as H. cbn [length Nat.add] in H. Local Ltac2 Set LiaHints.tbl := fun () => "0010<8017950831.2000003S1H".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma digits_aux_unfold : forall f b dig x acc,
Printf_model.digits_aux (S f) b dig x acc = if x =? 0 then acc else Printf_model.digits_aux f b dig (x / b) (dig (x mod b) :: acc).
Proof. reflexivity. Qed.
Lemma dec_digits_pos : forall x, 0 < x -> 1 <= zlength (dec_digits x).
Proof.
intros x Hx. unfold zlength, dec_digits. change 20%nat with (S 19). rewrite digits_aux_unfold.
Local Ltac2 Set LiaHints.tbl := fun () => "0020=32794156492.241539400765.3000004007S2HxS1H".
replace (x =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
pose proof (digits_aux_length_ge 19 10 (fun v => 48 + v) (x / 10) [48 + x mod 10]) as H. cbn [length] in H. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma dec_digits_fmt_u : forall x, dec_digits x = fmt_u x.
Proof.
intros x. unfold dec_digits, fmt_u.
assert (G : forall fuel y acc, Printf_model.digits_aux fuel 10 (fun v => 48 + v) y acc = Stdio.digits_aux fuel y acc).
{ induction fuel as [|fuel IH]; intros; cbn [Printf_model.digits_aux Stdio.digits_aux]; [reflexivity|]. destruct (y =? 0); [reflexivity|]. apply IH. }
apply G.
Qed.
Definition pct_d_conv_pieces (v : Z) : list (list Z) :=
if v =? 0 then [[]; [48]; []] else if v <? 0 then [[45]; dec_digits (- v)] else [[]; dec_digits v].
Definition pct_d_conv_len (v : Z) : Z :=
if v =? 0 then 1 else if v <? 0 then 1 + zlength (dec_digits (- v)) else zlength (dec_digits v).
Lemma tail_pieces_plain : forall cnt p prefix body,
0 <= cnt -> zlength prefix <= 2 -> zlength body <= 20 -> -1 <= p <= 21 -> cnt + 24 <= INT_MAX ->
tail_pieces cnt 0 0 p prefix body =
Some ([prefix] ++ (if Z.max p (zlength body) <=? zlength body then [] else [zrepeat 48 (Z.max p (zlength body) - zlength body)]) ++ [body],
cnt + (zlength prefix + Z.max p (zlength body))).
Proof.
intros cnt p prefix body Hc Hpl Hn Hp Hi.
pose proof (zlength_nonneg' prefix) as P0. pose proof (zlength_nonneg' body) as B0.
unfold tail_pieces. cbv zeta.
Local Ltac2 Set LiaHints.tbl := fun () => "0040>13888849306.1119286901771.1140586065903.1154398281092.1200000>00E00P00WS3Hpl2Hn2Hp2HiS2P02B0S3Hpl2Hn2HpS2Hp2B0".
replace (INT_MAX - zlength prefix <? Z.max p (zlength body)) with false by (symmetry; apply Z.ltb_ge; unfold INT_MAX; lia).
replace (Z.max 0 (zlength prefix + Z.max p (zlength body))) with (zlength prefix + Z.max p (zlength body)) by lia.
match goal with |- context [if ?c then None else _] => replace c with false by (symmetry; apply Z.ltb_ge; unfold INT_MAX in *; lia) end.
unfold pad_pieces. rewrite !Z.leb_refl. cbn [Z.land Z.lxor Z.lor LEFT_ADJ ZERO_PAD Z.eqb negb orb].
destruct (Z.leb_spec0 (Z.max p (zlength body)) (zlength body)) as [LE|GT].
- cbn [app]. reflexivity.
- replace (256 <=? Z.max p (zlength body) - zlength body) with false by (symmetry; apply Z.leb_gt; lia). cbn [app]. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma conv_pieces_d : forall cnt v, 0 <= cnt -> cnt + 24 <= INT_MAX -> -2^31 <= v < 2^31 ->
conv_pieces cnt {| d_fl := 0; d_w := 0; d_p := -1; d_xp := false; d_t := 100; d_ty := T_INT |} (PA_i v)
= Some (pct_d_conv_pieces v, cnt + pct_d_conv_len v).
Proof.
intros cnt v Hc Hi Hv.
unfold conv_pieces, pct_d_conv_pieces, pct_d_conv_len, int_pieces.
destruct (Z.eq_dec v 0) as [->|NZ].
- cbv -[tail_pieces].
Local Ltac2 Set LiaHints.tbl := fun () => "00J0>14593422957.8 19340382120.4 24590202220.1027339668945.8 29440610551.7 36930333427.9 37063004105.1037063004105.9 41415983368.4 41416055922.9 46338795142.9 5320615597.10 53334512447.4 53816872974.1053816872974.9 53817068916.4 54238493373.7 56332908809.7 60093098107.7 60093129575.7 6029663917.10 6029663917.9  6029722583.4  60360261763.8 61301372577.7 9538541126.10 00000400500900>00F00J00Q00X00Y00Z00^00b00c00g00k00o01701;01C01H01L01P01T01Y01^01_S2HvSS2DPS3NEGS2Hv3POSS2DLS2DP2DLS2DP2DLSSS2DPS2DLSS2HcS2HcS2HcS3POS2NZS2HvS2NZ3POSS3NEGS2HiS2HiS2HiS3NEGS3NEGS".
rewrite tail_pieces_plain by (try change (zlength (@nil Z)) with 0; lia).
change (zlength (@nil Z)) with 0. cbn. reflexivity.
- destruct (Z.lt_ge_cases v 0) as [NEG|POS].
+ replace (v <? 0) with true by (symmetry; apply Z.ltb_lt; lia).
replace (v =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
cbv -[tail_pieces dec_digits Z.modulo Z.ltb Z.opp Z.pow zlength Z.add Z.max Z.eqb].
change (10 =? 10) with true. change (0 =? 0) with true. cbv iota.
assert (M1 : v mod 2^64 = v + 2^64) by (Z.div_mod_to_equations; nia).
rewrite M1.
replace (9223372036854775807 <? v + 2^64) with true by (symmetry; apply Z.ltb_lt; lia).
replace ((- (v + 2^64)) mod 2^64) with (- v) by (Z.div_mod_to_equations; nia).
replace (- v =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbv iota.
pose proof (dec_digits_pos (- v) ltac:(lia)) as DP. pose proof (dec_digits_length (- v)) as DL.
rewrite Z.add_0_r.
rewrite tail_pieces_plain by (try change (zlength [45]) with 1; lia).
replace (Z.max (Z.max (-1) (zlength (dec_digits (- v)))) (zlength (dec_digits (- v)))) with (zlength (dec_digits (- v))) by lia.
rewrite Z.leb_refl. change (zlength [45]) with 1. cbn [app]. reflexivity.
+ replace (v <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
replace (v =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
cbv -[tail_pieces dec_digits Z.modulo Z.ltb Z.opp Z.pow zlength Z.add Z.max Z.eqb].
change (10 =? 10) with true. change (0 =? 0) with true. cbv iota.
rewrite (Z.mod_small v (2^64)) by lia.
replace (9223372036854775807 <? v) with false by (symmetry; apply Z.ltb_ge; lia).
change (0 =? 0) with true. cbv beta iota zeta.
replace (v =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbv beta iota zeta.
pose proof (dec_digits_pos v ltac:(lia)) as DP. pose proof (dec_digits_length v) as DL.
rewrite ?Z.add_0_r.
rewrite tail_pieces_plain by (try change (zlength (@nil Z)) with 0; lia).
replace (Z.max (Z.max (-1) (zlength (dec_digits v))) (zlength (dec_digits v))) with (zlength (dec_digits v)) by lia.
rewrite Z.leb_refl. change (zlength (@nil Z)) with 0. cbn [app]. rewrite ?Z.add_0_l. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Definition pct_d_len (v : Z) : Z := pct_d_conv_len v + 1.
Lemma printf_pieces_pct_d : forall v, -2^31 <= v < 2^31 ->
printf_pieces FMT_pct_d [PA_i v] = Some (pieces_pct_d v, pct_d_len v).
Proof.
intros v Hv. unfold printf_pieces.
change (Datatypes.length FMT_pct_d) with 4%nat.
ppl_step. change 10 with T_INT at 1. fold (@app (list Z)).
pose proof (zlength_nonneg' (dec_digits v)). pose proof (zlength_nonneg' (dec_digits (- v))).
pose proof (dec_digits_length v). pose proof (dec_digits_length (- v)).
rewrite conv_pieces_d by (unfold INT_MAX; lia).
rewrite (ppl_noargs_shift 3 [10; 0] (0 + pct_d_conv_len v) [[10]] 1 ltac:(vm_compute; reflexivity))
by (unfold pct_d_conv_len, INT_MAX; destruct (v =? 0); [lia|]; destruct (v <? 0); lia).
unfold pieces_pct_d, pct_d_conv_pieces, pct_d_len, pct_d_conv_len.
rewrite <- ?dec_digits_fmt_u.
destruct (v =? 0); [cbn; reflexivity|]. destruct (v <? 0); cbn -[zlength Z.add dec_digits]; do 2 f_equal; lia.
Qed.

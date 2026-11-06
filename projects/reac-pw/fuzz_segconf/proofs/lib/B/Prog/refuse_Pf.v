(* reac-pw/fuzz_segconf, ASan+UBSan image B (fuzz_segconf.asan-ubsan, pin sha256 c3796c0b38f3...): the printf-family
   and record facts of refuse's image-B prefix walk (a sub-lane of a sub-lane, the image-B refuse walk lane, the image-B G3 walk owner, 2026-10-30).
   Proves no function of the binary: no symbolic execution, no machine code. The lemmas are over readers
   (`reader = Z -> option Z`), the contract lib/B/Prog/refuse_c.v (refuse_va_locs), the vocabulary
   lib/B/Prog/SegABase.v (sa_lit, sa_str, sa_addr, sa_va_args, sa_heap, sa_fframe, sa_rconf), the model
   lib/Spec/SegModel.v (r_where, r_addr_fmt, r_addr_args, refuse, fmt) and the printf texts lib/B/Prog/refuse_pft.v
   (ffr_fmt, ffr_args, REFUSE_ALL_FMTS), with lib/B/Prog/refuse_f.v's functional lemmas as the engine.

   refuse (reac_segconf.c:30-48), when c->n_refusals < 8, prints
     k = snprintf(dst, 200, line > 0 ? "%s:%d: " : "%s: ", where[, line]);   dst = c->refusal[n]
     vsnprintf(dst + k, 200 - k, fmt, ap)
   Its walk takes the two printf rows through refuse_pft.v (r_aj_snprintf_atSF, r_aj_vsnprintf_atSF), each of
   which asks the format family at the call; the walk assumes FFR (refuse_pft.ffr_family), which turns ffr_fmt and
   ffr_args into it. This file builds ffr_fmt and ffr_args from the contract's premises and builds the record the
   post needs:
   A. rbf_str_bytes, rbf_aview_bytes: the bytes of a string an aview reader holds are 1 .. 255;
   B. rbf_ffr_fmt: an image literal below the GOT word, at an AR state, is ffr_fmt;
   C. rbf_ffr_args_addr (the address prefix's arguments), rbf_args_place / rbf_ffr_args_va (the caller's variadic
      words), rbf_args_apart / rbf_args_apart_of_va / rbf_args_place_of_locs (the place facts from refuse_va_locs at
      an AR state and the apart facts from sa_va_args);
   D. rbf_addr_fmt_in, rbf_addr_conv, rbf_fmt_in: the address prefix's format and kinds, a refusal format among
      REFUSE_ALL_FMTS;
   E. rbf_slot_text, rbf_rconf_refuse: the slot's text and the record after the two calls.
   rbf_rconf_refuse takes one premise more than its first text: the bytes of the slot past the text's NUL keep
   their value. rf_upd_slot rebuilds the whole 16616-byte block from the new reader, and the block's keep premise
   over the full 200-byte slot says nothing of those bytes, so without it the new reader may not hold them. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04 YG0v YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YI16 YM05 YN2j.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegSyms SegList SegPa SegPaLib PaLibF PaLibG PaLibH PaSB PaDenot.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase refuse_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require refuse_f refuse_pft.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

Lemma rbf_in_firstn : forall {A : Type} n (l : list A) x, In x (firstn n l) -> In x l.
Proof. intros A n l x H. rewrite <- (firstn_skipn n l). apply in_or_app. left. exact H. Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

(* ===================================== A. bytes of a string a reader holds ===================================== *)
Lemma rbf_str_bytes : forall rd p s, sa_str rd p s -> (forall a v, rd a = Some v -> 0 <= v < 256) ->
  Forall (fun x => 0 < x < 256) s.
Proof.
intros rd p s [[Hzs Hn0] _] Hb.
apply Forall_forall. intros x Hx.
destruct (In_nth s x 0 Hx) as [i [Hi Hn]].
assert (Hi' : (i < length (s ++ [0%Z]))%nat) by (rewrite length_app; cbn [length]; lia).
pose proof (Hzs i Hi') as E. rewrite app_nth1 in E by exact Hi. rewrite Hn in E.
pose proof (Hb _ _ E) as R.
assert (x <> 0) by (intros ->; exact (Hn0 Hx)). lia.
Qed.

Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Lemma rbf_aview_bytes : forall (W : world SEGS) mem p s, sa_str (rdW W mem) p s -> Forall (fun x => 0 < x < 256) s.
Proof.
intros W mem p s H. apply (rbf_str_bytes _ p s H). intros a v E. exact (sa_aview_rng _ _ _ _ _ E).
Qed.

Section e.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.

(* ======================================== B. the format of a call ======================================== *)
(* sa_lit gives the string, the shadow at every AR state (sa_pinned) and the image place; the 8 bytes past the NUL
   are application memory because the literal ends below the GOT word, which is below kImgEnd *)
Lemma rbf_ffr_fmt : forall ly S (W : world SEGS) mem md rs f fmt gotw,
  AR SEGS B ly S W mem md -> sa_lit SEGS B (rdW W mem) f fmt ->
  0x10000 <= f -> f + Z.of_nat (length fmt) + 1 <= gotw -> gotw + 8 <= kImgEnd ->
  Forall (zdisjoint (f, seg_spec.cstr_span f fmt)) rs ->
  refuse_pft.ffr_fmt SEGS B gotw (rdW W mem) rs f fmt.
Proof.
intros ly S W mem md rs f fmt gotw HAR (Hf0 & Hstr & Hpin & _ & Himg) Hlo Hgot Hend Hdis.
unfold refuse_pft.ffr_fmt.
split; [exact Hlo|]. split; [exact Hgot|]. split; [exact Hstr|].
split; [exact (Hpin ly S W mem md HAR)|]. split; [exact Himg|].
split; [|exact Hdis].
apply a3_amem_img; lia.
Qed.

(* ===================================== C. the arguments of the two calls ===================================== *)
(* the address prefix: where (c->reading or "reac-pw.conf") and, for line > 0, the line *)
Lemma rbf_ffr_args_addr : forall (W : world SEGS) mem rs (w ln : Z) (rcs : rconf) (rest : list Z),
  0 < w -> sa_str (rdW W mem) w (SegModel.r_where rcs) ->
  sa_addr (rdW W mem) w (Z.of_nat (length (SegModel.r_where rcs)) + 1) ->
  amem_range w (Z.of_nat (length (SegModel.r_where rcs)) + 8) ->
  (length (SegModel.r_where rcs) <= 95)%nat ->
  Forall (zdisjoint (w, seg_spec.cstr_span w (SegModel.r_where rcs))) rs ->
  0 <= ln < 2 ^ 31 ->
  refuse_pft.ffr_args (rdW W mem) rs (w :: ln :: rest) (SegModel.r_addr_args rcs ln).
Proof.
intros W mem rs w ln rcs rest Hw Hstr Hadr Ham Hlen Hdis Hln.
assert (HA : refuse_pft.ffr_arg (rdW W mem) rs w (SegModel.AS (SegModel.r_where rcs))).
{ cbn [refuse_pft.ffr_arg]. split; [exact Hw|]. split; [exact Hstr|].
  split; [exact (rbf_aview_bytes W mem w _ Hstr)|].
  split; [apply (Nat.le_trans _ 95); [exact Hlen | apply Nat.leb_le; vm_compute; reflexivity]|].
  split; [exact Hadr|]. split; [exact Ham | exact Hdis]. }
unfold SegModel.r_addr_args. destruct (0 <? ln); cbn [refuse_pft.ffr_args].
- split; [exact HA|]. split; [|destruct rest; exact I]. cbn [refuse_pft.ffr_arg]. split; [exact Hln | reflexivity].
- split; [exact HA | exact I].
Qed.

(* the caller's variadic words: for each string argument, the 8 bytes past its NUL in application memory and its
   read span apart from the regions rs the call writes *)
Fixpoint rbf_args_place (rd : reader) (rs : list (Z * Z)) (vs : list word) (xs : list SegModel.arg) {struct xs} : Prop :=
match xs, vs with
| [], _ => True
| SegModel.AS s :: xs', v :: vs' =>
    amem_range (bv_unsigned v) (Z.of_nat (length s) + 8) /\
    Forall (zdisjoint (bv_unsigned v, seg_spec.cstr_span (bv_unsigned v) s)) rs /\
    rbf_args_place rd rs vs' xs'
| SegModel.AI _ :: xs', v :: vs' => rbf_args_place rd rs vs' xs'
| _ :: _, [] => False
end.

Lemma rbf_ffr_args_va : forall (W : world SEGS) mem Wl rs (vs : list word) (xs : list SegModel.arg),
  sa_va_args (rdW W mem) Wl vs xs -> rbf_args_place (rdW W mem) rs vs xs ->
  refuse_pft.ffr_args (rdW W mem) rs (map (fun v : word => bv_unsigned v) vs) xs.
Proof.
intros W mem Wl rs vs xs. revert vs.
induction xs as [|x xs IH]; intros vs Hva Hpl.
- destruct vs; exact I.
- destruct vs as [|v vs]; [exact (False_ind _ Hva)|].
  cbn [sa_va_args] in Hva. destruct Hva as [Hx Hva].
  cbn [map refuse_pft.ffr_args].
  destruct x as [s|z]; cbn [rbf_args_place] in Hpl; cbn [sa_va_arg] in Hx; cbn [refuse_pft.ffr_arg].
  + destruct Hpl as (Ham & Hdis & Hpl). destruct Hx as (Hnz & Hstr & Hlen & Hadr & _).
    split; [|exact (IH vs Hva Hpl)].
    pose proof (bv_unsigned_in_range _ v) as Hr.
    split; [lia|]. split; [exact Hstr|]. split; [exact (rbf_aview_bytes W mem _ s Hstr)|].
    split; [exact Hlen|]. split; [exact Hadr|]. split; [exact Ham | exact Hdis].
  + destruct Hx as [Hz Heq]. split; [split; [exact Hz | exact Heq] | exact (IH vs Hva Hpl)].
Qed.

(* the apart half of rbf_args_place, by itself *)
Fixpoint rbf_args_apart (rs : list (Z * Z)) (vs : list word) (xs : list SegModel.arg) {struct xs} : Prop :=
match xs, vs with
| [], _ => True
| SegModel.AS s :: xs', v :: vs' =>
    Forall (zdisjoint (bv_unsigned v, seg_spec.cstr_span (bv_unsigned v) s)) rs /\ rbf_args_apart rs vs' xs'
| SegModel.AI _ :: xs', _ :: vs' => rbf_args_apart rs vs' xs'
| _ :: _, [] => False
end.

(* from the contract's sa_va_args: each region of rs (start, length) lies inside one forbidden range (lo, hi) of
   Wl *)
Lemma rbf_args_apart_of_va : forall (rd : reader) Wl rs (vs : list word) (xs : list SegModel.arg),
  sa_va_args rd Wl vs xs ->
  Forall (fun r => exists iv, In iv Wl /\ fst iv <= fst r /\ fst r + snd r <= snd iv) rs ->
  rbf_args_apart rs vs xs.
Proof.
intros rd Wl rs vs xs. revert vs.
induction xs as [|x xs IH]; intros vs Hva Hin.
- destruct vs; exact I.
- destruct vs as [|v vs]; [exact (False_ind _ Hva)|].
  cbn [sa_va_args] in Hva. destruct Hva as [Hx Hva].
  destruct x as [s|z]; cbn [rbf_args_apart]; cbn [sa_va_arg] in Hx.
  + split; [|exact (IH vs Hva Hin)].
    destruct Hx as (_ & _ & _ & _ & Hap). unfold sa_apart_all in Hap.
    apply Forall_forall. intros r Hr.
    pose proof (proj1 (Forall_forall _ _) Hin r Hr) as Hr'. cbv beta in Hr'.
    destruct Hr' as (iv & Hiv & H1 & H2).
    pose proof (proj1 (Forall_forall _ _) Hap iv Hiv) as H. cbv beta in H.
    unfold zdisjoint. cbn [fst snd]. lia.
  + exact (IH vs Hva Hin).
Qed.

(* the place facts from refuse_va_locs at an AR state: a string and its NUL in a live heap block
   (PaLibH.amem8_of_blockA) or a live side-stack frame (YCbq.frames_bounds, SegABase.a3_amem_slack) *)
Lemma rbf_args_place_of_locs : forall ly S (W : world SEGS) mem md rs (vs : list word) (xs : list SegModel.arg),
  AR SEGS B ly S W mem md ->
  refuse_va_locs (fun q n => sa_heap B ly S q n \/ sa_fframe ly S q n) vs xs ->
  rbf_args_apart rs vs xs ->
  rbf_args_place (rdW W mem) rs vs xs.
Proof.
intros ly S W mem md rs vs xs HAR. revert vs.
induction xs as [|x xs IH]; intros vs Hloc Hap.
- destruct vs; exact I.
- destruct vs as [|v vs]; [destruct x; exact (False_ind _ Hloc)|].
  destruct x as [s|z]; cbn [refuse_va_locs rbf_args_apart rbf_args_place] in Hloc, Hap |- *.
  + destruct Hloc as [Hq Hloc]. destruct Hap as [Hd Hap].
    split; [|split; [exact Hd | exact (IH vs Hloc Hap)]].
    destruct Hq as [Hh | (cid & pos & Hin & Hcid & H1 & H2)].
    * apply (amem8_of_blockA SEGS B LAWS ly S W mem md _ _ HAR); [|lia].
      destruct Hh as (b & m & Hin & H1 & H2). exists b, m. split; [exact Hin|]. split; lia.
    * destruct (frames_bounds SEGS B LAWS ly S W mem md cid pos HAR Hin) as (Hf0 & Hfc & Happ).
      apply (a3_amem_slack _ _ _ _ Happ); lia.
  + exact (IH vs Hloc Hap).
Qed.
End e.
End f.

(* ============================== D. the format and kinds of the address prefix ============================== *)
Lemma rbf_addr_fmt_in : forall ln, In (SegModel.r_addr_fmt ln) refuse_pft.REFUSE_ALL_FMTS.
Proof.
intros ln. unfold SegModel.r_addr_fmt, refuse_pft.REFUSE_ALL_FMTS.
destruct (0 <? ln); [exact (or_introl eq_refl) | exact (or_intror (or_introl eq_refl))].
Qed.

Lemma rbf_addr_conv : forall rcs ln, seg_spec.conv_kinds (SegModel.r_addr_fmt ln) =
  map seg_spec.arg_is_s (SegModel.r_addr_args rcs ln).
Proof.
intros rcs ln. unfold SegModel.r_addr_fmt, SegModel.r_addr_args.
destruct (0 <? ln); cbn [map seg_spec.arg_is_s]; vm_compute; reflexivity.
Qed.

(* a refusal format is among the formats FFR covers *)
Lemma rbf_fmt_in : forall f, In f seg_spec.REFUSE_FORMATS -> In f refuse_pft.REFUSE_ALL_FMTS.
Proof. intros f H. exact (or_intror (or_intror H)). Qed.

(* ===================================== E. the record after the two calls ===================================== *)
Lemma rbf_slot_text : forall rcs ln f args, 0 <= ln < 2 ^ 31 -> (length (rc_refusal rcs) < 8)%nat ->
  forall bs, seg_spec.rconf_enc rcs bs ->
  nth (length (rc_refusal rcs)) (rc_refusal (SegModel.refuse rcs ln f args)) [] =
  SegModel.fmt (SegModel.r_addr_fmt ln) (SegModel.r_addr_args rcs ln) ++
  firstn (Z.to_nat (199 - Z.of_nat (length (SegModel.fmt (SegModel.r_addr_fmt ln) (SegModel.r_addr_args rcs ln)))))
         (SegModel.fmt f args).
Proof.
intros rcs ln f args Hln Hn8 bs HE.
rewrite (refuse_f.rf_refuse_lt8 rcs bs ln f args HE Hln Hn8). cbn [rc_refusal].
rewrite app_nth2 by lia. rewrite Nat.sub_diag. reflexivity.
Qed.

(* the one the walk calls at the end: the block after refused++, the slot's text and its NUL, n_refusals++ *)
Lemma rbf_rconf_refuse : forall (rd rd' : reader) c rcs ln f args,
  sa_rconf rd c rcs ->
  rc_refused rcs + 1 < 2 ^ 32 -> (length (rc_refusal rcs) < 8)%nat -> 0 <= ln < 2 ^ 31 ->
  In f seg_spec.REFUSE_FORMATS -> seg_spec.conv_kinds f = map seg_spec.arg_is_s args ->
  Forall refuse_f.rf_argok args ->
  (forall i, 0 <= i < seg_spec.SEG_C_SIZE ->
     ~ (seg_spec.RC_REFUSED <= i < seg_spec.RC_REFUSED + 4) ->
     ~ (seg_spec.RC_NREF <= i < seg_spec.RC_NREF + 4) ->
     ~ (seg_spec.RC_REFUSAL + 200 * Z.of_nat (length (rc_refusal rcs)) <= i <
        seg_spec.RC_REFUSAL + 200 * Z.of_nat (length (rc_refusal rcs)) + 200) ->
     rd' (c + i) = rd (c + i)) ->
  (forall i, seg_spec.RC_REFUSAL + 200 * Z.of_nat (length (rc_refusal rcs)) +
       Z.of_nat (length (nth (length (rc_refusal rcs)) (rc_refusal (SegModel.refuse rcs ln f args)) [])) + 1 <= i <
       seg_spec.RC_REFUSAL + 200 * Z.of_nat (length (rc_refusal rcs)) + 200 ->
     rd' (c + i) = rd (c + i)) ->
  rd32 rd' (c + seg_spec.RC_REFUSED) (rc_refused rcs + 1) ->
  rd32 rd' (c + seg_spec.RC_NREF) (Z.of_nat (length (rc_refusal rcs)) + 1) ->
  sa_zs rd' (seg_spec.refusal_addr c (length (rc_refusal rcs)))
    (nth (length (rc_refusal rcs)) (rc_refusal (SegModel.refuse rcs ln f args)) [] ++ [0]) ->
  sa_rconf rd' c (SegModel.refuse rcs ln f args).
Proof.
intros rd rd' c rcs ln f args Hrc Hr Hn8 Hln Hf Hck Hok Hk Htail H32 H32n Hzs.
pose proof Hrc as (bs & _ & HE).
destruct (refuse_f.rf_T1 rcs bs ln HE Hln) as (HTl & HTn & HTb).
destruct (refuse_f.rf_txt f args (or_intror (or_intror Hf)) Hck Hok) as (HFn & HFb & _).
rewrite (rbf_slot_text rcs ln f args Hln Hn8 bs HE) in Htail, Hzs.
rewrite (refuse_f.rf_refuse_lt8 rcs bs ln f args HE Hln Hn8).
set (T := SegModel.fmt (SegModel.r_addr_fmt ln) (SegModel.r_addr_args rcs ln)) in *.
set (FT := SegModel.fmt f args) in *.
set (txt := T ++ firstn (Z.to_nat (199 - Z.of_nat (length T))) FT) in *.
assert (Htn : ~ In 0 txt).
{ intros H. apply in_app_or in H. destruct H as [H|H]; [exact (HTn H) | exact (HFn (rbf_in_firstn _ _ _ H))]. }
assert (Htb : Forall (fun x => 0 <= x < 256) txt).
{ apply Forall_forall. intros x Hx. apply in_app_or in Hx. destruct Hx as [Hx|Hx].
  - pose proof (proj1 (Forall_forall _ _) HTb x Hx) as H. cbv beta in H. lia.
  - pose proof (proj1 (Forall_forall _ _) HFb x (rbf_in_firstn _ _ _ Hx)) as H. cbv beta in H. lia. }
assert (Htl : (length txt < 200)%nat).
{ unfold txt. rewrite length_app, length_firstn. lia. }
apply (refuse_f.rf_upd_slot rd rd' c rcs txt Hrc Hr Hn8 Htn Htb Htl); [|exact H32 | exact H32n | exact Hzs].
intros i Hi Ha Hb Hc.
destruct (Z_lt_le_dec i (seg_spec.RC_REFUSAL + 200 * Z.of_nat (length (rc_refusal rcs)) + 200)) as [Hlt|Hge].
- destruct (Z_lt_le_dec i (seg_spec.RC_REFUSAL + 200 * Z.of_nat (length (rc_refusal rcs)))) as [Hlt2|Hge2].
  + apply Hk; [exact Hi | exact Ha | exact Hb | lia].
  + apply Htail. lia.
- apply Hk; [exact Hi | exact Ha | exact Hb | lia].
Qed.
End d.

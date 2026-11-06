(* GXA's model of musl's printf (lib/CJ/RL/GX/Printf_model.v printf_model, the statement musl vfprintf's released
   walk takes, lib/CJ/RL/GXA/G_vfprintf_snf.v) renders a segconf format (lib/A/Rt/RtPFSeg.v seg_parse / seg_text) as
   seg_text does: seg_printf_text_ok is Printf_text.v:869 printf_text_ok over seg_piece, with the model's argument
   list seg_pargs.
   The released agreement (Printf_text.v pt_pieces, :714-801) is proved over GXA's own copy of the released pieces and
   cannot see %u, %zu or %.24s, whose bytes its parser refuses. This file repeats its induction over the format bytes
   on seg_parse, with three more directive arms, and reuses every per-conversion lemma of Printf_text.v:
   - %u   : parse_dir "u"   = T_UINT   (pt_pd_u),  conv at PA_u (v mod 2^32) (pt_conv_u);
   - %zu  : parse_dir "zu"  = T_SIZET  (pt_pd_zu), conv at PA_ull u (pt_conv_ull);
   - %.24s: parse_dir ".24s" = precision 24 on T_PTR (seg_pd_24s), conv at PA_s s writes firstn 24 s (seg_conv_24s:
            musl's strnlen (s, 24) bytes).
   Pure: no machine state, no image value. *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Lib Require Import ITree.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Spec Require Import Prelim Monad FmtFp.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.GX Require Import Printf_model.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.GX Require G_printf_core_common.
Import OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.GX.G_printf_core_common.G_printf_iface.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.GX Require Printf_text.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtPFPf RtPFSeg.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require Import SegPfStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require FMpfStep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Module PT := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.GX.Printf_text.
Module PFS := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.FMpfStep.

Local Ltac szl := unfold zlength in *; cbn [length] in *; lia.

(* ---- GXA's copy of the renderers is ours ---- *)
Lemma seg_pt_digits : forall fuel x acc, PT.pf_digits fuel x acc = pf_digits fuel x acc.
Proof.
induction fuel as [|f IH]; intros x acc; [reflexivity|].
cbn [PT.pf_digits pf_digits]. destruct (x <? 10); [reflexivity | apply IH].
Qed.
Lemma seg_pt_dec : forall v, PT.pf_dec v = pf_dec v.
Proof. intros v. unfold PT.pf_dec, pf_dec. rewrite !seg_pt_digits. reflexivity. Qed.
Lemma seg_pt_udec : forall u, PT.pf_udec u = pf_udec u.
Proof. intros u. unfold PT.pf_udec, pf_udec. apply seg_pt_digits. Qed.
Lemma seg_pt_hexs : forall fuel x acc, PT.pf_hexs fuel x acc = pf_hexs fuel x acc.
Proof.
induction fuel as [|f IH]; intros x acc; [reflexivity|].
cbn [PT.pf_hexs pf_hexs]. unfold PT.pf_hexd, pf_hexd. destruct (x <? 16); [reflexivity | apply IH].
Qed.
Lemma seg_pt_hexw4 : forall v, PT.pt_hexw 4 v = pf_hex4 v.
Proof. intros v. unfold PT.pt_hexw, pf_hex4. cbv zeta. rewrite seg_pt_hexs. reflexivity. Qed.
Lemma seg_pt_hexw2 : forall v, PT.pt_hexw 2 v = pf_hex2 v.
Proof. intros v. unfold PT.pt_hexw, pf_hex2. cbv zeta. rewrite seg_pt_hexs. reflexivity. Qed.

(* ---- the model's argument list: one parg per argument a piece consumes (Printf_text.v pf_pargs, and PA_u
   (v mod 2^32) at %u, PA_ull u at %zu, PA_s s at %.24s) ---- *)
Fixpoint seg_pargs (qs : list seg_piece) (args : list pf_arg) : list parg :=
  match qs with
  | [] => []
  | PRel (PLit _) :: qs' => seg_pargs qs' args
  | PRel Pd :: qs' => match args with AInt v :: a' => PA_i v :: seg_pargs qs' a' | _ => [] end
  | PRel Pc :: qs' => match args with AInt v :: a' => PA_i v :: seg_pargs qs' a' | _ => [] end
  | PRel Px04 :: qs' => match args with AInt v :: a' => PA_u (v mod 2^32) :: seg_pargs qs' a' | _ => [] end
  | PRel Px02 :: qs' => match args with AInt v :: a' => PA_u (v mod 2^32) :: seg_pargs qs' a' | _ => [] end
  | PRel Pllu :: qs' => match args with AU64 u :: a' => PA_ull u :: seg_pargs qs' a' | _ => [] end
  | PRel Ps :: qs' => match args with APtr s :: a' => PA_s s :: seg_pargs qs' a' | _ => [] end
  | PRel Pps :: qs' =>
      match args with AInt k :: APtr s :: a' => PA_i k :: PA_s s :: seg_pargs qs' a' | _ => [] end
  | Pu :: qs' => match args with AInt v :: a' => PA_u (v mod 2^32) :: seg_pargs qs' a' | _ => [] end
  | Pzu :: qs' => match args with AU64 u :: a' => PA_ull u :: seg_pargs qs' a' | _ => [] end
  | P24s :: qs' => match args with APtr s :: a' => PA_s s :: seg_pargs qs' a' | _ => [] end
  end.

(* the ranges the model needs of the arguments (Printf_text.v pt_fit) *)
Definition seg_fit (a : pf_arg) : Prop := match a with AInt v => -2^31 <= v < 2^31 | AU64 u => 0 <= u | _ => True end.

(* the model's argument for an argument (FMgxaSeamPf.v pt_parg) and the shape the seam reads (pt_parg_ok) *)
Definition seg_parg (a : pf_arg) : parg := match a with AInt v => PA_i v | AU64 u => PA_ull u | APtr s => PA_s s end.
Definition seg_parg_ok (a : pf_arg) (pa : parg) : Prop :=
  pa = seg_parg a \/ exists v, a = AInt v /\ pa = PA_u (v mod 2^32).

(* ---- the parser, at a directive and at a literal ---- *)
Lemma seg_parse_pct : forall r qs, seg_parse (37 :: r) = Some qs ->
  exists q qs' r1, qs = q :: qs' /\ seg_parse r1 = Some qs' /\ 37 :: r = seg_code q ++ r1 /\
    (forall b, q <> PRel (PLit b)).
Proof.
intros r qs H. destruct qs as [|q qs']; [apply seg_parse_nil in H; discriminate H|].
destruct (seg_parse_split _ q qs' H) as (r1 & E & Hr1 & Hok).
exists q, qs', r1. split; [reflexivity|]. split; [exact Hr1|]. split; [exact E|].
intros b ->. cbn [seg_code PFS.pf_code app] in E. injection E as E1 _.
cbn [seg_code_ok PFS.pf_code_ok] in Hok. lia.
Qed.

(* the byte after a directive's '%' is not '%' *)
Lemma seg_pct_next : forall r qs, seg_parse (37 :: r) = Some qs -> exists c2 s3, r = c2 :: s3 /\ c2 <> 37.
Proof.
intros r qs H. destruct (seg_parse_pct r qs H) as (q & qs' & r1 & _ & _ & E & Hnl).
destruct q as [[b| | | | | | |]| | |]; [exfalso; exact (Hnl b eq_refl) | ..];
  cbn [seg_code PFS.pf_code app] in E; injection E as E; subst r; eexists; eexists; (split; [reflexivity | lia]).
Qed.

Lemma seg_parse_lit : forall b r qs, b <> 37 -> seg_parse (b :: r) = Some qs ->
  0 < b < 256 /\ exists qs', seg_parse r = Some qs' /\ qs = PRel (PLit b) :: qs'.
Proof.
intros b r qs Hb H. cbn [seg_parse] in H.
replace (b =? 37) with false in H by (symmetry; apply Z.eqb_neq; exact Hb).
destruct (0 <? b) eqn:E1; cbn [andb] in H; [|discriminate H].
destruct (b <? 256) eqn:E2; cbn [andb] in H; [|discriminate H].
apply Z.ltb_lt in E1. apply Z.ltb_lt in E2.
apply PT.pt_omap_some in H as (qs' & H & ->). split; [lia|]. exists qs'. split; [exact H | reflexivity].
Qed.

Lemma seg_lit_split : forall fmt qs, seg_parse fmt = Some qs ->
  exists L R qsR, fmt = L ++ R /\ lit_run (fmt ++ [0]) = L /\ seg_parse R = Some qsR /\
    qs = map (fun b => PRel (PLit b)) L ++ qsR /\ (R = [] \/ exists R', R = 37 :: R').
Proof.
induction fmt as [|b r IH]; intros qs H.
- exists [], [], []. cbn [seg_parse] in H. injection H as <-.
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. left. reflexivity.
- destruct (Z.eqb_spec b 37) as [->|Hb].
  + exists [], (37 :: r), qs. split; [reflexivity|]. split; [reflexivity|]. split; [exact H|]. split; [reflexivity|].
    right. exists r. reflexivity.
  + destruct (seg_parse_lit b r qs Hb H) as [Hb2 (qs' & H' & ->)].
    destruct (IH qs' H') as (L & R & qsR & E1 & E2 & E3 & E4 & E5).
    exists (b :: L), R, qsR. split; [rewrite E1; reflexivity|]. split.
    { cbn [app lit_run]. replace (b =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      replace (b =? 37) with false by (symmetry; apply Z.eqb_neq; exact Hb). cbn [orb]. rewrite E2. reflexivity. }
    split; [exact E3|]. split; [rewrite E4; reflexivity|]. exact E5.
Qed.

Lemma seg_text_lits : forall L qs args,
  seg_text (map (fun b => PRel (PLit b)) L ++ qs) args = option_map (app L) (seg_text qs args).
Proof.
induction L as [|x L IH]; intros qs args; cbn [map app seg_text seg_step]; [|rewrite IH];
  destruct (seg_text qs args); reflexivity.
Qed.

Lemma seg_pargs_lits : forall L qs args, seg_pargs (map (fun b => PRel (PLit b)) L ++ qs) args = seg_pargs qs args.
Proof. induction L as [|x L IH]; intros qs args; cbn [map app seg_pargs]; auto. Qed.

Lemma seg_pargs_nog : forall qs args, Forall PT.pt_nog (seg_pargs qs args).
Proof.
induction qs as [|q qs IH]; intros args; [constructor|].
destruct q as [[b| | | | | | |]| | |]; cbn [seg_pargs]; try apply IH;
  destruct args as [|[v|u|s] [|[v2|u2|s2] a']]; repeat constructor; apply IH.
Qed.

(* ---- %.24s: musl's strnlen (s, 24) bytes of s ---- *)
Lemma seg_pd_24s : forall t, parse_dir (46 :: 50 :: 52 :: 115 :: t) = Some (mkDir 0 0 24 true 115 T_PTR, t).
Proof. intros t; reflexivity. Qed.

Lemma seg_conv_24s : forall cnt s, 0 <= cnt -> cnt + zlength (firstn 24 s) <= INT_MAX ->
  exists ps, conv_pieces cnt (mkDir 0 0 24 true 115 T_PTR) (PA_s s) = Some (ps, cnt + zlength (firstn 24 s))
    /\ concat ps = firstn 24 s.
Proof.
intros cnt s Hc Hm.
assert (HF : zlength (firstn 24 s) = Z.min (zlength s) 24) by (unfold zlength; rewrite length_firstn; lia).
assert (C : conv_pieces cnt (mkDir 0 0 24 true 115 T_PTR) (PA_s s)
            = tail_pieces cnt 0 0 (Z.min (zlength s) 24) [] (firstn (Z.to_nat (Z.min (zlength s) 24)) s))
  by reflexivity.
assert (E : firstn (Z.to_nat (Z.min (zlength s) 24)) s = firstn 24 s).
{ unfold zlength. destruct (Nat.le_gt_cases (length s) 24) as [L|L].
  - rewrite !firstn_all2 by lia. reflexivity.
  - replace (Z.to_nat (Z.min (Z.of_nat (length s)) 24)) with 24%nat by lia. reflexivity. }
rewrite C, E, <- HF. pose proof (PT.pt_zlength_nonneg (firstn 24 s)).
apply PT.pt_tail_exact; [szl|szl|szl|szl|reflexivity|reflexivity].
Qed.

Local Ltac seg_hs HS := destruct HS as [HS|HS];
  [left; rewrite ?PT.pt_zlength_app in HS; lia | right; intros ? Hin; apply HS; cbn [In]; tauto].

(* ---- Printf_text.v pt_pieces over segconf's grammar ---- *)
Lemma seg_pieces : forall fuel fmt qs args T cnt,
  (length fmt < fuel)%nat -> seg_parse fmt = Some qs -> seg_text qs args = Some T -> Forall seg_fit args ->
  0 <= cnt -> cnt + zlength T <= INT_MAX ->
  (cnt + zlength T < INT_MAX \/ (forall s, In (APtr s) args -> zlength s < INT_MAX)) ->
  exists pcs, printf_pieces_loop fuel (fmt ++ [0]) (seg_pargs qs args) cnt = Some (pcs, cnt + zlength T)
    /\ concat pcs = T.
Proof.
induction fuel as [|fuel IH]; intros fmt qs args T cnt Hlen Hp Ht Ha Hc HT HS; [lia|].
destruct fmt as [|b r].
{ cbn [seg_parse] in Hp. injection Hp as <-. destruct args as [|a args]; cbn [seg_text] in Ht; [|discriminate Ht].
  injection Ht as <-. exists []. split; [|reflexivity]. change (zlength (@nil Z)) with 0. rewrite Z.add_0_r.
  reflexivity. }
destruct (Z.eqb_spec b 37) as [->|Hb].
- destruct (seg_parse_pct r qs Hp) as (q & qs' & r1 & -> & Hp' & E & Hnl).
  destruct q as [[b| | | | | | |]| | |]; [exfalso; exact (Hnl b eq_refl) | ..];
    cbn [seg_code PFS.pf_code app] in E; injection E as E; subst r; cbn [length] in Hlen.
  + (* %d *)
    destruct args as [|[v|u|s] a']; cbn [seg_text seg_step] in Ht; try discriminate Ht.
    apply PT.pt_omap_some in Ht as (T' & Ht' & ->). inversion_clear Ha as [|? ? Hv Ha']. cbn [seg_fit] in Hv.
    rewrite PT.pt_zlength_app in HT. pose proof (PT.pt_zlength_nonneg (pf_dec v)).
    pose proof (PT.pt_zlength_nonneg T').
    destruct (PT.pt_conv_d cnt v Hv Hc ltac:(rewrite seg_pt_dec; lia)) as (ps1 & C & E1).
    rewrite seg_pt_dec in C, E1.
    destruct (IH r1 qs' a' T' (cnt + zlength (pf_dec v)) ltac:(lia) Hp' Ht' Ha' ltac:(lia) ltac:(lia)
                ltac:(seg_hs HS)) as (pcs & P & E2).
    cbn [app seg_pargs].
    exact (PT.pt_dir_glue fuel 100 _ _ _ _ _ cnt ps1 (pf_dec v) pcs T' ltac:(lia) (PT.pt_pd_d _) C E1 P E2).
  + (* %c *)
    destruct args as [|[v|u|s] a']; cbn [seg_text seg_step] in Ht; try discriminate Ht.
    apply PT.pt_omap_some in Ht as (T' & Ht' & ->). inversion_clear Ha as [|? ? Hv Ha'].
    rewrite PT.pt_zlength_app in HT. pose proof (PT.pt_zlength_nonneg [v mod 256]).
    pose proof (PT.pt_zlength_nonneg T').
    destruct (PT.pt_conv_c cnt v Hc ltac:(lia)) as (ps1 & C & E1).
    destruct (IH r1 qs' a' T' (cnt + zlength [v mod 256]) ltac:(lia) Hp' Ht' Ha' ltac:(lia) ltac:(lia)
                ltac:(seg_hs HS)) as (pcs & P & E2).
    cbn [app seg_pargs].
    exact (PT.pt_dir_glue fuel 99 _ _ _ _ _ cnt ps1 [v mod 256] pcs T' ltac:(lia) (PT.pt_pd_c _) C E1 P E2).
  + (* %04x *)
    destruct args as [|[v|u|s] a']; cbn [seg_text seg_step] in Ht; try discriminate Ht.
    apply PT.pt_omap_some in Ht as (T' & Ht' & ->). inversion_clear Ha as [|? ? Hv Ha'].
    rewrite PT.pt_zlength_app in HT. pose proof (PT.pt_zlength_nonneg (pf_hex4 v)).
    pose proof (PT.pt_zlength_nonneg T').
    destruct (PT.pt_conv_x 4 cnt v (or_intror eq_refl) Hc ltac:(rewrite seg_pt_hexw4; lia)) as (ps1 & C & E1).
    rewrite seg_pt_hexw4 in C, E1.
    destruct (IH r1 qs' a' T' (cnt + zlength (pf_hex4 v)) ltac:(lia) Hp' Ht' Ha' ltac:(lia) ltac:(lia)
                ltac:(seg_hs HS)) as (pcs & P & E2).
    cbn [app seg_pargs].
    exact (PT.pt_dir_glue fuel 48 _ _ _ _ _ cnt ps1 (pf_hex4 v) pcs T' ltac:(lia) (PT.pt_pd_x4 _) C E1 P E2).
  + (* %02x *)
    destruct args as [|[v|u|s] a']; cbn [seg_text seg_step] in Ht; try discriminate Ht.
    apply PT.pt_omap_some in Ht as (T' & Ht' & ->). inversion_clear Ha as [|? ? Hv Ha'].
    rewrite PT.pt_zlength_app in HT. pose proof (PT.pt_zlength_nonneg (pf_hex2 v)).
    pose proof (PT.pt_zlength_nonneg T').
    destruct (PT.pt_conv_x 2 cnt v (or_introl eq_refl) Hc ltac:(rewrite seg_pt_hexw2; lia)) as (ps1 & C & E1).
    rewrite seg_pt_hexw2 in C, E1.
    destruct (IH r1 qs' a' T' (cnt + zlength (pf_hex2 v)) ltac:(lia) Hp' Ht' Ha' ltac:(lia) ltac:(lia)
                ltac:(seg_hs HS)) as (pcs & P & E2).
    cbn [app seg_pargs].
    exact (PT.pt_dir_glue fuel 48 _ _ _ _ _ cnt ps1 (pf_hex2 v) pcs T' ltac:(lia) (PT.pt_pd_x2 _) C E1 P E2).
  + (* %llu *)
    destruct args as [|[v|u|s] a']; cbn [seg_text seg_step] in Ht; try discriminate Ht.
    apply PT.pt_omap_some in Ht as (T' & Ht' & ->). inversion_clear Ha as [|? ? Hu Ha']. cbn [seg_fit] in Hu.
    rewrite PT.pt_zlength_app in HT. pose proof (PT.pt_zlength_nonneg (pf_udec u)).
    pose proof (PT.pt_zlength_nonneg T').
    destruct (PT.pt_conv_ull cnt T_ULLONG u (or_introl eq_refl) Hu Hc ltac:(rewrite seg_pt_udec; lia))
      as (ps1 & C & E1).
    rewrite seg_pt_udec in C, E1.
    destruct (IH r1 qs' a' T' (cnt + zlength (pf_udec u)) ltac:(lia) Hp' Ht' Ha' ltac:(lia) ltac:(lia)
                ltac:(seg_hs HS)) as (pcs & P & E2).
    cbn [app seg_pargs].
    exact (PT.pt_dir_glue fuel 108 _ _ _ _ _ cnt ps1 (pf_udec u) pcs T' ltac:(lia) (PT.pt_pd_llu _) C E1 P E2).
  + (* %s *)
    destruct args as [|[v|u|s] a']; cbn [seg_text seg_step] in Ht; try discriminate Ht.
    apply PT.pt_omap_some in Ht as (T' & Ht' & ->). inversion_clear Ha as [|? ? Hv Ha'].
    rewrite PT.pt_zlength_app in HT. pose proof (PT.pt_zlength_nonneg s). pose proof (PT.pt_zlength_nonneg T').
    assert (Hs : zlength s < INT_MAX)
      by (destruct HS as [HS|HS]; [rewrite PT.pt_zlength_app in HS; lia | apply HS; left; reflexivity]).
    destruct (PT.pt_conv_s cnt s Hs Hc ltac:(lia)) as (ps1 & C & E1).
    destruct (IH r1 qs' a' T' (cnt + zlength s) ltac:(lia) Hp' Ht' Ha' ltac:(lia) ltac:(lia) ltac:(seg_hs HS))
      as (pcs & P & E2).
    cbn [app seg_pargs].
    exact (PT.pt_dir_glue fuel 115 _ _ _ _ _ cnt ps1 s pcs T' ltac:(lia) (PT.pt_pd_s _) C E1 P E2).
  + (* %.*s *)
    destruct args as [|[k|u|s] [|[v|u2|s2] a']]; cbn [seg_text seg_step] in Ht; try discriminate Ht.
    revert Ht. destruct ((0 <=? k) && (k <=? Z.of_nat (length s2))) eqn:Ek; intros Ht; cbv beta iota in Ht;
      [|discriminate Ht].
    apply andb_prop in Ek as [Ek1 Ek2]. apply Z.leb_le in Ek1. apply Z.leb_le in Ek2.
    apply PT.pt_omap_some in Ht as (T' & Ht' & ->). inversion_clear Ha as [|? ? Hv Ha0].
    inversion_clear Ha0 as [|? ? _ Ha'].
    rewrite PT.pt_zlength_app in HT. pose proof (PT.pt_zlength_nonneg (firstn (Z.to_nat k) s2)).
    pose proof (PT.pt_zlength_nonneg T').
    destruct (PT.pt_conv_ps cnt k s2 ltac:(unfold zlength; lia) Hc ltac:(lia)) as (ps1 & C & E1).
    destruct (IH r1 qs' a' T' (cnt + zlength (firstn (Z.to_nat k) s2)) ltac:(lia) Hp' Ht' Ha' ltac:(lia) ltac:(lia)
                ltac:(seg_hs HS)) as (pcs & P & E2).
    cbn [app seg_pargs].
    exact (PT.pt_star_glue fuel 46 _ _ _ k _ _ cnt ps1 (firstn (Z.to_nat k) s2) pcs T' ltac:(lia)
             (PT.pt_pd_ps _) (PT.pt_ps_ps _) C E1 P E2).
  + (* %u *)
    destruct args as [|[v|u|s] a']; cbn [seg_text seg_step] in Ht; try discriminate Ht.
    apply PT.pt_omap_some in Ht as (T' & Ht' & ->). inversion_clear Ha as [|? ? Hv Ha'].
    pose proof (Z.mod_pos_bound v (2^32) ltac:(lia)) as Hu.
    rewrite PT.pt_zlength_app in HT. pose proof (PT.pt_zlength_nonneg (pf_udec (v mod 2^32))).
    pose proof (PT.pt_zlength_nonneg T').
    destruct (PT.pt_conv_u cnt (v mod 2^32) ltac:(lia) Hc ltac:(rewrite seg_pt_udec; lia)) as (ps1 & C & E1).
    rewrite seg_pt_udec in C, E1.
    destruct (IH r1 qs' a' T' (cnt + zlength (pf_udec (v mod 2^32))) ltac:(lia) Hp' Ht' Ha' ltac:(lia) ltac:(lia)
                ltac:(seg_hs HS)) as (pcs & P & E2).
    cbn [app seg_pargs].
    exact (PT.pt_dir_glue fuel 117 _ _ _ _ _ cnt ps1 (pf_udec (v mod 2^32)) pcs T' ltac:(lia) (PT.pt_pd_u _) C E1 P
             E2).
  + (* %zu *)
    destruct args as [|[v|u|s] a']; cbn [seg_text seg_step] in Ht; try discriminate Ht.
    apply PT.pt_omap_some in Ht as (T' & Ht' & ->). inversion_clear Ha as [|? ? Hu Ha']. cbn [seg_fit] in Hu.
    rewrite PT.pt_zlength_app in HT. pose proof (PT.pt_zlength_nonneg (pf_udec u)).
    pose proof (PT.pt_zlength_nonneg T').
    destruct (PT.pt_conv_ull cnt T_SIZET u (or_intror eq_refl) Hu Hc ltac:(rewrite seg_pt_udec; lia))
      as (ps1 & C & E1).
    rewrite seg_pt_udec in C, E1.
    destruct (IH r1 qs' a' T' (cnt + zlength (pf_udec u)) ltac:(lia) Hp' Ht' Ha' ltac:(lia) ltac:(lia)
                ltac:(seg_hs HS)) as (pcs & P & E2).
    cbn [app seg_pargs].
    exact (PT.pt_dir_glue fuel 122 _ _ _ _ _ cnt ps1 (pf_udec u) pcs T' ltac:(lia) (PT.pt_pd_zu _) C E1 P E2).
  + (* %.24s *)
    destruct args as [|[v|u|s] a']; cbn [seg_text seg_step] in Ht; try discriminate Ht.
    apply PT.pt_omap_some in Ht as (T' & Ht' & ->). inversion_clear Ha as [|? ? Hv Ha'].
    rewrite PT.pt_zlength_app in HT. pose proof (PT.pt_zlength_nonneg (firstn 24 s)).
    pose proof (PT.pt_zlength_nonneg T').
    destruct (seg_conv_24s cnt s Hc ltac:(lia)) as (ps1 & C & E1).
    destruct (IH r1 qs' a' T' (cnt + zlength (firstn 24 s)) ltac:(lia) Hp' Ht' Ha' ltac:(lia) ltac:(lia)
                ltac:(seg_hs HS)) as (pcs & P & E2).
    cbn [app seg_pargs].
    exact (PT.pt_dir_glue fuel 46 _ _ _ _ _ cnt ps1 (firstn 24 s) pcs T' ltac:(lia) (seg_pd_24s _) C E1 P E2).
- destruct (seg_parse_lit b r qs Hb Hp) as [Hb2 _].
  destruct (seg_lit_split (b :: r) qs Hp) as (L & R & qsR & E1 & E2 & E3 & -> & E5).
  rewrite seg_text_lits in Ht. apply PT.pt_omap_some in Ht as (TR & Ht' & ->).
  assert (HL : 0 < zlength L).
  { destruct L as [|x L]; [|unfold zlength; cbn [length]; lia].
    cbn [app] in E1. destruct E5 as [->|(R' & ->)]; [discriminate E1|]. injection E1 as E1 _. contradiction. }
  assert (Hlen' : (length R < fuel)%nat).
  { rewrite E1, length_app in Hlen. unfold zlength in HL. lia. }
  rewrite PT.pt_zlength_app in HT. pose proof (PT.pt_zlength_nonneg TR).
  destruct (IH R qsR args TR (cnt + zlength L) Hlen' E3 Ht' Ha ltac:(lia) ltac:(lia) ltac:(seg_hs HS))
    as (pcs & P & E).
  exists (L :: pcs). split.
  + rewrite seg_pargs_lits, PT.pt_zlength_app, Z.add_assoc. change ((b :: r) ++ [0]) with (b :: (r ++ [0])).
    eapply PT.pt_lit_step with (s1 := R ++ [0]); [lia | exact E2 | | exact HL | | lia | exact P].
    * change (b :: r ++ [0]) with ((b :: r) ++ [0]). rewrite E1, <- app_assoc. apply PT.pt_skipn_app.
    * destruct E5 as [->|(R' & ->)]; [cbn [app]; left; reflexivity|].
      destruct (seg_pct_next R' qsR E3) as (c2 & s3 & -> & Hc2).
      cbn [app]. right. split; [reflexivity|]. exists c2, (s3 ++ [0]). split; [reflexivity | exact Hc2].
  + cbn [concat]. rewrite E. reflexivity.
Qed.

Lemma seg_fit_of : forall args, (forall v, In (AInt v) args -> -2^31 <= v < 2^31) ->
  (forall u, In (AU64 u) args -> 0 <= u) -> Forall seg_fit args.
Proof. intros args HA HU. apply Forall_forall. intros [v|u|s] Hin; [exact (HA v Hin)|exact (HU u Hin)|exact I]. Qed.

Theorem seg_printf_text_model : forall fmt qs args T,
  seg_parse fmt = Some qs -> seg_text qs args = Some T ->
  (forall v, In (AInt v) args -> -2^31 <= v < 2^31) ->
  (forall u, In (AU64 u) args -> 0 <= u) ->
  zlength T <= 2147483647 ->
  (zlength T < 2147483647 \/ (forall s, In (APtr s) args -> zlength s < 2147483647)) ->
  printf_model (St:=list Z) (OUT_snf (zlength T)) OUTFP_snf (fmt ++ [0]) (seg_pargs qs args) []
    = ITree.Ret (Ok (zlength T, T)).
Proof.
intros fmt qs args T Hp Ht HA HU HT HS.
destruct (seg_pieces (length (fmt ++ [0])) fmt qs args T 0 ltac:(rewrite length_app; cbn [length]; lia) Hp Ht
            (seg_fit_of args HA HU) ltac:(lia) HT HS) as (pcs & P & E).
pose proof (PT.printf_model_snf_pieces (zlength T) _ _ pcs (zlength T) P ltac:(rewrite E; lia)) as M.
rewrite E in M. exact M.
Qed.

Theorem seg_printf_text_pass1 : forall fmt qs args T,
  seg_parse fmt = Some qs -> seg_text qs args = Some T -> zlength T <= 2147483647 ->
  pass1_ok (fmt ++ [0]) = true.
Proof.
intros fmt qs args T Hp Ht HT.
destruct (seg_lit_split fmt qs Hp) as (L & R & qsR & E1 & E2 & E3 & -> & E5).
rewrite seg_text_lits in Ht. apply PT.pt_omap_some in Ht as (TR & _ & ->).
rewrite PT.pt_zlength_app in HT. pose proof (PT.pt_zlength_nonneg TR).
unfold pass1_ok. cbv zeta. rewrite E2.
replace (zlength L <=? INT_MAX) with true by (symmetry; apply Z.leb_le; unfold INT_MAX; lia).
rewrite E1, <- app_assoc, PT.pt_skipn_app.
destruct E5 as [->|(R' & ->)]; [reflexivity|].
destruct (seg_parse_pct R' qsR E3) as (q & qs' & r1 & _ & _ & E & Hnl).
destruct q as [[b| | | | | | |]| | |]; [exfalso; exact (Hnl b eq_refl) | ..];
  cbn [seg_code PFS.pf_code app] in E; injection E as E; subst R'; cbn [app].
- rewrite PT.pt_pd_d. reflexivity.
- rewrite PT.pt_pd_c. reflexivity.
- rewrite PT.pt_pd_x4. reflexivity.
- rewrite PT.pt_pd_x2. reflexivity.
- rewrite PT.pt_pd_llu. reflexivity.
- rewrite PT.pt_pd_s. reflexivity.
- rewrite PT.pt_pd_ps, PT.pt_ps_ps. reflexivity.
- rewrite PT.pt_pd_u. reflexivity.
- rewrite PT.pt_pd_zu. reflexivity.
- rewrite seg_pd_24s. reflexivity.
Qed.

Theorem seg_printf_text_fp : forall fmt qs args,
  fp_calls (length (fmt ++ [0])) (fmt ++ [0]) (seg_pargs qs args) = [].
Proof. intros fmt qs args. apply PT.pt_fp_nog. apply seg_pargs_nog. Qed.

(* the agreement: GXA's model on a segconf format, with the model's own argument list *)
Theorem seg_printf_text_ok : forall fmt qs args T,
  seg_parse fmt = Some qs -> seg_text qs args = Some T ->
  (forall v, In (AInt v) args -> -2^31 <= v < 2^31) ->
  (forall u, In (AU64 u) args -> 0 <= u) ->
  zlength T <= 2147483647 ->
  (zlength T < 2147483647 \/ (forall s, In (APtr s) args -> zlength s < 2147483647)) ->
  printf_model (St:=list Z) (OUT_snf (zlength T)) OUTFP_snf (fmt ++ [0]) (seg_pargs qs args) []
    = ITree.Ret (Ok (zlength T, T))
  /\ pass1_ok (fmt ++ [0]) = true
  /\ fp_calls (length (fmt ++ [0])) (fmt ++ [0]) (seg_pargs qs args) = []
  /\ Forall (fun c => 0 <= c < 256) (fmt ++ [0]).
Proof.
intros fmt qs args T Hp Ht HA HU HT HS. split; [|split; [|split]].
- exact (seg_printf_text_model fmt qs args T Hp Ht HA HU HT HS).
- exact (seg_printf_text_pass1 fmt qs args T Hp Ht HT).
- apply seg_printf_text_fp.
- exact (seg_parse_bytes0 fmt qs Hp).
Qed.

(* the model's arguments have the shape the seam reads: one seg_parg_ok parg per argument *)
Lemma seg_pargs_shape : forall qs args T, seg_text qs args = Some T -> Forall2 seg_parg_ok args (seg_pargs qs args).
Proof.
induction qs as [|q qs IH]; intros args T HT.
- destruct args as [|a args]; cbn in HT |- *; [constructor | discriminate].
- destruct q as [[b| | | | | | |]| | |].
  + cbn [seg_text seg_step seg_pargs] in HT |- *. apply PT.pt_omap_some in HT as (T' & E & _).
    exact (IH args T' E).
  + destruct args as [|[v|u|s] a']; cbn [seg_text seg_step seg_pargs] in HT |- *; try discriminate HT.
    apply PT.pt_omap_some in HT as (T' & E & _). constructor; [left; reflexivity | exact (IH a' T' E)].
  + destruct args as [|[v|u|s] a']; cbn [seg_text seg_step seg_pargs] in HT |- *; try discriminate HT.
    apply PT.pt_omap_some in HT as (T' & E & _). constructor; [left; reflexivity | exact (IH a' T' E)].
  + destruct args as [|[v|u|s] a']; cbn [seg_text seg_step seg_pargs] in HT |- *; try discriminate HT.
    apply PT.pt_omap_some in HT as (T' & E & _).
    constructor; [right; exists v; split; reflexivity | exact (IH a' T' E)].
  + destruct args as [|[v|u|s] a']; cbn [seg_text seg_step seg_pargs] in HT |- *; try discriminate HT.
    apply PT.pt_omap_some in HT as (T' & E & _).
    constructor; [right; exists v; split; reflexivity | exact (IH a' T' E)].
  + destruct args as [|[v|u|s] a']; cbn [seg_text seg_step seg_pargs] in HT |- *; try discriminate HT.
    apply PT.pt_omap_some in HT as (T' & E & _). constructor; [left; reflexivity | exact (IH a' T' E)].
  + destruct args as [|[v|u|s] a']; cbn [seg_text seg_step seg_pargs] in HT |- *; try discriminate HT.
    apply PT.pt_omap_some in HT as (T' & E & _). constructor; [left; reflexivity | exact (IH a' T' E)].
  + destruct args as [|[k|u|s0] [|[v|u'|s] a']]; cbn [seg_text seg_step seg_pargs] in HT |- *; try discriminate HT.
    revert HT. destruct ((0 <=? k) && (k <=? Z.of_nat (length s))); intros HT; cbv beta iota in HT;
      [|discriminate HT].
    apply PT.pt_omap_some in HT as (T' & E & _).
    constructor; [left; reflexivity | constructor; [left; reflexivity | exact (IH a' T' E)]].
  + destruct args as [|[v|u|s] a']; cbn [seg_text seg_step seg_pargs] in HT |- *; try discriminate HT.
    apply PT.pt_omap_some in HT as (T' & E & _).
    constructor; [right; exists v; split; reflexivity | exact (IH a' T' E)].
  + destruct args as [|[v|u|s] a']; cbn [seg_text seg_step seg_pargs] in HT |- *; try discriminate HT.
    apply PT.pt_omap_some in HT as (T' & E & _). constructor; [left; reflexivity | exact (IH a' T' E)].
  + destruct args as [|[v|u|s] a']; cbn [seg_text seg_step seg_pargs] in HT |- *; try discriminate HT.
    apply PT.pt_omap_some in HT as (T' & E & _). constructor; [left; reflexivity | exact (IH a' T' E)].
Qed.

(* ---- controls: the three new conversions on GXA's model, by computation ---- *)
Example seg_model_u : printf_model (St:=list Z) (OUT_snf 10) OUTFP_snf [37; 117; 0] (seg_pargs [Pu] [AInt (-1)]) []
  = ITree.Ret (Ok (10, [52; 50; 57; 52; 57; 54; 55; 50; 57; 53])).
Proof. vm_compute. reflexivity. Qed.
Example seg_model_zu : printf_model (St:=list Z) (OUT_snf 2) OUTFP_snf [37; 122; 117; 0] (seg_pargs [Pzu] [AU64 46]) []
  = ITree.Ret (Ok (2, [52; 54])).
Proof. vm_compute. reflexivity. Qed.
Example seg_model_24s : printf_model (St:=list Z) (OUT_snf 24) OUTFP_snf [37; 46; 50; 52; 115; 0]
  (seg_pargs [P24s] [APtr (repeat 97 30)]) [] = ITree.Ret (Ok (24, repeat 97 24)).
Proof. vm_compute. reflexivity. Qed.

(* Step 2 of the evt -> SRr seam at musl vfprintf: MODEL AGREEMENT.

   The shared snprintf contract (FMsnprintfShared.v, RtPrintf.Param) states what a run prints with
   lib/A/FMsnprintfPf.v's parser and renderer (pf_parse / pf_text over pf_piece / pf_arg), copied
   from fuzz_disco lib/Rt/PfFacts.v.  GXA's musl vfprintf statement
   (lib/CJ/RL/GXA/G_vfprintf_snf.v:206) asks instead for
     printf_model (OUT_snf OM) OUTFP_snf fmt args [] = ITree.Ret (Ok (r, o)).

   The released GXA tree already proves the agreement for ITS OWN copy of the parser and renderer:
   lib/CJ/RL/GX/Printf_text.v declares pf_piece / pf_arg / pf_parse / pf_text with the same
   constructors and the same bodies, and printf_text_ok (Printf_text.v:869) closes
   printf_model = Ret (Ok (zlength T, T)) together with pass1_ok and the byte range.  Both copies
   descend from fuzz_disco's printf_facts_c.v, so nothing here is a new printf proof: this file is
   the type isomorphism between the two copies, plus the covered-piece side conditions.

   WHAT A NEW PIECE COSTS.  pt_parse_eq is piece-generic (one induction over the format bytes).
   Per piece, one lemma each:
     - the piece's renderer arm: pt_text_eq's case (for PLit / Ps / Pps: nothing to prove, the two
       bodies are convertible; for Pd / Pc / Px04 / Px02 / Pllu, the arm needs the one equation
       PT.pf_dec = pf_dec, PT.pf_hex4 = pf_hex4, PT.pf_hex2 = pf_hex2, PT.pf_udec = pf_udec,
       each an induction over the digit fuel);
     - the piece's argument shape: pt_pargs_eq's case and fm_args_kind's case.
   Nothing else in this file moves, and printf_text_ok already covers every conversion. *)
(* Modified by Theorem Labs, 2026-10: c-libc-stdio's copy for fuzz_preset (L3-V2, the GXA seam over ARx; parent c-libc-stdio 14:3xZ) of proofs/omx-clap-core/fuzz_manifest/lib/A/FMgxaSeamPf.v at origin/cold/port-fm-rtprintf-param 3e35620c52e: module paths fuzz_manifest -> fuzz_preset, lib/A/FMsnprintfPf -> lib/Reusable/FMsnprintfPf (h-mani-a8's copy, the same text); the covered pieces WIDENED from PLit | Ps | Pps to PLit | Pc | Px04 | Ps | Pps (preset's put_string pieces are PLit | Pc | Px04), at the cost the header above names: the Px04 arm needs PT.pf_hex4 = pf_hex4 (pt_hexs_eq, an induction over the digit fuel), and %04x's argument is the UNSIGNED int the model pops (Printf_text.v pf_pargs: PA_u (v mod 2^32)), so the argument list GXA receives is the piece-aware pt_pargs ps args, related to the arguments by Forall2 pt_parg_rel (pt_pargs_rel), instead of map pt_parg args; fm_model_agree concludes at pt_pargs ps args. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib Require Import ITree.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Spec Require Import Prelim Monad FmtFp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.GX Require Import Printf_model.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.GX Require G_printf_core_common.
Import OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.GX.G_printf_core_common.G_printf_iface.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.GX Require Printf_text.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import FMsnprintfPf.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Module PT := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.GX.Printf_text.

(* ---- the isomorphism between the two copies of the piece / argument types ---- *)
Definition pt_piece (p : pf_piece) : PT.pf_piece :=
  match p with
  | PLit b => PT.PLit b | Pd => PT.Pd | Pc => PT.Pc | Px04 => PT.Px04
  | Px02 => PT.Px02 | Pllu => PT.Pllu | Ps => PT.Ps | Pps => PT.Pps
  end.
Definition pt_arg (a : pf_arg) : PT.pf_arg :=
  match a with AInt v => PT.AInt v | AU64 u => PT.AU64 u | APtr s => PT.APtr s end.
(* the argument list the model consumes, one parg per argument (fm's pieces take APtr for %s and
   AInt then APtr for %.*s, in that order) *)
Definition pt_parg (a : pf_arg) : parg :=
  match a with AInt v => PA_i v | AU64 u => PA_ull u | APtr s => PA_s s end.

(* ---- the parser is the same function on both copies ---- *)
Lemma pt_parse_eq : forall n f, (length f <= n)%nat ->
  PT.pf_parse f = option_map (map pt_piece) (pf_parse f).
Proof.
induction n as [|n IH]; intros f Hn.
- destruct f as [|b r]; [reflexivity | cbn in Hn; lia].
- destruct f as [|b r]; [reflexivity|]. cbn in Hn.
  cbn [PT.pf_parse pf_parse]. destruct (b =? 37).
  + destruct r as [|c r1]; [reflexivity|]. cbn in Hn.
    assert (Hr1 : (length r1 <= n)%nat) by lia.
    destruct (c =? 100); [rewrite (IH r1 Hr1); destruct (pf_parse r1); reflexivity|].
    destruct (c =? 99); [rewrite (IH r1 Hr1); destruct (pf_parse r1); reflexivity|].
    destruct (c =? 115); [rewrite (IH r1 Hr1); destruct (pf_parse r1); reflexivity|].
    destruct (c =? 48).
    { destruct r1 as [|c2 r2]; [reflexivity|]. destruct r2 as [|c3 r3]; [reflexivity|].
      cbn in Hr1. assert (Hr3 : (length r3 <= n)%nat) by lia.
      destruct ((c2 =? 52) && (c3 =? 120)); [rewrite (IH r3 Hr3); destruct (pf_parse r3); reflexivity|].
      destruct ((c2 =? 50) && (c3 =? 120)); [rewrite (IH r3 Hr3); destruct (pf_parse r3); reflexivity|].
      reflexivity. }
    destruct (c =? 108).
    { destruct r1 as [|c2 r2]; [reflexivity|]. destruct r2 as [|c3 r3]; [reflexivity|].
      cbn in Hr1. assert (Hr3 : (length r3 <= n)%nat) by lia.
      destruct ((c2 =? 108) && (c3 =? 117)); [rewrite (IH r3 Hr3); destruct (pf_parse r3); reflexivity|].
      reflexivity. }
    destruct (c =? 46).
    { destruct r1 as [|c2 r2]; [reflexivity|]. destruct r2 as [|c3 r3]; [reflexivity|].
      cbn in Hr1. assert (Hr3 : (length r3 <= n)%nat) by lia.
      destruct ((c2 =? 42) && (c3 =? 115)); [rewrite (IH r3 Hr3); destruct (pf_parse r3); reflexivity|].
      reflexivity. }
    reflexivity.
  + destruct ((0 <? b) && (b <? 256)); [|reflexivity].
    rewrite (IH r ltac:(lia)). destruct (pf_parse r); reflexivity.
Qed.

Lemma pt_parse : forall f ps, pf_parse f = Some ps -> PT.pf_parse f = Some (map pt_piece ps).
Proof. intros f ps H. rewrite (pt_parse_eq (length f) f (le_n _)), H. reflexivity. Qed.

(* ---- the two copies of the hex renderer are the same function (for Px04) ---- *)
Lemma pt_hexd_eq : forall d, PT.pf_hexd d = pf_hexd d.
Proof. reflexivity. Qed.
Lemma pt_hexs_eq : forall fuel x acc, PT.pf_hexs fuel x acc = pf_hexs fuel x acc.
Proof.
induction fuel as [|fuel IH]; intros x acc; [reflexivity|].
cbn [PT.pf_hexs pf_hexs]. rewrite pt_hexd_eq. destruct (x <? 16); [reflexivity|].
rewrite pt_hexd_eq. exact (IH (x / 16) (pf_hexd (x mod 16) :: acc)).
Qed.
Lemma pt_hex4_eq : forall v, PT.pf_hex4 v = pf_hex4 v.
Proof. intros v. unfold PT.pf_hex4, pf_hex4. rewrite pt_hexs_eq. reflexivity. Qed.

(* the argument GXA's model pops for an argument of a covered piece: fm's pt_parg, or, for %04x, the unsigned int
   PA_u (v mod 2^32) (Printf_text.v pf_pargs) *)
Definition pt_parg_rel (a : pf_arg) (p : parg) : Prop :=
  p = pt_parg a \/ exists v, a = AInt v /\ p = PA_u (v mod 2 ^ 32).
Definition pt_pargs (ps : list pf_piece) (args : list pf_arg) : list parg :=
  PT.pf_pargs (map pt_piece ps) (map pt_arg args).

(* ---- the covered pieces: renderer, argument list, argument kinds ---- *)
(* PK is the unit's covered-piece predicate; fm instantiated it with pf_fm_piece (PLit / Ps / Pps), preset
   instantiates it with its put_string pieces (PLit / Pc / Px04).  Widening PK to another conversion is PK_cov plus that
   conversion's case in the lemmas below. *)
Section Covered.
Variable PK : pf_piece -> Prop.
Hypothesis PK_cov : forall p, PK p -> match p with PLit _ | Pc | Px04 | Ps | Pps => True | _ => False end.

Lemma pt_text_eq : forall ps args T, Forall PK ps -> pf_text ps args = Some T ->
  PT.pf_text (map pt_piece ps) (map pt_arg args) = Some T.
Proof.
induction ps as [|p ps IH]; intros args T HK HT.
- destruct args as [|a args]; cbn in HT |- *; [exact HT | discriminate].
- inversion HK as [|? ? Hp0 HK']; subst. apply PK_cov in Hp0. rename Hp0 into Hp.
  destruct p; try (exfalso; exact Hp).
  + (* PLit *) cbn [map pt_piece] in *. cbn [pf_text PT.pf_text] in HT |- *.
    destruct (pf_text ps args) as [T'|] eqn:E; cbn in HT; [|discriminate].
    rewrite (IH args T' HK' E). cbn. injection HT as <-. reflexivity.
  + (* Pc *) cbn [map pt_piece] in *. cbn [pf_text PT.pf_text] in HT |- *.
    destruct args as [|[v|u|s] args']; try discriminate.
    cbn [map pt_arg].
    destruct (pf_text ps args') as [T'|] eqn:E; cbn in HT; [|discriminate].
    rewrite (IH args' T' HK' E). cbn. injection HT as <-. reflexivity.
  + (* Px04 *) cbn [map pt_piece] in *. cbn [pf_text PT.pf_text] in HT |- *.
    destruct args as [|[v|u|s] args']; try discriminate.
    cbn [map pt_arg].
    destruct (pf_text ps args') as [T'|] eqn:E; cbn [option_map] in HT; [|discriminate].
    rewrite (IH args' T' HK' E). cbn [option_map]. rewrite pt_hex4_eq. injection HT as <-. reflexivity.
  + (* Ps *) cbn [map pt_piece] in *. cbn [pf_text PT.pf_text] in HT |- *.
    destruct args as [|[v|u|s] args']; try discriminate.
    cbn [map pt_arg].
    destruct (pf_text ps args') as [T'|] eqn:E; cbn in HT; [|discriminate].
    rewrite (IH args' T' HK' E). cbn. injection HT as <-. reflexivity.
  + (* Pps *) cbn [map pt_piece] in *. cbn [pf_text PT.pf_text] in HT |- *.
    destruct args as [|[k|u|s0] args']; try discriminate.
    destruct args' as [|[v|u|s] args'']; try discriminate.
    cbn [map pt_arg].
    destruct ((0 <=? k) && (k <=? Z.of_nat (length s))) eqn:Hk; [|discriminate].
    destruct (pf_text ps args'') as [T'|] eqn:E; cbn in HT; [|discriminate].
    rewrite (IH args'' T' HK' E). cbn. injection HT as <-. reflexivity.
Qed.

Lemma pt_pargs_rel : forall ps args T, Forall PK ps -> pf_text ps args = Some T ->
  Forall2 pt_parg_rel args (pt_pargs ps args).
Proof.
unfold pt_pargs.
induction ps as [|p ps IH]; intros args T HK HT.
- destruct args as [|a args]; cbn in HT |- *; [constructor | discriminate].
- inversion HK as [|? ? Hp0 HK']; subst. apply PK_cov in Hp0. rename Hp0 into Hp.
  destruct p; try (exfalso; exact Hp).
  + cbn [map pt_piece PT.pf_pargs]. cbn [pf_text] in HT.
    destruct (pf_text ps args) as [T'|] eqn:E; cbn in HT; [|discriminate].
    exact (IH args T' HK' E).
  + (* Pc: the signed int *) cbn [pf_text] in HT. destruct args as [|[v|u|s] args']; try discriminate.
    cbn [map pt_piece pt_arg PT.pf_pargs].
    destruct (pf_text ps args') as [T'|] eqn:E; cbn in HT; [|discriminate].
    constructor; [left; reflexivity | exact (IH args' T' HK' E)].
  + (* Px04: the unsigned int *) cbn [pf_text] in HT. destruct args as [|[v|u|s] args']; try discriminate.
    cbn [map pt_piece pt_arg PT.pf_pargs].
    destruct (pf_text ps args') as [T'|] eqn:E; cbn in HT; [|discriminate].
    constructor; [right; exists v; split; reflexivity | exact (IH args' T' HK' E)].
  + cbn [pf_text] in HT. destruct args as [|[v|u|s] args']; try discriminate.
    cbn [map pt_piece pt_arg PT.pf_pargs].
    destruct (pf_text ps args') as [T'|] eqn:E; cbn in HT; [|discriminate].
    constructor; [left; reflexivity | exact (IH args' T' HK' E)].
  + cbn [pf_text] in HT. destruct args as [|[k|u|s0] args']; try discriminate.
    destruct args' as [|[v|u|s] args'']; try discriminate.
    cbn [map pt_piece pt_arg PT.pf_pargs].
    destruct ((0 <=? k) && (k <=? Z.of_nat (length s))) eqn:Hk; [|discriminate].
    destruct (pf_text ps args'') as [T'|] eqn:E; cbn in HT; [|discriminate].
    constructor; [left; reflexivity|]. constructor; [left; reflexivity | exact (IH args'' T' HK' E)].
Qed.

(* a run over the covered pieces takes no 64-bit argument: %llu is not one of them *)
Lemma fm_args_kind : forall ps args T, Forall PK ps -> pf_text ps args = Some T ->
  forall u, ~ In (AU64 u) args.
Proof.
induction ps as [|p ps IH]; intros args T HK HT u Hin.
- destruct args as [|a args]; cbn in HT; [exact (in_nil Hin) | discriminate].
- inversion HK as [|? ? Hp0 HK']; subst. apply PK_cov in Hp0. rename Hp0 into Hp.
  destruct p; try (exfalso; exact Hp).
  + cbn [pf_text] in HT. destruct (pf_text ps args) as [T'|] eqn:E; cbn in HT; [|discriminate].
    exact (IH args T' HK' E u Hin).
  + cbn [pf_text] in HT. destruct args as [|[v|u'|s] args']; try discriminate.
    destruct (pf_text ps args') as [T'|] eqn:E; cbn in HT; [|discriminate].
    destruct Hin as [Hin|Hin]; [discriminate | exact (IH args' T' HK' E u Hin)].
  + cbn [pf_text] in HT. destruct args as [|[v|u'|s] args']; try discriminate.
    destruct (pf_text ps args') as [T'|] eqn:E; cbn in HT; [|discriminate].
    destruct Hin as [Hin|Hin]; [discriminate | exact (IH args' T' HK' E u Hin)].
  + cbn [pf_text] in HT. destruct args as [|[v|u'|s] args']; try discriminate.
    destruct (pf_text ps args') as [T'|] eqn:E; cbn in HT; [|discriminate].
    destruct Hin as [Hin|Hin]; [discriminate | exact (IH args' T' HK' E u Hin)].
  + cbn [pf_text] in HT. destruct args as [|[k|u'|s0] args']; try discriminate.
    destruct args' as [|[v|u'|s] args'']; try discriminate.
    destruct ((0 <=? k) && (k <=? Z.of_nat (length s))) eqn:Hk; [|discriminate].
    destruct (pf_text ps args'') as [T'|] eqn:E; cbn in HT; [|discriminate].
    destruct Hin as [Hin|[Hin|Hin]]; [discriminate | discriminate | exact (IH args'' T' HK' E u Hin)].
Qed.

(* ---- the agreement itself ---- *)
Theorem fm_model_agree : forall (fmtb : list Z) (ps : list pf_piece) (args : list pf_arg) (T : list Z),
  pf_parse fmtb = Some ps -> Forall PK ps -> pf_text ps args = Some T ->
  (forall v, In (AInt v) args -> -2^31 <= v < 2^31) ->
  (forall s, In (APtr s) args -> zlength s < 2147483647) ->
  zlength T <= 2147483647 ->
  printf_model (St:=list Z) (OUT_snf (zlength T)) OUTFP_snf (fmtb ++ [0]) (pt_pargs ps args) []
    = ITree.Ret (Ok (zlength T, T))
  /\ pass1_ok (fmtb ++ [0]) = true
  /\ Forall (fun c => 0 <= c < 256) (fmtb ++ [0]).
Proof.
intros fmtb ps args T HP HK HT HI HS HTl.
pose proof (pt_parse fmtb ps HP) as HP'.
pose proof (pt_text_eq ps args T HK HT) as HT'.
assert (HI' : forall v, In (PT.AInt v) (map pt_arg args) -> -2^31 <= v < 2^31).
{ intros v Hin. apply in_map_iff in Hin as ([v'|u'|s'] & E & Hin); cbn in E; try discriminate.
  injection E as <-. exact (HI _ Hin). }
assert (HU' : forall u, In (PT.AU64 u) (map pt_arg args) -> 0 <= u).
{ intros u Hin. apply in_map_iff in Hin as ([v'|u'|s'] & E & Hin); cbn in E; try discriminate.
  injection E as <-. exfalso. exact (fm_args_kind ps args T HK HT _ Hin). }
assert (HS' : forall s, In (PT.APtr s) (map pt_arg args) -> zlength s < 2147483647).
{ intros s Hin. apply in_map_iff in Hin as ([v'|u'|s'] & E & Hin); cbn in E; try discriminate.
  injection E as <-. exact (HS _ Hin). }
destruct (PT.printf_text_ok fmtb (map pt_piece ps) (map pt_arg args) T HP' HT' HI' HU' HTl
            (or_intror HS')) as (M & P1 & _ & BY).
split; [exact M | split; [exact P1 | exact BY]].
Qed.

End Covered.

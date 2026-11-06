(* Modified by Theorem Labs, 2026-10: relocated from omx-clap-core/fuzz_manifest lib/A/FMgxaSeamPf.v (a working branch 7e395de08f5) to libreac/fuzz_boxreg.asan-ubsan: module paths changed; 0 address numerals relocated (port_addr_check 5033540ba83b predict mode, symbol + offset); re-pointed Requires: FMsnprintfPf -> lib.A.Rt. *)
(* Step 2 of the evt -> SRr seam at musl vfprintf: MODEL AGREEMENT.

   The shared snprintf contract (FMsnprintfShared.v, a Theorem Labs lane) states what a run prints with
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
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.Lib Require Import ITree.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.Spec Require Import Prelim Monad FmtFp.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.RL.GX Require Import Printf_model.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.RL.GX Require G_printf_core_common.
Import OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.RL.GX.G_printf_core_common.G_printf_iface.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.RL.GX Require Printf_text.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Rt Require Import FMsnprintfPf.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Module PT := OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.RL.GX.Printf_text.

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

(* ---- the covered pieces: renderer, argument list, argument kinds ---- *)
(* PK is the unit's covered-piece predicate; fm instantiates it with FMsnprintfShared.v's
   pf_fm_piece (PLit / Ps / Pps).  Widening PK to another conversion is PK_cov plus that
   conversion's case in the three lemmas below. *)
Section Covered.
Variable PK : pf_piece -> Prop.
Hypothesis PK_cov : forall p, PK p -> match p with PLit _ | Ps | Pps => True | _ => False end.

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

Lemma pt_pargs_eq : forall ps args T, Forall PK ps -> pf_text ps args = Some T ->
  PT.pf_pargs (map pt_piece ps) (map pt_arg args) = map pt_parg args.
Proof.
induction ps as [|p ps IH]; intros args T HK HT.
- destruct args as [|a args]; cbn in HT |- *; [reflexivity | discriminate].
- inversion HK as [|? ? Hp0 HK']; subst. apply PK_cov in Hp0. rename Hp0 into Hp.
  destruct p; try (exfalso; exact Hp).
  + cbn [map pt_piece PT.pf_pargs]. cbn [pf_text] in HT.
    destruct (pf_text ps args) as [T'|] eqn:E; cbn in HT; [|discriminate].
    exact (IH args T' HK' E).
  + cbn [pf_text] in HT. destruct args as [|[v|u|s] args']; try discriminate.
    cbn [map pt_piece pt_arg PT.pf_pargs map pt_parg].
    destruct (pf_text ps args') as [T'|] eqn:E; cbn in HT; [|discriminate].
    rewrite (IH args' T' HK' E). reflexivity.
  + cbn [pf_text] in HT. destruct args as [|[k|u|s0] args']; try discriminate.
    destruct args' as [|[v|u|s] args'']; try discriminate.
    cbn [map pt_piece pt_arg PT.pf_pargs map pt_parg].
    destruct ((0 <=? k) && (k <=? Z.of_nat (length s))) eqn:Hk; [|discriminate].
    destruct (pf_text ps args'') as [T'|] eqn:E; cbn in HT; [|discriminate].
    rewrite (IH args'' T' HK' E). reflexivity.
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
  printf_model (St:=list Z) (OUT_snf (zlength T)) OUTFP_snf (fmtb ++ [0]) (map pt_parg args) []
    = ITree.Ret (Ok (zlength T, T))
  /\ pass1_ok (fmtb ++ [0]) = true
  /\ Forall (fun c => 0 <= c < 256) (fmtb ++ [0]).
Proof.
intros fmtb ps args T HP HK HT HI HS HTl.
pose proof (pt_parse fmtb ps HP) as HP'.
pose proof (pt_text_eq ps args T HK HT) as HT'.
pose proof (pt_pargs_eq ps args T HK HT) as HA'.
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
rewrite HA' in M. split; [exact M | split; [exact P1 | exact BY]].
Qed.

End Covered.

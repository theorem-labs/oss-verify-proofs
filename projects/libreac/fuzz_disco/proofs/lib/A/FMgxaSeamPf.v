(* Copied from proofs/omx-clap-core/fuzz_manifest/lib/A/FMgxaSeamPf.v (a working branch 0ddf65fd8cc); relocated to libreac/fuzz_disco.asan by reloc.py (target disco-A): module paths changed; 0 address numerals moved (port_addr_check 0767e70e074a predict, fm.asan -> fuzz_disco.asan, symbol + offset; table: this file's rows in provenance/evidence/g9-gxa/g9tool/g9-table-disco-A.tsv). *)
(* Step 2 of the evt -> SRr seam at musl vfprintf: MODEL AGREEMENT.

   The shared snprintf contract (proofs/omx-clap-core/fuzz_manifest/lib/A/FMsnprintfShared.v (a working branch 0ddf65fd8cc), a Theorem Labs lane) states what a run prints with
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

   WHAT A NEW PIECE COSTS (R-1 W0).  pt_parse_eq is piece-generic (one induction over the format bytes).
   A unit's covered-piece predicate PK widens by the three SEAM ARMS of each new piece p, each a statement
   about the single piece p and one step of the renderer (FMpfStep.v pf_step):
     - seam_text_arm p: GXA's renderer takes p's step as pf_text does (for PLit / Ps / Pps / Pc the two
       bodies are convertible; Pd / Px04 / Px02 / Pllu need PT.pf_dec = pf_dec, PT.pf_hex4 = pf_hex4,
       PT.pf_hex2 = pf_hex2, PT.pf_udec = pf_udec, each an induction over the digit fuel);
     - seam_pargs_arm p: the model's arguments for the ones p consumes (pt_parg_ok: pt_parg, or
       PA_u (v mod 2^32) at %04x / %02x);
     - seam_bytes_arm p: what p renders from fitting arguments (FMpfStep.v pf_arg_fit) is bytes.
   Section CoveredP proves the agreement for any PK from those three hypotheses; pf_fm_*_arms give them for
   fm's pieces (PLit / Ps / Pps).  printf_text_ok already covers every conversion. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib Require Import ITree.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Spec Require Import Prelim Monad FmtFp.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.GX Require Import Printf_model.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.GX Require G_printf_core_common.
Import OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.GX.G_printf_core_common.G_printf_iface.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.GX Require Printf_text.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import PfFacts.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A Require Import FMpfStep.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Module PT := OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.GX.Printf_text.

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

(* ==== the per-piece seam arms (R-1 W0) ==== *)
(* the model's argument for an argument a piece consumes: pt_parg of it, or, at %04x / %02x, the unsigned
   32-bit form GXA's model takes (Printf_text.v pf_pargs: PA_u (v mod 2^32)) *)
Definition pt_parg_ok (a : pf_arg) (pa : parg) : Prop :=
  pa = pt_parg a \/ exists v, a = AInt v /\ pa = PA_u (v mod 2^32).

(* the text: GXA's renderer takes p's step, whatever pieces follow *)
Definition seam_text_arm (p : pf_piece) : Prop :=
  forall (qs : list PT.pf_piece) (args : list pf_arg) (c : list Z) (a' : list pf_arg),
    pf_step p args = Some (c, a') ->
    PT.pf_text (pt_piece p :: qs) (map pt_arg args) = option_map (app c) (PT.pf_text qs (map pt_arg a')).

(* the model's arguments: one parg for each argument p consumes, pt_parg_ok *)
Definition seam_pargs_arm (p : pf_piece) : Prop :=
  forall (qs : list PT.pf_piece) (args : list pf_arg) (c : list Z) (a' : list pf_arg),
    pf_step p args = Some (c, a') ->
    exists (used : list pf_arg) (pas : list parg), args = used ++ a' /\ Forall2 pt_parg_ok used pas /\
      PT.pf_pargs (pt_piece p :: qs) (map pt_arg args) = pas ++ PT.pf_pargs qs (map pt_arg a').

(* the bytes: what p renders from fitting arguments is bytes *)
Definition seam_bytes_arm (p : pf_piece) : Prop :=
  forall (args : list pf_arg) (c : list Z) (a' : list pf_arg),
    pf_code_ok p -> Forall pf_arg_fit args -> pf_step p args = Some (c, a') -> Forall (fun x => 0 <= x < 256) c.

(* ---- fm's pieces have their arms ---- *)
Lemma seam_text_arm_lit : forall b, seam_text_arm (PLit b).
Proof.
intros b qs args c a' H. cbn [pf_step] in H. injection H as <- <-.
cbn [pt_piece PT.pf_text]. destruct (PT.pf_text qs (map pt_arg args)); reflexivity.
Qed.
Lemma seam_text_arm_ps : seam_text_arm Ps.
Proof.
intros qs args c a' H. destruct args as [|[v|u|s] a'']; cbn [pf_step] in H; try discriminate H.
injection H as <- <-. cbn [pt_piece map pt_arg PT.pf_text].
destruct (PT.pf_text qs (map pt_arg a'')); reflexivity.
Qed.
Lemma seam_text_arm_pps : seam_text_arm Pps.
Proof.
intros qs args c a' H. destruct args as [|[k|u|s0] [|[v|u'|s] a'']]; cbn [pf_step] in H; try discriminate H.
cbn [pt_piece map pt_arg PT.pf_text].
destruct ((0 <=? k) && (k <=? Z.of_nat (length s))); [|discriminate H]. injection H as <- <-.
destruct (PT.pf_text qs (map pt_arg a'')); reflexivity.
Qed.

Lemma seam_pargs_arm_lit : forall b, seam_pargs_arm (PLit b).
Proof.
intros b qs args c a' H. cbn [pf_step] in H. injection H as <- <-.
exists [], []. split; [reflexivity|]. split; [constructor | reflexivity].
Qed.
Lemma seam_pargs_arm_ps : seam_pargs_arm Ps.
Proof.
intros qs args c a' H. destruct args as [|[v|u|s] a'']; cbn [pf_step] in H; try discriminate H.
injection H as <- <-. exists [APtr s], [PA_s s].
split; [reflexivity|]. split; [constructor; [left; reflexivity | constructor] | reflexivity].
Qed.
Lemma seam_pargs_arm_pps : seam_pargs_arm Pps.
Proof.
intros qs args c a' H. destruct args as [|[k|u|s0] [|[v|u'|s] a'']]; cbn [pf_step] in H; try discriminate H.
destruct ((0 <=? k) && (k <=? Z.of_nat (length s))); [|discriminate H]. injection H as <- <-.
exists [AInt k; APtr s], [PA_i k; PA_s s].
split; [reflexivity|].
split; [constructor; [left; reflexivity | constructor; [left; reflexivity | constructor]] | reflexivity].
Qed.

Lemma seam_bytes_arm_lit : forall b, seam_bytes_arm (PLit b).
Proof.
intros b args c a' Hok _ H. cbn [pf_step] in H. injection H as <- _. cbn in Hok.
constructor; [lia | constructor].
Qed.
Lemma seam_bytes_arm_ps : seam_bytes_arm Ps.
Proof.
intros args c a' _ HF H. destruct args as [|[v|u|s] a'']; cbn [pf_step] in H; try discriminate H.
injection H as <- _. inversion HF as [|? ? Hs0 _]; subst. destruct Hs0 as [Hs _].
eapply Forall_impl; [|exact Hs]. intros x Hx. cbv beta in *. lia.
Qed.
Lemma seam_bytes_arm_pps : seam_bytes_arm Pps.
Proof.
intros args c a' _ HF H. destruct args as [|[k|u|s0] [|[v|u'|s] a'']]; cbn [pf_step] in H; try discriminate H.
destruct ((0 <=? k) && (k <=? Z.of_nat (length s))); [|discriminate H]. injection H as <- _.
inversion HF as [|? ? _ HF']; subst. inversion HF' as [|? ? Hs0 _]; subst. destruct Hs0 as [Hs _].
assert (G : forall n (l : list Z), Forall (fun x => 0 < x < 256) l -> Forall (fun x => 0 <= x < 256) (firstn n l)).
{ induction n as [|n IH]; intros l Hl; [constructor|]. destruct l as [|x l]; [constructor|].
  inversion Hl; subst. cbn [firstn]. constructor; [lia | apply IH; assumption]. }
exact (G _ _ Hs).
Qed.

(* fm's pieces (FMsnprintfShared.v pf_fm_piece is this predicate) *)
Lemma pf_fm_text_arms : forall p, match p with PLit _ | Ps | Pps => True | _ => False end -> seam_text_arm p.
Proof.
intros p Hp. destruct p; try (exfalso; exact Hp).
- apply seam_text_arm_lit.
- exact seam_text_arm_ps.
- exact seam_text_arm_pps.
Qed.
Lemma pf_fm_pargs_arms : forall p, match p with PLit _ | Ps | Pps => True | _ => False end -> seam_pargs_arm p.
Proof.
intros p Hp. destruct p; try (exfalso; exact Hp).
- apply seam_pargs_arm_lit.
- exact seam_pargs_arm_ps.
- exact seam_pargs_arm_pps.
Qed.
Lemma pf_fm_bytes_arms : forall p, match p with PLit _ | Ps | Pps => True | _ => False end -> seam_bytes_arm p.
Proof.
intros p Hp. destruct p; try (exfalso; exact Hp).
- apply seam_bytes_arm_lit.
- exact seam_bytes_arm_ps.
- exact seam_bytes_arm_pps.
Qed.

(* ==== the agreement for any covered-piece predicate PK whose pieces have their arms ==== *)
Section CoveredP.
Variable PK : pf_piece -> Prop.
Hypothesis ARM_text : forall p, PK p -> seam_text_arm p.
Hypothesis ARM_pargs : forall p, PK p -> seam_pargs_arm p.
Hypothesis ARM_bytes : forall p, PK p -> seam_bytes_arm p.

Lemma pt_text_eqP : forall ps args T, Forall PK ps -> pf_text ps args = Some T ->
  PT.pf_text (map pt_piece ps) (map pt_arg args) = Some T.
Proof.
induction ps as [|p ps IH]; intros args T HK HT.
- destruct args as [|a args]; cbn in HT |- *; [exact HT | discriminate].
- inversion HK as [|? ? Hp HK']; subst. rewrite pf_text_step in HT.
  destruct (pf_step p args) as [[c a']|] eqn:ES; [|discriminate HT].
  destruct (pf_text ps a') as [T'|] eqn:E; cbn in HT; [|discriminate HT]. injection HT as <-.
  cbn [map]. rewrite (ARM_text p Hp (map pt_piece ps) args c a' ES), (IH a' T' HK' E). reflexivity.
Qed.

Lemma pt_pargs_shapeP : forall ps args T, Forall PK ps -> pf_text ps args = Some T ->
  Forall2 pt_parg_ok args (PT.pf_pargs (map pt_piece ps) (map pt_arg args)).
Proof.
induction ps as [|p ps IH]; intros args T HK HT.
- destruct args as [|a args]; cbn in HT |- *; [constructor | discriminate].
- inversion HK as [|? ? Hp HK']; subst. rewrite pf_text_step in HT.
  destruct (pf_step p args) as [[c a']|] eqn:ES; [|discriminate HT].
  destruct (pf_text ps a') as [T'|] eqn:E; cbn in HT; [|discriminate HT].
  destruct (ARM_pargs p Hp (map pt_piece ps) args c a' ES) as (used & pas & Eu & F2 & EP).
  cbn [map]. rewrite EP, Eu. apply Forall2_app; [exact F2 | exact (IH a' T' HK' E)].
Qed.

Lemma pf_text_bytesP : forall ps args T, Forall pf_code_ok ps -> Forall PK ps -> Forall pf_arg_fit args ->
  pf_text ps args = Some T -> Forall (fun x => 0 <= x < 256) T.
Proof.
induction ps as [|p ps IH]; intros args T HC HK HF HT.
- destruct args as [|a args]; cbn in HT; [injection HT as <-; constructor | discriminate].
- inversion HK as [|? ? Hp HK']; subst. inversion HC as [|? ? Hc HC']; subst. rewrite pf_text_step in HT.
  destruct (pf_step p args) as [[c a']|] eqn:ES; [|discriminate HT].
  destruct (pf_text ps a') as [T'|] eqn:E; cbn in HT; [|discriminate HT]. injection HT as <-.
  destruct (pf_step_prefix p args c a' ES) as [used Eu].
  assert (HF' : Forall pf_arg_fit a') by (rewrite Eu in HF; apply Forall_app in HF; exact (proj2 HF)).
  apply Forall_app. split; [exact (ARM_bytes p Hp args c a' Hc HF ES) | exact (IH a' T' HC' HK' HF' E)].
Qed.

(* the agreement: GXA's model on the format, with the model's own argument list *)
Theorem pf_model_agreeP : forall (fmtb : list Z) (ps : list pf_piece) (args : list pf_arg) (T : list Z),
  pf_parse fmtb = Some ps -> Forall PK ps -> pf_text ps args = Some T -> Forall pf_arg_fit args ->
  zlength T <= 2147483647 ->
  printf_model (St:=list Z) (OUT_snf (zlength T)) OUTFP_snf (fmtb ++ [0])
      (PT.pf_pargs (map pt_piece ps) (map pt_arg args)) []
    = ITree.Ret (Ok (zlength T, T))
  /\ pass1_ok (fmtb ++ [0]) = true
  /\ Forall (fun c => 0 <= c < 256) (fmtb ++ [0]).
Proof.
intros fmtb ps args T HP HK HT HF HTl.
pose proof (pt_parse fmtb ps HP) as HP'.
pose proof (pt_text_eqP ps args T HK HT) as HT'.
rewrite Forall_forall in HF.
assert (HI' : forall v, In (PT.AInt v) (map pt_arg args) -> -2^31 <= v < 2^31).
{ intros v Hin. apply in_map_iff in Hin as ([v'|u'|s'] & E & Hin); cbn in E; try discriminate.
  injection E as <-. exact (HF _ Hin). }
assert (HU' : forall u, In (PT.AU64 u) (map pt_arg args) -> 0 <= u).
{ intros u Hin. apply in_map_iff in Hin as ([v'|u'|s'] & E & Hin); cbn in E; try discriminate.
  injection E as <-. exact (proj1 (HF _ Hin)). }
assert (HS' : forall s, In (PT.APtr s) (map pt_arg args) -> zlength s < 2147483647).
{ intros s Hin. apply in_map_iff in Hin as ([v'|u'|s'] & E & Hin); cbn in E; try discriminate.
  injection E as <-. destruct (HF _ Hin) as [_ Hl]. unfold zlength. lia. }
destruct (PT.printf_text_ok fmtb (map pt_piece ps) (map pt_arg args) T HP' HT' HI' HU' HTl
            (or_intror HS')) as (M & P1 & _ & BY).
split; [exact M | split; [exact P1 | exact BY]].
Qed.

End CoveredP.

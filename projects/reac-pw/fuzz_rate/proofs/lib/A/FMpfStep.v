(* Copied from proofs/omx-clap-core/fuzz_manifest/lib/A/FMpfStep.v (cold/port-fm-rtprintf-param 0ddf65fd8cc); relocated to libreac/fuzz_disco.asan by g9/tool (reloc.py target disco-A): module paths changed; 0 address numerals moved (port_addr_check 0767e70e074a predict, fm.asan -> fuzz_disco.asan, symbol + offset; table g9/tool/tables/disco-A/FMpfStep.table). *)
(* Modified by Theorem Labs, 2026-10: proofs/libreac/fuzz_disco/lib/A/FMpfStep.v at 2d2ff01bb6f2 relocated to reac-pw/fuzz_rate's ASan image A: module paths changed; numerals by port_core 1e42da8952ec (ledger provenance/reloc/A-Snp.tsv). *)
(* One format piece at a time (the shared printf route's per-piece interface, R-1 W0). For each piece p of
   FMsnprintfPf.v:
   - pf_step p args: what pf_text renders for p and the arguments it leaves (pf_text_step: pf_text is the steps
     one after the other);
   - pf_code p: the format bytes pf_parse reads p from (pf_parse_split: a parsed format is its pieces' codes);
   - pf_arg_fit: the ranges a run's arguments have (a 32-bit int, a 64-bit unsigned word, a string of nonzero bytes).
   The per-piece ARM statements are stated over these: FMgxaSeamPf.v seam_arm (GXA's model of musl vfprintf) and
   RT_pf_sh.v pcom_arm (ASan's printf_common scan); FMpfArms.v bundles them. Image-neutral. New file. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Rt Require Import PfFacts.
Import ListNotations.
Open Scope Z_scope.

(* ---- the renderer, one piece ---- *)
Definition pf_step (p : pf_piece) (args : list pf_arg) : option (list Z * list pf_arg) :=
  match p, args with
  | PLit b, _ => Some ([b], args)
  | Pd, AInt v :: a' => Some (pf_dec v, a')
  | Pc, AInt v :: a' => Some ([v mod 256], a')
  | Px04, AInt v :: a' => Some (pf_hex4 v, a')
  | Px02, AInt v :: a' => Some (pf_hex2 v, a')
  | Pllu, AU64 u :: a' => Some (pf_udec u, a')
  | Ps, APtr s :: a' => Some (s, a')
  | Pps, AInt k :: APtr s :: a' =>
      if (0 <=? k) && (k <=? Z.of_nat (length s)) then Some (firstn (Z.to_nat k) s, a') else None
  | _, _ => None
  end.

Lemma pf_text_step : forall p ps args,
  pf_text (p :: ps) args =
  match pf_step p args with Some (c, a') => option_map (app c) (pf_text ps a') | None => None end.
Proof.
intros p ps args.
destruct p; cbn [pf_text pf_step];
  [destruct (pf_text ps args); reflexivity | ..];
  destruct args as [|[v|u|s] [|[v'|u'|s'] a'']]; try reflexivity.
all: destruct (_ && _); reflexivity.
Qed.

(* a step consumes a prefix of the arguments *)
Lemma pf_step_prefix : forall p args c a', pf_step p args = Some (c, a') -> exists used, args = used ++ a'.
Proof.
intros p args c a' H.
destruct p; cbn [pf_step] in H;
  [injection H as _ <-; exists []; reflexivity | ..];
  destruct args as [|[v|u|s] [|[v'|u'|s'] a'']]; try discriminate H;
  try (injection H as _ <-; eexists; rewrite <- app_comm_cons, app_nil_l; reflexivity).
all: destruct (_ && _); [|discriminate H]; injection H as _ <-; exists [AInt v; APtr s']; reflexivity.
Qed.

(* ---- the parser, one piece ---- *)
Definition pf_code (p : pf_piece) : list Z :=
  match p with
  | PLit b => [b] | Pd => [37; 100] | Pc => [37; 99] | Px04 => [37; 48; 52; 120] | Px02 => [37; 48; 50; 120]
  | Pllu => [37; 108; 108; 117] | Ps => [37; 115] | Pps => [37; 46; 42; 115]
  end.

(* a literal byte is a nonzero byte other than '%' *)
Definition pf_code_ok (p : pf_piece) : Prop := match p with PLit b => 0 < b < 256 /\ b <> 37 | _ => True end.

Lemma pf_parse_nil : forall fmt, pf_parse fmt = Some [] -> fmt = [].
Proof.
intros [|b r] H; [reflexivity|]. exfalso. cbn [pf_parse] in H.
destruct (b =? 37).
- destruct r as [|c r1]; [discriminate H|].
  destruct (c =? 100); [destruct (pf_parse r1); discriminate H|].
  destruct (c =? 99); [destruct (pf_parse r1); discriminate H|].
  destruct (c =? 115); [destruct (pf_parse r1); discriminate H|].
  destruct (c =? 48).
  { destruct r1 as [|c2 [|c3 r3]]; try discriminate H.
    destruct (_ && _); [destruct (pf_parse r3); discriminate H|].
    destruct (_ && _); [destruct (pf_parse r3); discriminate H | discriminate H]. }
  destruct (c =? 108).
  { destruct r1 as [|c2 [|c3 r3]]; try discriminate H.
    destruct (_ && _); [destruct (pf_parse r3); discriminate H | discriminate H]. }
  destruct (c =? 46); [|discriminate H].
  destruct r1 as [|c2 [|c3 r3]]; try discriminate H.
  destruct (_ && _); [destruct (pf_parse r3); discriminate H | discriminate H].
- destruct (_ && _); [destruct (pf_parse r); discriminate H | discriminate H].
Qed.

Lemma pf_parse_split : forall fmt p ps, pf_parse fmt = Some (p :: ps) ->
  exists r, fmt = pf_code p ++ r /\ pf_parse r = Some ps /\ pf_code_ok p.
Proof.
intros [|b r] p ps H; [discriminate H|]. cbn [pf_parse] in H.
assert (T : forall k r', option_map (cons k) (pf_parse r') = Some (p :: ps) -> k = p /\ pf_parse r' = Some ps).
{ intros k r' E. destruct (pf_parse r'); cbn in E; [injection E as -> ->; split; reflexivity | discriminate E]. }
destruct (Z.eqb_spec b 37) as [->|N37].
- destruct r as [|c r1]; [discriminate H|].
  destruct (Z.eqb_spec c 100) as [->|_]; [destruct (T _ _ H) as [<- E]; exists r1; split; [reflexivity|]; split; [exact E | exact I]|].
  destruct (Z.eqb_spec c 99) as [->|_]; [destruct (T _ _ H) as [<- E]; exists r1; split; [reflexivity|]; split; [exact E | exact I]|].
  destruct (Z.eqb_spec c 115) as [->|_]; [destruct (T _ _ H) as [<- E]; exists r1; split; [reflexivity|]; split; [exact E | exact I]|].
  destruct (Z.eqb_spec c 48) as [->|_].
  { destruct r1 as [|c2 [|c3 r3]]; try discriminate H.
    destruct ((c2 =? 52) && (c3 =? 120)) eqn:E4.
    - apply andb_true_iff in E4 as [E4a E4b]. apply Z.eqb_eq in E4a, E4b. subst c2 c3.
      destruct (T _ _ H) as [<- E]. exists r3. split; [reflexivity|]. split; [exact E | exact I].
    - destruct ((c2 =? 50) && (c3 =? 120)) eqn:E2; [|discriminate H].
      apply andb_true_iff in E2 as [E2a E2b]. apply Z.eqb_eq in E2a, E2b. subst c2 c3.
      destruct (T _ _ H) as [<- E]. exists r3. split; [reflexivity|]. split; [exact E | exact I]. }
  destruct (Z.eqb_spec c 108) as [->|_].
  { destruct r1 as [|c2 [|c3 r3]]; try discriminate H.
    destruct ((c2 =? 108) && (c3 =? 117)) eqn:E8; [|discriminate H].
    apply andb_true_iff in E8 as [E8a E8b]. apply Z.eqb_eq in E8a, E8b. subst c2 c3.
    destruct (T _ _ H) as [<- E]. exists r3. split; [reflexivity|]. split; [exact E | exact I]. }
  destruct (Z.eqb_spec c 46) as [->|_]; [|discriminate H].
  destruct r1 as [|c2 [|c3 r3]]; try discriminate H.
  destruct ((c2 =? 42) && (c3 =? 115)) eqn:E6; [|discriminate H].
  apply andb_true_iff in E6 as [E6a E6b]. apply Z.eqb_eq in E6a, E6b. subst c2 c3.
  destruct (T _ _ H) as [<- E]. exists r3. split; [reflexivity|]. split; [exact E | exact I].
- destruct ((0 <? b) && (b <? 256)) eqn:Eb; [|discriminate H].
  apply andb_true_iff in Eb as [E1 E2]. apply Z.ltb_lt in E1, E2.
  destruct (T _ _ H) as [<- E]. exists r. split; [reflexivity|]. split; [exact E|]. cbn. lia.
Qed.

(* ---- the arguments' ranges ---- *)
Definition pf_arg_fit (a : pf_arg) : Prop :=
  match a with
  | AInt v => -2 ^ 31 <= v < 2 ^ 31
  | AU64 u => 0 <= u < 2 ^ 64
  | APtr s => Forall (fun c => 0 < c < 256) s /\ Z.of_nat (length s) + 8 < 2 ^ 31
  end.

(* every piece of a parsed format has its code_ok *)
Lemma pf_parse_codes_n : forall n fmt ps, (length fmt <= n)%nat -> pf_parse fmt = Some ps -> Forall pf_code_ok ps.
Proof.
induction n as [|n IH]; intros fmt ps Hn H.
- destruct fmt as [|b r]; [cbn in H; injection H as <-; constructor | cbn in Hn; lia].
- destruct ps as [|p ps]; [constructor|].
  destruct (pf_parse_split fmt p ps H) as (r & -> & Hr & Hok).
  constructor; [exact Hok|]. apply (IH r ps); [|exact Hr].
  rewrite length_app in Hn. destruct p; cbn [pf_code length] in Hn; lia.
Qed.

Lemma pf_parse_codes : forall fmt ps, pf_parse fmt = Some ps -> Forall pf_code_ok ps.
Proof. intros fmt ps H. exact (pf_parse_codes_n (length fmt) fmt ps (le_n _) H). Qed.

(* The format-family constructors of port-fm's FMsnprintfShared.v (origin/cold/port-fm-rtprintf-param 7e395de08f5,
   :42-69 str_end / pf_arg_asan / pf_args_asan / fmt_at and :83-97 pf_prec_pos / pf_family), which PSnpShared.v leaves
   out because the chain is generic in FF, and the families printf_common's contract is stated for: port-fm's FF_pcom
   (lib/A/RT_pf_sh.v:157-171) with its pieces widened to literals, %c, %04x, %s and %.*s and the image top a parameter
   (FF_pcom_x), and h-mani-a8's FF_preset (origin/cold/h-mani-a8-preset-alloc a8439a761af0 lib/A/CfSnprintfPreset.v:
   pieces literal, %c, %04x; the format between the image's low end and the stack-protector GOT cell; nonempty) with
   those two bounds parameters instead of CfImg_A fields (FF_preset_x), and the inclusion FF_preset_x -> FF_pcom_x.
   Pieces, parser and renderer: lib/Reusable/FMsnprintfPf.v, h-mani-a8's copy taken by path from a8439a761af0
   (blob 9f89f54c01c4). No image numeral. *)
(* Modified by Theorem Labs, 2026-10: c-libc-stdio's file for fuzz_preset (route (a) P2, ASan's printf_common over ARx;
   parent c-libc-stdio 13:0xZ). New file; the definitions above are copied unchanged from the sources named. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import FMsnprintfPf PSnpShared.
Import ListNotations.
Local Open Scope Z_scope.

(* ---- FMsnprintfShared.v:42-69 ---- *)
Definition str_end (w : Z) (s : list Z) : Z :=
w + Z.of_nat (length s) - (w + Z.of_nat (length s)) mod 8 + 8.
Definition pf_arg_asan (rd : reader) (rs : list (Z * Z)) (w : Z) (a : pf_arg) : Prop :=
match a with
| AInt v => -2 ^ 31 <= v < 2 ^ 31 /\ w mod 2 ^ 32 = v mod 2 ^ 32
| AU64 u => w = u
| APtr s =>
Forall (fun c => 0 < c < 256) s /\ 0 < w /\ Z.of_nat (length s) + 8 < 2 ^ 31 /\
(forall i, 0 <= i <= Z.of_nat (length s) -> rd (w + i) = Some (nth (Z.to_nat i) (s ++ [0]) 0)) /\
(forall x, w + Z.of_nat (length s) < x < str_end w s -> rd x <> None) /\
Forall (zdisjoint (w, str_end w s - w)) rs /\
amem_range w (Z.of_nat (length s) + 1) /\
range_addressable rd SHADOW_OFF w (Z.of_nat (length s) + 1) /\
shadow_hull_vis rd w (Z.of_nat (length s) + 1)
end.
Fixpoint pf_args_asan (rd : reader) (rs : list (Z * Z)) (ws : list Z) (args : list pf_arg) : Prop :=
match args, ws with
| [], _ => True
| a :: args', w :: ws' => pf_arg_asan rd rs w a /\ pf_args_asan rd rs ws' args'
| _ :: _, [] => False
end.
Definition fmt_at (rd : reader) (rs : list (Z * Z)) (f : Z) (fmt : list Z) : Prop :=
0 < f /\
(forall i, 0 <= i <= Z.of_nat (length fmt) -> rd (f + i) = Some (nth (Z.to_nat i) (fmt ++ [0]) 0)) /\
Forall (zdisjoint (f, Z.of_nat (length fmt) + 1)) rs /\
amem_range f (Z.of_nat (length fmt) + 1) /\
range_addressable rd SHADOW_OFF f (Z.of_nat (length fmt) + 1) /\
shadow_hull_vis rd f (Z.of_nat (length fmt) + 1).

(* ---- FMsnprintfShared.v:83-97 ---- *)
(* every %.*s precision is at least 1 (pf_text already asks k <= len s) *)
Fixpoint pf_prec_pos (ps : list pf_piece) (args : list pf_arg) : Prop :=
match ps, args with
| [], _ => True
| PLit _ :: ps', _ => pf_prec_pos ps' args
| Pps :: ps', AInt k :: _ :: a' => 1 <= k /\ pf_prec_pos ps' a'
| Pps :: _, _ => True
| _ :: ps', _ :: a' => pf_prec_pos ps' a'
| _ :: _, [] => True
end.
(* h-rw-dis-5's family for the conversions PK covers (FMsnprintfShared.v:93-97) *)
Definition pf_family (PK : pf_piece -> Prop) : fmt_fam := fun rd rs f ws T =>
exists (fmt : list Z) (ps : list pf_piece) (args : list pf_arg),
fmt_at rd rs f fmt /\ pf_parse fmt = Some ps /\ Forall PK ps /\ pf_args_asan rd rs ws args /\
pf_text ps args = Some T /\ pf_prec_pos ps args.

(* ---- the families of printf_common's contract ---- *)
(* the conversions ASan's printf_common grammar (Bz I_pcxgram.v) is shown to accept here: literals, %c, %04x, %s, %.*s *)
Definition pf_pcom_piece (p : pf_piece) : Prop :=
  match p with PLit _ | Pc | Px04 | Ps | Pps => True | _ => False end.
(* put_string's conversions (h-mani-a8's pf_preset_piece, CfSnprintfPreset.v) *)
Definition pf_preset_piece (p : pf_piece) : Prop :=
  match p with PLit _ | Pc | Px04 => True | _ => False end.

(* every %s / %.*s string with its NUL word inside the application memory (RT_pf_sh.v:159-164, unchanged) *)
Fixpoint pf_args_amem (ws : list Z) (args : list pf_arg) : Prop :=
  match args, ws with
  | APtr s :: a', w :: w' => amem_range w (Z.of_nat (length s) + 8) /\ pf_args_amem w' a'
  | _ :: a', _ :: w' => pf_args_amem w' a'
  | _, _ => True
  end.

(* RT_pf_sh.v:167-171 FF_pcom with the pieces pf_pcom_piece and the image top ie a parameter (fm: TFIB_IMG_END) *)
Definition FF_pcom_x (ie : Z) : fmt_fam := fun rd rs f ws T =>
  exists (fmt : list Z) (ps : list pf_piece) (args : list pf_arg),
  fmt_at rd rs f fmt /\ fmt <> [] /\ f + Z.of_nat (length fmt) + 1 <= ie /\
  pf_parse fmt = Some ps /\ Forall pf_pcom_piece ps /\ pf_args_asan rd rs ws args /\ pf_args_amem ws args /\
  pf_text ps args = Some T /\ pf_prec_pos ps args.

(* h-mani-a8's FF_preset (CfSnprintfPreset.v) with @cf_img_lo CfImg_A and @cf_got_stack_chk_guard CfImg_A as the
   parameters lo and got *)
Definition FF_preset_x (lo got : Z) : fmt_fam := fun rd rs f ws T =>
  exists (fmt : list Z) (ps : list pf_piece) (args : list pf_arg),
    fmt_at rd rs f fmt /\ pf_parse fmt = Some ps /\ Forall pf_preset_piece ps /\ pf_args_asan rd rs ws args /\
    pf_text ps args = Some T /\ pf_prec_pos ps args /\
    lo <= f /\ f + Z.of_nat (length fmt) + 1 <= got /\ fmt <> [].

(* put_string's pieces take no string argument *)
Lemma pf_text_preset_noptr : forall ps args T, Forall pf_preset_piece ps -> pf_text ps args = Some T ->
  forall s, ~ In (APtr s) args.
Proof.
  induction ps as [|p ps IH]; intros args T HK HT s Hin.
  - cbn in HT. destruct args; [exact Hin | discriminate HT].
  - inversion HK as [|? ? Hp HK']; subst. destruct p; try destruct Hp.
    + cbn [pf_text] in HT. destruct (pf_text ps args) as [T'|] eqn:E; [|discriminate HT]. exact (IH args T' HK' E s Hin).
    + cbn [pf_text] in HT. destruct args as [|[v|u|s0] a']; try discriminate HT.
      destruct (pf_text ps a') as [T'|] eqn:E; [|discriminate HT].
      destruct Hin as [Hin|Hin]; [discriminate Hin | exact (IH a' T' HK' E s Hin)].
    + cbn [pf_text] in HT. destruct args as [|[v|u|s0] a']; try discriminate HT.
      destruct (pf_text ps a') as [T'|] eqn:E; [|discriminate HT].
      destruct Hin as [Hin|Hin]; [discriminate Hin | exact (IH a' T' HK' E s Hin)].
Qed.

Lemma pf_args_amem_noptr : forall args ws, (forall s, ~ In (APtr s) args) -> pf_args_amem ws args.
Proof.
  induction args as [|a args IH]; intros ws H; [destruct ws; exact I|].
  destruct ws as [|w ws]; [destruct a; exact I|].
  destruct a as [v|u|s].
  - cbn. apply IH. intros s Hs. exact (H s (or_intror Hs)).
  - cbn. apply IH. intros s Hs. exact (H s (or_intror Hs)).
  - exfalso. exact (H s (or_introl eq_refl)).
Qed.

(* FF_preset_x is inside FF_pcom_x when the GOT cell lies at or below the image top *)
Lemma FF_preset_x_pcom : forall lo got ie, got <= ie ->
  forall rd rs f ws T, FF_preset_x lo got rd rs f ws T -> FF_pcom_x ie rd rs f ws T.
Proof.
  intros lo got ie Hg rd rs f ws T (fmt & ps & args & HF & HP & HK & HA & HT & HPP & Hlo & Hhi & HNE).
  exists fmt, ps, args. split; [exact HF|]. split; [exact HNE|]. split; [lia|]. split; [exact HP|].
  split; [eapply Forall_impl; [|exact HK]; intros p Hp; destruct p; try exact I; destruct Hp|].
  split; [exact HA|]. split; [exact (pf_args_amem_noptr args ws (pf_text_preset_noptr ps args T HK HT))|].
  split; [exact HT | exact HPP].
Qed.

(* reac-pw/fuzz_link, image A: the format family of link's printf-family calls, from the contracts' own vocabulary.

   link's own contracts state a format and its arguments in lib/Prog/printf_facts_c.v's model (`pf_piece`, `pf_arg`,
   `pf_parse`, `pf_text`) over link_amem.v's views (`acstr_at`, model_decide_c.v `astr_rt_ok`, reac_code_emit_c.v
   `apf_arg_ok`). The libc printf contracts (lib/A/Rt/LinkVfDefs.v, LinkSnpDef.v) take a format family over
   lib/Rt/PfFacts.v's model (a copy of printf_facts_c.v's text, so another inductive type) and SnShared.v's readers
   (`fmt_at`, `pf_args_asan`, `pf_family`). This file is the bridge:
   - section t: the two models are the same function on translated pieces and arguments (`pf_parse_tr`,
     `pf_text_tr`); a format that parses has its bytes in 1..255 (`pf_parse_bytes`); the pieces link's calls use
     (literal, %d, %s: `apf_link_piece`) are lib/A/Rt/LinkPfPiece.v's `pf_link_piece` after translation and need no
     precision (`pf_prec_pos`);
   - section m: at a memory m and a call whose regions are `vmf_out Kc spc f` (the callee window inside the caller's
     window [sp - K, sp), and link's FILE block), a C string with `astr_rt_ok` is `pf_arg_asan` (`astr_asan`), a
     format with `astr_rt_ok` is `fmt_at` (`afmt_at`), `apf_args_ok` over the vararg registers is `pf_args_asan` over
     their values (`apf_args_asan`), and together they give `pf_family pf_link_piece` (`pf_family_of_c`) and the
     closed printf contracts' family LinkVfInst.v `link_vf_FF` (`link_vf_FF_of_c`, with `apf_args_slack`).
   The strings lie outside the callee window because `astr_rt_ok`'s `apart_frame regs K` puts them outside the
   caller's [sp - K, sp), which holds the callee's; the rest of a string's last word (str_end) stays outside too,
   because sp - K is a multiple of 8.

   Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YI04 YM05 YG0v YG0f YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require printf_facts_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Rt Require PfFacts.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Rt Require Import SnShared SnFF.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AMemFileSink.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require RT_pf_sh.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import LinkPfPiece LinkVfDefs LinkVfInst.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_amem model_decide_c reac_code_emit_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Module PFC := printf_facts_c.
Module PFF := PfFacts.

(* ==========================================================================
   t. The two printf models
   ========================================================================== *)

Definition pp_tr (p : PFC.pf_piece) : PFF.pf_piece :=
  match p with
  | PFC.PLit b => PFF.PLit b | PFC.Pd => PFF.Pd | PFC.Pc => PFF.Pc | PFC.Px04 => PFF.Px04 | PFC.Px02 => PFF.Px02
  | PFC.Pllu => PFF.Pllu | PFC.Ps => PFF.Ps | PFC.Pps => PFF.Pps
  end.

Definition pa_tr (a : PFC.pf_arg) : PFF.pf_arg :=
  match a with PFC.AInt v => PFF.AInt v | PFC.AU64 u => PFF.AU64 u | PFC.APtr s => PFF.APtr s end.

Lemma pf_parse_tr : forall f, PFF.pf_parse f = option_map (map pp_tr) (PFC.pf_parse f).
Proof.
fix IH 1. intros [|b r]; [reflexivity|].
cbn [PFF.pf_parse PFC.pf_parse].
destruct (b =? 37).
- destruct r as [|c r1]; [reflexivity|].
  destruct (c =? 100); [rewrite (IH r1); destruct (PFC.pf_parse r1); reflexivity|].
  destruct (c =? 99); [rewrite (IH r1); destruct (PFC.pf_parse r1); reflexivity|].
  destruct (c =? 115); [rewrite (IH r1); destruct (PFC.pf_parse r1); reflexivity|].
  destruct (c =? 48).
  + destruct r1 as [|c2 [|c3 r3]]; [reflexivity | reflexivity|].
    destruct ((c2 =? 52) && (c3 =? 120)); [rewrite (IH r3); destruct (PFC.pf_parse r3); reflexivity|].
    destruct ((c2 =? 50) && (c3 =? 120)); [rewrite (IH r3); destruct (PFC.pf_parse r3); reflexivity | reflexivity].
  + destruct (c =? 108).
    * destruct r1 as [|c2 [|c3 r3]]; [reflexivity | reflexivity|].
      destruct ((c2 =? 108) && (c3 =? 117)); [rewrite (IH r3); destruct (PFC.pf_parse r3); reflexivity | reflexivity].
    * destruct (c =? 46); [|reflexivity].
      destruct r1 as [|c2 [|c3 r3]]; [reflexivity | reflexivity|].
      destruct ((c2 =? 42) && (c3 =? 115)); [rewrite (IH r3); destruct (PFC.pf_parse r3); reflexivity | reflexivity].
- destruct ((0 <? b) && (b <? 256)); [rewrite (IH r); destruct (PFC.pf_parse r); reflexivity | reflexivity].
Qed.

Lemma pf_text_tr : forall ps args, PFF.pf_text (map pp_tr ps) (map pa_tr args) = PFC.pf_text ps args.
Proof.
induction ps as [|p ps IH]; intros args.
- destruct args; reflexivity.
- destruct p.
  + cbn [map pp_tr PFF.pf_text PFC.pf_text]. rewrite IH. reflexivity.
  + destruct args as [|[v|u|s] args]; cbn [map pp_tr pa_tr PFF.pf_text PFC.pf_text]; try reflexivity.
    rewrite IH. reflexivity.
  + destruct args as [|[v|u|s] args]; cbn [map pp_tr pa_tr PFF.pf_text PFC.pf_text]; try reflexivity.
    rewrite IH. reflexivity.
  + destruct args as [|[v|u|s] args]; cbn [map pp_tr pa_tr PFF.pf_text PFC.pf_text]; try reflexivity.
    rewrite IH. reflexivity.
  + destruct args as [|[v|u|s] args]; cbn [map pp_tr pa_tr PFF.pf_text PFC.pf_text]; try reflexivity.
    rewrite IH. reflexivity.
  + destruct args as [|[v|u|s] args]; cbn [map pp_tr pa_tr PFF.pf_text PFC.pf_text]; try reflexivity.
    rewrite IH. reflexivity.
  + destruct args as [|[v|u|s] args]; cbn [map pp_tr pa_tr PFF.pf_text PFC.pf_text]; try reflexivity.
    rewrite IH. reflexivity.
  + destruct args as [|[k|u|s] [|[k2|u2|s2] args]]; cbn [map pp_tr pa_tr PFF.pf_text PFC.pf_text]; try reflexivity.
    rewrite IH. reflexivity.
Qed.

(* a format that parses holds bytes 1..255 only *)
Lemma pf_parse_bytes : forall f ps, PFC.pf_parse f = Some ps -> Forall (fun b => 0 < b < 256) f.
Proof.
fix IH 1. intros [|b r] ps H; [constructor|].
cbn [PFC.pf_parse] in H.
destruct (b =? 37) eqn:E37.
- apply Z.eqb_eq in E37. subst b.
  destruct r as [|c r1]; [discriminate H|].
  constructor; [lia|].
  destruct (c =? 100) eqn:E1;
    [apply Z.eqb_eq in E1; subst c; destruct (PFC.pf_parse r1) as [q|] eqn:Q; [|discriminate H];
     constructor; [lia | exact (IH r1 q Q)]|].
  destruct (c =? 99) eqn:E2;
    [apply Z.eqb_eq in E2; subst c; destruct (PFC.pf_parse r1) as [q|] eqn:Q; [|discriminate H];
     constructor; [lia | exact (IH r1 q Q)]|].
  destruct (c =? 115) eqn:E3;
    [apply Z.eqb_eq in E3; subst c; destruct (PFC.pf_parse r1) as [q|] eqn:Q; [|discriminate H];
     constructor; [lia | exact (IH r1 q Q)]|].
  destruct (c =? 48) eqn:E4.
  + apply Z.eqb_eq in E4. subst c.
    destruct r1 as [|c2 [|c3 r3]]; [discriminate H | discriminate H|].
    destruct ((c2 =? 52) && (c3 =? 120)) eqn:E5.
    * apply andb_prop in E5 as [E5a E5b]. apply Z.eqb_eq in E5a, E5b. subst c2 c3.
      destruct (PFC.pf_parse r3) as [q|] eqn:Q; [|discriminate H].
      constructor; [lia|]. constructor; [lia|]. constructor; [lia | exact (IH r3 q Q)].
    * destruct ((c2 =? 50) && (c3 =? 120)) eqn:E6; [|discriminate H].
      apply andb_prop in E6 as [E6a E6b]. apply Z.eqb_eq in E6a, E6b. subst c2 c3.
      destruct (PFC.pf_parse r3) as [q|] eqn:Q; [|discriminate H].
      constructor; [lia|]. constructor; [lia|]. constructor; [lia | exact (IH r3 q Q)].
  + destruct (c =? 108) eqn:E7.
    * apply Z.eqb_eq in E7. subst c.
      destruct r1 as [|c2 [|c3 r3]]; [discriminate H | discriminate H|].
      destruct ((c2 =? 108) && (c3 =? 117)) eqn:E8; [|discriminate H].
      apply andb_prop in E8 as [E8a E8b]. apply Z.eqb_eq in E8a, E8b. subst c2 c3.
      destruct (PFC.pf_parse r3) as [q|] eqn:Q; [|discriminate H].
      constructor; [lia|]. constructor; [lia|]. constructor; [lia | exact (IH r3 q Q)].
    * destruct (c =? 46) eqn:E9; [|discriminate H].
      apply Z.eqb_eq in E9. subst c.
      destruct r1 as [|c2 [|c3 r3]]; [discriminate H | discriminate H|].
      destruct ((c2 =? 42) && (c3 =? 115)) eqn:E10; [|discriminate H].
      apply andb_prop in E10 as [E10a E10b]. apply Z.eqb_eq in E10a, E10b. subst c2 c3.
      destruct (PFC.pf_parse r3) as [q|] eqn:Q; [|discriminate H].
      constructor; [lia|]. constructor; [lia|]. constructor; [lia | exact (IH r3 q Q)].
- destruct ((0 <? b) && (b <? 256)) eqn:Eb; [|discriminate H].
  apply andb_prop in Eb as [Eb1 Eb2]. apply Z.ltb_lt in Eb1, Eb2.
  destruct (PFC.pf_parse r) as [q|] eqn:Q; [|discriminate H].
  constructor; [lia | exact (IH r q Q)].
Qed.

(* the conversions link's printf calls use (reac_code_emit_c.v apf_link_piece: literal bytes, %d, %s) are
   lib/A/Rt/LinkPfPiece.v pf_link_piece after translation *)
Lemma link_piece_tr : forall ps, Forall apf_link_piece ps -> Forall pf_link_piece (map pp_tr ps).
Proof.
intros ps H. apply Forall_map. eapply Forall_impl; [|exact H]. intros [b| | | | | | |] Hp; cbn in *; tauto.
Qed.

Lemma link_piece_prec : forall ps args, Forall apf_link_piece ps -> pf_prec_pos (map pp_tr ps) args.
Proof.
intros ps args H. apply pf_disco_prec_pos. apply Forall_map. eapply Forall_impl; [|exact H].
intros [b| | | | | | |] Hp; cbn in *; tauto.
Qed.

(* ==========================================================================
   m. The readers SnShared.v's family takes, from link_amem.v's views
   ========================================================================== *)

Lemma lwf_u8 : forall z, 0 <= z < 256 -> bv_unsigned (Z_to_bv 8 z) = z.
Proof.
intros z Hz. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
apply Z.mod_small. exact Hz.
Qed.

(* the end of a string's last 8-byte word, which the interceptors read (SnShared.v str_end) *)
Lemma str_end_bounds : forall (w : Z) (s : list Z),
  w + Z.of_nat (length s) < str_end w s <= w + Z.of_nat (length s) + 8.
Proof.
intros w s. unfold str_end. pose proof (Z.mod_pos_bound (w + Z.of_nat (length s)) 8 ltac:(lia)). lia.
Qed.

Section m.
Variable segs : list Segment.

(* a callee window [spc - Kc, spc) inside the caller's [sp - K, sp), whose bottom is a multiple of 8 *)
Definition win_in (sp K spc Kc : Z) : Prop :=
  sp - K <= spc - Kc /\ spc <= sp /\ (sp - K) mod 8 = 0 /\ 0 <= Kc.

(* the bytes of a C string of numbers, read through ard *)
Lemma ard_cstr : forall (m : word -> option byte) p (l : list Z),
  acstr_at segs m p (map (Z_to_bv 8) l) -> Forall (fun c => 0 <= c < 256) l ->
  forall i, 0 <= i <= Z.of_nat (length l) -> ard segs m (p + i) = Some (nth (Z.to_nat i) (l ++ [0]) 0).
Proof.
intros m p l ((H0 & Hlen & Hb) & _) Hr i Hi.
rewrite length_app, length_map in Hb. cbn [length] in Hb.
assert (Hk : (Z.to_nat i < length l + 1)%nat) by lia.
specialize (Hb (Z.to_nat i) Hk). rewrite Z2Nat.id in Hb by lia.
unfold ard. rewrite Hb.
destruct (Nat.lt_ge_cases (Z.to_nat i) (length l)) as [Hlt | Hge].
- rewrite nth_error_app1 by (rewrite length_map; exact Hlt).
  rewrite nth_error_map. destruct (nth_error l (Z.to_nat i)) as [c|] eqn:Ec;
    [|apply nth_error_None in Ec; lia].
  cbn [option_map]. rewrite app_nth1 by exact Hlt.
  assert (Hc : nth (Z.to_nat i) l 0 = c) by (apply nth_error_nth; exact Ec). rewrite Hc.
  rewrite lwf_u8; [reflexivity|].
  rewrite Forall_forall in Hr. apply Hr. exact (nth_error_In l (Z.to_nat i) Ec).
- assert (Ei : Z.to_nat i = length l) by lia.
  rewrite Ei. rewrite nth_error_app2 by (rewrite length_map; lia). rewrite length_map, Nat.sub_diag.
  cbn [nth_error option_map]. rewrite app_nth2 by lia. rewrite Nat.sub_diag. cbn [nth].
  unfold zb. rewrite lwf_u8 by lia. reflexivity.
Qed.

(* a string that astr_rt_ok places outside the caller's window and that lies apart from the FILE block misses the
   callee's two regions, up to the end of its last word *)
Lemma str_apart_out : forall (regs : bvmap 5 word) K p (l : list Z) n Kc spc f,
  win_in (spZ regs) K spc Kc ->
  apart_frame regs K p (Z.of_nat (length l) + 1) ->
  apart p (Z.of_nat (length l) + 8) f AMF_BLOCK ->
  0 <= n <= str_end p l - p ->
  Forall (zdisjoint (p, n)) (vmf_out Kc spc f).
Proof.
intros regs K p l n Kc spc f (W1 & W2 & W3 & W4) HA HF Hn.
pose proof (str_end_bounds p l) as Hse.
unfold vmf_out. constructor; [|constructor; [|constructor]].
- unfold zdisjoint. cbn [fst snd]. unfold apart_frame in HA.
  destruct HA as [HA | HA]; [left | right; lia].
  (* the string's last word ends at or below the caller's window, a multiple of 8 *)
  unfold str_end in Hn. pose proof (Z.mod_pos_bound (p + Z.of_nat (length l)) 8 ltac:(lia)). lia.
- unfold zdisjoint, apart in *. cbn [fst snd]. lia.
Qed.

(* a %s argument: a C string with astr_rt_ok is SnShared.v's pf_arg_asan at the callee's regions *)
Lemma astr_asan : forall (regs : bvmap 5 word) K (m : word -> option byte) w (s : list Z) Kc spc f,
  win_in (spZ regs) K spc Kc ->
  Forall (fun c => 0 < c < 256) s ->
  acstr_at segs m w (map (Z_to_bv 8) s) ->
  astr_rt_ok segs regs K m w (map (Z_to_bv 8) s) ->
  apart w (Z.of_nat (length s) + 8) f AMF_BLOCK ->
  pf_arg_asan (ard segs m) (vmf_out Kc spc f) w (PFF.APtr s).
Proof.
intros regs K m w s Kc spc f HW Hs Hc (Hp & Hl & Ham & Hra & Hhull & Htail & Hap) HF.
rewrite length_map in Hl, Ham, Hra, Hhull, Htail, Hap.
pose proof (str_end_bounds w s) as Hse.
cbn [pf_arg_asan].
split; [exact Hs|]. split; [exact Hp|]. split; [exact Hl|].
split.
{ intros i Hi. apply (ard_cstr m w s Hc); [|exact Hi].
  eapply Forall_impl; [|exact Hs]. intros c Hc'. cbv beta in Hc'. lia. }
split.
{ intros x Hx. apply Htail. unfold str_end in Hx. exact Hx. }
split; [exact (str_apart_out regs K w s (str_end w s - w) Kc spc f HW Hap HF ltac:(lia))|].
split; [unfold amem_range in *; lia|].
split; [exact Hra | exact Hhull].
Qed.

(* the format: a C string with astr_rt_ok, apart from the FILE block, is SnShared.v's fmt_at *)
Lemma afmt_at : forall (regs : bvmap 5 word) K (m : word -> option byte) fp (fmt : list Z) Kc spc f,
  win_in (spZ regs) K spc Kc ->
  Forall (fun c => 0 < c < 256) fmt ->
  acstr_at segs m fp (map (Z_to_bv 8) fmt) ->
  astr_rt_ok segs regs K m fp (map (Z_to_bv 8) fmt) ->
  apart fp (Z.of_nat (length fmt) + 8) f AMF_BLOCK ->
  fmt_at (ard segs m) (vmf_out Kc spc f) fp fmt.
Proof.
intros regs K m fp fmt Kc spc f HW Hs Hc (Hp & Hl & Ham & Hra & Hhull & Htail & Hap) HF.
rewrite length_map in Hl, Ham, Hra, Hhull, Htail, Hap.
pose proof (str_end_bounds fp fmt) as Hse.
split; [exact Hp|].
split.
{ intros i Hi. apply (ard_cstr m fp fmt Hc); [|exact Hi].
  eapply Forall_impl; [|exact Hs]. intros c Hc'. cbv beta in Hc'. lia. }
split; [exact (str_apart_out regs K fp fmt (Z.of_nat (length fmt) + 1) Kc spc f HW Hap HF ltac:(lia))|].
split; [unfold amem_range in *; lia|].
split; [exact Hra | exact Hhull].
Qed.

(* the vararg registers: reac_code_emit_c.v's apf_args_ok is pf_args_asan over the registers' values *)
Lemma apf_args_asan : forall (regs : bvmap 5 word) K (m : word -> option byte) f (rs : list word) args Kc spc,
  win_in (spZ regs) K spc Kc ->
  apf_args_ok segs regs K m f rs args ->
  pf_args_asan (ard segs m) (vmf_out Kc spc f) (map (fun r : word => bv_unsigned r) rs) (map pa_tr args).
Proof.
intros regs K m f rs args Kc spc HW. revert rs.
induction args as [|a args IH]; intros rs H; [destruct rs; exact I|].
destruct rs as [|r rs]; [destruct H|].
destruct H as (Ha & Hr). cbn [map pf_args_asan]. split; [|exact (IH rs Hr)].
destruct a as [v|u|s]; cbn [pa_tr pf_arg_asan apf_arg_ok] in *.
- exact Ha.
- exact Ha.
- destruct Ha as (Hs & Hc & Hrt & Hap). exact (astr_asan regs K m (bv_unsigned r) s Kc spc f HW Hs Hc Hrt Hap).
Qed.

(* the family: a format of literal / %d / %s pieces, its arguments, its text *)
Lemma pf_family_of_c : forall (rd : reader) rs fp (fmt : list Z) ps args T (ws : list Z),
  fmt_at rd rs fp fmt ->
  PFC.pf_parse fmt = Some ps ->
  Forall apf_link_piece ps ->
  pf_args_asan rd rs ws (map pa_tr args) ->
  PFC.pf_text ps args = Some T ->
  pf_family pf_link_piece rd rs fp ws T.
Proof.
intros rd rs fp fmt ps args T ws Hf Hp Hk Ha Ht.
exists fmt, (map pp_tr ps), (map pa_tr args).
split; [exact Hf|].
split; [rewrite pf_parse_tr, Hp; reflexivity|].
split; [exact (link_piece_tr ps Hk)|].
split; [exact Ha|].
split; [rewrite pf_text_tr; exact Ht|].
exact (link_piece_prec ps (map pa_tr args) Hk).
Qed.

(* the arguments' slack facts (SnFF.v pf_args_slack, RT_pf_sh.v pf_args_amem): each %s string's last word and its
   8-byte band lie in application memory, which astr_rt_ok's amem_range p (|s| + 8) says *)
Lemma apf_args_slack : forall (regs : bvmap 5 word) K (m : word -> option byte) f (rs : list word) args,
  apf_args_ok segs regs K m f rs args ->
  pf_args_slack (map (fun r : word => bv_unsigned r) rs) (map pa_tr args) /\
  RT_pf_sh.pf_args_amem (map (fun r : word => bv_unsigned r) rs) (map pa_tr args).
Proof.
intros regs K m f rs args. revert rs.
induction args as [|a args IH]; intros rs H; [destruct rs; split; exact I|].
destruct rs as [|r rs]; [destruct H|].
destruct H as (Ha & Hr). destruct (IH rs Hr) as [IH1 IH2].
destruct a as [v|u|s]; cbn [map pa_tr pf_args_slack RT_pf_sh.pf_args_amem apf_arg_ok] in *.
- split; [exact IH1 | exact IH2].
- split; [exact IH1 | exact IH2].
- destruct Ha as (_ & _ & (_ & _ & Ham & _) & _). rewrite length_map in Ham.
  pose proof (str_end_bounds (bv_unsigned r) s) as Hse.
  split; [split; [unfold amem_range in *; lia | exact IH1] | split; [exact Ham | exact IH2]].
Qed.

(* link's format family (lib/A/Rt/LinkVfInst.v link_vf_FF = FMsnprintfFmI.FF_fmP pf_link_piece, the family of the
   closed vfprintf / fprintf contracts) from the contracts' vocabulary, through LinkVfInst.v link_ff_intro *)
Lemma link_vf_FF_of_c : forall (rd : reader) rs fp (fmt : list Z) ps args T (ws : list Z),
  fmt_at rd rs fp fmt ->
  PFC.pf_parse fmt = Some ps ->
  Forall apf_link_piece ps ->
  pf_args_asan rd rs ws (map pa_tr args) ->
  PFC.pf_text ps args = Some T ->
  0x10000 <= fp -> fp + Z.of_nat (length fmt) + 1 <= 0xa2658 ->
  pf_args_slack ws (map pa_tr args) -> fmt <> [] -> RT_pf_sh.pf_args_amem ws (map pa_tr args) ->
  link_vf_FF rd rs fp ws T.
Proof.
intros rd rs fp fmt ps args T ws Hf Hp Hk Ha Ht Hlo Hhi Hsl Hne Ham.
apply (link_ff_intro rd rs fp fmt (map pp_tr ps) (map pa_tr args) ws T Hf); try assumption.
- rewrite pf_parse_tr, Hp. reflexivity.
- exact (link_piece_tr ps Hk).
- rewrite pf_text_tr. exact Ht.
Qed.

End m.

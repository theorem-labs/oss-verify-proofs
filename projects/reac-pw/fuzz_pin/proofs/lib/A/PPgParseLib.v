(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/libreac/fuzz_knock/lib/Reusable/YC85.v at 6ebe35ba632
   (aj_stack_malloc_atS; donor licence Apache-2.0 OR MIT) ported to reac-pw/fuzz_pin's kit, with module paths
   changed. *)
(* Modified by Theorem Labs, 2026-10: proofs/libreac/fuzz_grant/lib/A/Prog/CtrlParseLib.v at 6ebe35ba632
   (pz_sh_app, pz_kept_refl / _trans / _step / _run / _frame_byte / _ra, pz_nf, pz_awr_cons, pz_own_sep,
   pz_nf_sep, pz_kept_own; donor licence Apache-2.0) ported from the position-abstract image to image A's
   segments tfibsegs: the side-stack frame of class 1 (128 bytes, 16 shadow bytes) is the class-0 frame of
   reac_box_pin_parse (64 bytes, 8 shadow bytes, the flag pointer at F + 56), the out struct of the caller is
   an abstract set of caller bytes Eo, and the two memories of acall_kept may sit in different worlds. *)
(* Generic lemmas the walk of reac_box_pin_parse (0x80b44, fuzz_pin.asan) uses:
   1. aj_stack_malloc_atS: the call of the side stack for frames (class c), with the state after it a
      set_fs of the state before it, so that the meter does not grow (pp_mo_le_set_fs).
   2. The three wrapper call lemmas in the shape of lib/Reusable/YCbq.v aj_bcmp_at: aj_strcspn_at,
      aj_strncmp_at, aj_strlen_at, and the string premise of the wrappers (awrap_str) from the contract's
      string facts (pp_awrap_of_ro, pp_awrap_of_spec, pp_amem_blk).
   3. The class-0 frame: what a step of the walk keeps of the caller's memory (the pz_kept lemmas), and the
      frame's separation from every heap block, every caller frame and its shadow bytes, and the image
      (pz_nf_sep); the two out-cells of a live call (pp_oc_sep, pp_oc_img); the four memory clauses of
      pin_post_parse from the kept fact (pp_post_mem_of_kept).
   4. The model bridges over lib/Prog/pin_spec.v and lib/A/PPgWrap.v (strcspn of ":" is colon_idx, the
      strlen / strncmp test of a row is the token equality, the row scan, the label, the result).
   The wrappers' texts are lib/A/PPgWrap.v's (astrcspn_realizes, astrncmp_realizes) and lib/A/Rt/StrlenDef.v's
   (astrlen_realizes). *)
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YG0s YI16 YM05 DepotCfg.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require YImgTop.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A Require Import AWalkFw0 ACeh ACem.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A.Rt Require Import WrapRo StrlenDef.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A Require Import PPgBase PPgWrap.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Prog Require Import pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A Require Import PPgCSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ===================================== 4. the model bridges ===================================== *)

(* strcspn(s, ":") on s ++ NUL is the index of the first ':' (lib/A/PPgWrap.v cspn_len, pin_spec colon_idx). *)
Lemma pp_cspn_colon : forall s, cspn_len [Z_to_bv 8 COLON] s = colon_idx s.
Proof.
induction s as [|x s IH]; [reflexivity|]. cbn [cspn_len colon_idx existsb].
rewrite orb_false_r. assert (E : bv_unsigned (Z_to_bv 8 COLON) = COLON) by reflexivity. rewrite E, Z.eqb_sym.
destruct (bv_unsigned x =? COLON); [reflexivity|]. rewrite IH. reflexivity.
Qed.
Lemma pp_cspn_colon_bytes : forall s, cspn_len pin_colon_bytes s = colon_idx s.
Proof. exact pp_cspn_colon. Qed.

(* The byte list of s ++ NUL as the Z values garr8 holds. *)
Lemma pp_zb_lt : forall s j, (j < length s)%nat -> nth j (pin_zbytes s ++ [0]) 0 = bv_unsigned (nth j s pin_spec.NUL).
Proof.
intros s j Hj. unfold pin_zbytes. rewrite app_nth1 by (rewrite length_map; exact Hj).
rewrite (nth_indep _ 0 (bv_unsigned pin_spec.NUL)) by (rewrite length_map; exact Hj).
exact (map_nth (fun b : byte => bv_unsigned b) s pin_spec.NUL j).
Qed.
Lemma pp_zb_ge : forall s j, (length s <= j)%nat -> nth j (pin_zbytes s ++ [0]) 0 = 0.
Proof.
intros s j Hj. unfold pin_zbytes. rewrite app_nth2 by (rewrite length_map; exact Hj).
destruct (j - length (map (fun b : byte => bv_unsigned b) s))%nat as [|[|n]]; reflexivity.
Qed.
Lemma pp_byte0 : forall b : byte, bv_unsigned b = 0 -> b = pin_spec.NUL.
Proof. intros b H. apply bv_eq. rewrite H. reflexivity. Qed.
Lemma pp_zb_nz : forall s j, ~ In pin_spec.NUL s -> (j < length s)%nat -> nth j (pin_zbytes s ++ [0]) 0 <> 0.
Proof.
intros s j Hs Hj. rewrite (pp_zb_lt s j Hj). intros H0. apply Hs.
rewrite <- (pp_byte0 _ H0). apply nth_In. exact Hj.
Qed.

(* strncmp_walk over two lists that hold no NUL before position k: 0 exactly when the first k + 1 bytes agree. *)
Lemma pp_walk : forall k (l r : list byte), (S k <= length l)%nat -> (S k <= length r)%nat ->
(forall j, (j < k)%nat -> bv_unsigned (nth j l (Z_to_bv 8 0)) <> 0) ->
(forall j, (j < k)%nat -> bv_unsigned (nth j r (Z_to_bv 8 0)) <> 0) ->
exists d, strncmp_walk l r k = Some d /\ (d = 0 <-> firstn (S k) l = firstn (S k) r).
Proof.
induction k as [|k IH]; intros [|a l] [|b r] Hl Hr Hnl Hnr; cbn [length] in Hl, Hr; try lia.
- cbn [strncmp_walk Nat.eqb]. rewrite orb_true_r. cbn [orb].
  exists (bv_unsigned a - bv_unsigned b). split; [reflexivity|]. cbn [firstn]. split; intros H.
  + f_equal. apply bv_eq. lia.
  + injection H as H. rewrite H. lia.
- assert (Ha0 : bv_unsigned a <> 0) by exact (Hnl 0%nat ltac:(lia)).
  assert (Hb0 : bv_unsigned b <> 0) by exact (Hnr 0%nat ltac:(lia)).
  cbn [strncmp_walk Nat.eqb]. rewrite (proj2 (Z.eqb_neq _ _) Ha0), (proj2 (Z.eqb_neq _ _) Hb0). cbn [orb].
  destruct (bv_unsigned a =? bv_unsigned b) eqn:E; cbn [negb].
  + apply Z.eqb_eq in E. assert (Eab : a = b) by (apply bv_eq; exact E). subst b.
    destruct (IH l r ltac:(lia) ltac:(lia)) as (d & Hd & Hiff).
    * intros j Hj. exact (Hnl (S j) ltac:(lia)).
    * intros j Hj. exact (Hnr (S j) ltac:(lia)).
    * exists d. split; [exact Hd|]. cbn [firstn]. rewrite Hiff. split; [intros ->; reflexivity | intros H; injection H as H; exact H].
  + apply Z.eqb_neq in E. exists (bv_unsigned a - bv_unsigned b). split; [reflexivity|]. split; intros H.
    * exfalso. lia.
    * cbn [firstn] in H. injection H as H _. exfalso. apply E. rewrite H. reflexivity.
Qed.

(* The strncmp test of row i (spec first, token second, n = toklen) when the token's length is toklen:
   0 exactly when the token is the spec's token. *)
Lemma pp_strncmp_tok : forall i (s : list byte) (toklen : nat),
(i < CAT_N)%nat -> ~ In pin_spec.NUL s -> toklen = colon_idx s ->
Z.of_nat (length (tok_bytes i)) = Z.of_nat toklen ->
exists d, strncmp_model (s ++ [Z_to_bv 8 0]) (tok_bytes i ++ [Z_to_bv 8 0]) (Z.of_nat toklen) = Some d /\
(d = 0 <-> tok_bytes i = pin_token s).
Proof.
intros i s toklen Hi Hs -> Hlen. apply Nat2Z.inj in Hlen.
pose proof (tokens_nonempty i Hi) as Hne. pose proof (colon_idx_le s) as Hle.
unfold pin_token. remember (colon_idx s) as c eqn:Ec. destruct c as [|k]; [lia|].
unfold strncmp_model. replace (Z.of_nat (S k) =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
replace (Z.to_nat (Z.of_nat (S k) - 1)) with k by lia.
destruct (pp_walk k (s ++ [Z_to_bv 8 0]) (tok_bytes i ++ [Z_to_bv 8 0])) as (d & Hd & Hiff).
- rewrite length_app. cbn [length]. lia.
- rewrite length_app. cbn [length]. lia.
- intros j Hj. rewrite app_nth1 by lia. intros H0. apply Hs. rewrite <- (pp_byte0 _ H0). apply nth_In. lia.
- intros j Hj. rewrite app_nth1 by lia. apply (tokens_no_nul i _ Hi). apply nth_In. lia.
- exists d. split; [exact Hd|]. rewrite Hiff.
  rewrite (firstn_app (S k) s), (firstn_app (S k) (tok_bytes i)).
  replace (S k - length s)%nat with 0%nat by lia. replace (S k - length (tok_bytes i))%nat with 0%nat by lia.
  cbn [firstn]. rewrite !app_nil_r.
  assert (Et : firstn (S k) (tok_bytes i) = tok_bytes i) by (apply firstn_all2; lia). rewrite Et.
  split; intros H; symmetry; exact H.
Qed.
(* When the token's length is not toklen, the row is not the spec's token. *)
Lemma pp_strlen_ne : forall i (s : list byte) (toklen : nat), toklen = colon_idx s ->
Z.of_nat (length (tok_bytes i)) <> Z.of_nat toklen -> tok_bytes i <> pin_token s.
Proof.
intros i s toklen -> Hne E. apply Hne. rewrite E. unfold pin_token. rewrite length_firstn.
pose proof (colon_idx_le s). f_equal. lia.
Qed.

(* The row scan (pin_spec row_of). *)
Lemma pp_row_none : forall s, (forall j, (j < CAT_N)%nat -> tok_bytes j <> pin_token s) -> pin_row s = None.
Proof.
intros s H. unfold pin_row. destruct (row_of (pin_token s)) as [i|] eqn:E; [|reflexivity].
destruct (row_of_some _ _ E) as (Hi & Ht & _). exfalso. exact (H i Hi Ht).
Qed.
Lemma pp_row_some : forall s i, (i < CAT_N)%nat -> tok_bytes i = pin_token s -> pin_row s = Some i.
Proof. intros s i Hi Ht. unfold pin_row. rewrite <- Ht. exact (row_of_token i Hi). Qed.
Lemma pp_row_step : forall s i, (forall j, (j < i)%nat -> tok_bytes j <> pin_token s) -> tok_bytes i <> pin_token s ->
forall j, (j < S i)%nat -> tok_bytes j <> pin_token s.
Proof. intros s i H Hi j Hj. destruct (Nat.eq_dec j i) as [->|Hne]; [exact Hi | apply H; lia]. Qed.

(* The label: with toklen = colon_idx s, b the byte of s ++ NUL at toklen and b' the byte at toklen + 1. *)
Lemma pp_label_eq : forall s (toklen : nat), ~ In pin_spec.NUL s -> toklen = colon_idx s ->
pin_label_off s =
if (nth toklen (pin_zbytes s ++ [0]) 0 =? COLON) && negb (nth (S toklen) (pin_zbytes s ++ [0]) 0 =? 0)
then Some (S toklen) else None.
Proof.
intros s toklen Hs ->. unfold pin_label_off. pose proof (colon_idx_le s) as Hle.
destruct (Nat.lt_ge_cases (colon_idx s) (length s)) as [Hlt|Hge].
- destruct (colon_idx_at s Hlt) as (b & Hb & Hbc).
  assert (Eb : nth (colon_idx s) s pin_spec.NUL = b) by (apply nth_error_nth; exact Hb).
  rewrite (pp_zb_lt s _ Hlt), Eb, Hbc, Z.eqb_refl. cbn [andb].
  destruct (Nat.lt_ge_cases (S (colon_idx s)) (length s)) as [H2|H2].
  + rewrite (proj2 (Nat.ltb_lt _ _) H2). rewrite (proj2 (Z.eqb_neq _ _) (pp_zb_nz s _ Hs H2)). reflexivity.
  + rewrite (proj2 (Nat.ltb_ge _ _) H2). rewrite (pp_zb_ge s _ H2). reflexivity.
- rewrite (proj2 (Nat.ltb_ge (S (colon_idx s)) (length s)) ltac:(lia)). rewrite (pp_zb_ge s _ Hge). reflexivity.
Qed.
Lemma pp_label_some : forall s (toklen : nat), ~ In pin_spec.NUL s -> toklen = colon_idx s ->
nth toklen (pin_zbytes s ++ [0]) 0 = COLON -> nth (S toklen) (pin_zbytes s ++ [0]) 0 <> 0 ->
pin_label_off s = Some (S toklen).
Proof.
intros s toklen Hs Ht Hb Hb'. rewrite (pp_label_eq s toklen Hs Ht), Hb, Z.eqb_refl, (proj2 (Z.eqb_neq _ _) Hb'). reflexivity.
Qed.
Lemma pp_label_none_colon : forall s (toklen : nat), ~ In pin_spec.NUL s -> toklen = colon_idx s ->
nth toklen (pin_zbytes s ++ [0]) 0 <> COLON -> pin_label_off s = None.
Proof.
intros s toklen Hs Ht Hb. rewrite (pp_label_eq s toklen Hs Ht), (proj2 (Z.eqb_neq _ _) Hb). reflexivity.
Qed.
Lemma pp_label_none_end : forall s (toklen : nat), ~ In pin_spec.NUL s -> toklen = colon_idx s ->
nth (S toklen) (pin_zbytes s ++ [0]) 0 = 0 -> pin_label_off s = None.
Proof.
intros s toklen Hs Ht Hb'. rewrite (pp_label_eq s toklen Hs Ht), Hb', Z.eqb_refl. cbn [negb]. rewrite andb_false_r. reflexivity.
Qed.
Lemma pp_label_at_some : forall DP sa s i k, pin_label_off s = Some k -> pin_label_at DP sa s i = sa + Z.of_nat k.
Proof. intros DP sa s i k H. unfold pin_label_at. rewrite H. reflexivity. Qed.
Lemma pp_label_at_none : forall DP sa s i, pin_label_off s = None -> pin_label_at DP sa s i = DP i.
Proof. intros DP sa s i H. unfold pin_label_at. rewrite H. reflexivity. Qed.

(* The result. *)
Lemma pp_live_iff : forall sa mo lb, pin_parse_live sa mo lb = true <-> sa <> 0 /\ mo <> 0 /\ lb <> 0.
Proof. intros sa mo lb. unfold pin_parse_live. rewrite !andb_true_iff, !negb_true_iff, !Z.eqb_neq. tauto. Qed.
Lemma pp_res_live : forall cat DP sa mo lb s i, pin_parse_live sa mo lb = true -> pin_row s = Some i ->
pin_parse_res cat DP sa mo lb s = Some (row_addr cat i, pin_label_at DP sa s i).
Proof. intros cat DP sa mo lb s i Hl Hr. unfold pin_parse_res. rewrite Hl, Hr. reflexivity. Qed.
Lemma pp_res_norow : forall cat DP sa mo lb s, pin_row s = None -> pin_parse_res cat DP sa mo lb s = None.
Proof. intros cat DP sa mo lb s Hr. unfold pin_parse_res. rewrite Hr. destruct (pin_parse_live sa mo lb); reflexivity. Qed.
Lemma pp_res_dead : forall cat DP sa mo lb s, pin_parse_live sa mo lb = false -> pin_parse_res cat DP sa mo lb s = None.
Proof. intros cat DP sa mo lb s Hl. unfold pin_parse_res. rewrite Hl. reflexivity. Qed.
Lemma pp_res_sa0 : forall cat DP mo lb s, pin_parse_res cat DP 0 mo lb s = None.
Proof. intros. apply pp_res_dead. reflexivity. Qed.
Lemma pp_res_mo0 : forall cat DP sa lb s, pin_parse_res cat DP sa 0 lb s = None.
Proof. intros. apply pp_res_dead. unfold pin_parse_live. destruct (sa =? 0), (lb =? 0); reflexivity. Qed.
Lemma pp_res_lb0 : forall cat DP sa mo s, pin_parse_res cat DP sa mo 0 s = None.
Proof. intros. apply pp_res_dead. unfold pin_parse_live. destruct (sa =? 0), (mo =? 0); reflexivity. Qed.
Lemma pp_res_nil : forall cat DP sa mo lb, pin_parse_res cat DP sa mo lb [] = None.
Proof. intros. apply pp_res_norow. exact pin_row_nil. Qed.
Lemma pp_rc_some : forall p, parse_rc (Some p) = 0.
Proof. intros. reflexivity. Qed.
Lemma pp_rc_none : parse_rc None = -1.
Proof. reflexivity. Qed.
Lemma pp_w64_m1 : w64 (-1) = Z_to_bv 64 18446744073709551615.
Proof. unfold w64. apply bv_eq. rewrite !Z_to_bv_unsigned. reflexivity. Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
(* A byte of a garr8 list, read through aview. *)
Lemma pp_aview_garr8 : forall segs H (mem : word -> option byte) x L j,
garr8 segs (mrestrict H mem) x L -> (j < length L)%nat -> aview segs H mem (x + Z.of_nat j) = Some (nth j L 0).
Proof.
intros segs H mem x L j HG Hj. unfold aview. rewrite (garr8_mbyte segs _ x L j HG Hj). cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. apply bv_wrap_small. destruct (HG j Hj) as [_ Hr]. unfold bv_modulus. cbn [Z.of_N]. lia.
Qed.

(* The two out-cells of the call, when it is live, lie in caller frames of the entry state. *)
Definition pp_oc_frames (lyc : alayout) (Sc : astate) (live : bool) (mo lb cidm posm cidl posl : Z) : Prop :=
live = true ->
In (cidm, posm) (frames Sc) /\ frame_addr lyc cidm posm <= mo /\ mo + 8 <= frame_addr lyc cidm posm + fs_frame_bytes cidm /\
In (cidl, posl) (frames Sc) /\ frame_addr lyc cidl posl <= lb /\ lb + 8 <= frame_addr lyc cidl posl + fs_frame_bytes cidl.

(* The bytes of reac_box_pin_parse's own side-stack frame (class 0: 64 bytes at F), its 8 shadow bytes and
   its flag byte FL. *)
Definition pp_nf (F FL a : Z) : Prop :=
(F <= a < F + 64) \/ (SHADOW_OFF + F / 8 <= a < SHADOW_OFF + F / 8 + 8) \/ a = FL.

(* A shadow byte of an address below 2^47 is never an application byte. *)
Lemma pz_sh_app : forall x p n, 0 <= x < 2 ^ 47 -> in_app p n -> ~ (p <= shadow_addr x < p + n).
Proof.
intros x p n Hx [H0 [H|[H1 H2]]] Hs; unfold shadow_addr, SHADOW_OFF in Hs;
pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia));
assert (x / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia); unfold kLowShadowBeg, kHighMemBeg in *; lia.
Qed.
Lemma pz_awr_cons : forall STK sp0 FP bl0 blc ly own x a,
awr_byte STK sp0 FP bl0 blc ly own a -> awr_byte STK sp0 FP bl0 blc ly (x :: own) a.
Proof.
intros STK sp0 FP bl0 blc ly own x a [H|[H|[H|(cid & pos & Hin & Hr)]]];
[left; exact H | right; left; exact H | right; right; left; exact H |].
right; right; right. exists cid, pos. split; [right; exact Hin | exact Hr].
Qed.
Lemma pp_mo_le_set_fs : forall MT Sc S2, ameter_laws MT -> ameter_fs_laws MT -> (exists f, S2 = set_fs f Sc) ->
mo_le MT Sc S2 0.
Proof. intros MT Sc S2 HL HF (f & ->). apply (mo_le_set_fs_r MT HF). apply (mo_le_refl MT HL). Qed.

Section h.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Hypothesis errno_low : api_env segs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis stack_malloc_progress : stack_malloc_progressP B.
Local Notation code := (as_code B).

(* ============================== 1. the side stack for frames ============================== *)
(* knock's lib/Reusable/YC85.v:352-414 (aj_stack_malloc_atS), with pin's module paths: YCbq.v
   aj_stack_malloc_at plus the callee's own journal and `exists f, S2 = set_fs f Sc` from stack_malloc_post. *)
Lemma aj_stack_malloc_atS : forall cid, astack_malloc_realizes segs B cid -> 0 <= cid <= 10 ->
forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k (o : Z) raw,
ajournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw ->
count_cid cid (frames Sc) < fs_frames cid ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 (pc_stack_malloc code cid)) memT (seg_rom segs)) mdc)
(fun W2 c2 => W2 = W /\ exists S2 regs2 mem2 md2 pos,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal segs B STK sp0 FP ly S W0 mem md ((cid, pos) :: own) lyc S2 W mem2 md2 k /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 (frame_addr lyc cid pos) /\
ablocks B lyc S2 = ablocks B lyc Sc /\ frames S2 = (cid, pos) :: frames Sc /\ ~ In (cid, pos) (frames Sc) /\
st_nev S2 = st_nev Sc /\ blocks_bytes S2 = blocks_bytes Sc /\
zero_shadow (aview segs (w_H W) mem2) SHADOW_OFF (frame_addr lyc cid pos) (fs_frame_bytes cid) /\
rdword (aview segs (w_H W) mem2) (frame_addr lyc cid pos + fs_frame_bytes cid - 8) = Some (flag_addr lyc cid pos) /\
acall_kept segs B lyc Sc W memT W mem2 (sp0 + o - ESTACK) (sp0 + o) (fun _ => False) /\
ajournal segs B ESTACK (sp0 + o) [] lyc Sc W memT mdc [(cid, pos)] lyc S2 W mem2 md2 0 /\
(exists f, S2 = set_fs f Sc)).
Proof.
intros cid ASM Hcid W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k o raw
HJ Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hcnt.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres & Hstatic & F5 & HQT).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof (proj1 errno_low) as [He0 He1].
assert (ASTACK = 16384) as Has by reflexivity. assert (ESTACK = 4096) as Hes by reflexivity.
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
assert (HstkC : astk_ok ESTACK lyc (spZ regsT)).
{ unfold astk_ok, ly_bot in *. rewrite Hsp', Eslo, Eshi, Etop. repeat split; try zlia.
all: rewrite Z.add_mod, Hal16, Hal by zlia; reflexivity. }
assert (HPRE : ecall_pre segs B lyc Sc W regsT memT mdc).
{ split; [exact HAR|]. split; [rewrite Hra; exact Hraw|]. split; [destruct HstkC as (Q1 & _); exact Q1|].
split; [rewrite Eslo, Hsp'; zlia|]. split; [rewrite Eshi, Hsp'; zlia|].
split; [intros a Ha; apply Hpres; rewrite Hsp' in Ha; zlia|]. split; [exact Hgp | exact Htp]. }
pose proof (am_wf _ _ _ _ (proj1 HAR)) as HWF.
destruct (stack_malloc_progress Sc cid HWF Hcid Hcnt) as (pos & S2 & Hpath).
pose proof (ml_stack_malloc _ ML Sc cid HWF Hcid) as HTOK.
destruct (atok_apath _ _ _ [] (PFake cid pos, S2) HTOK Hpath) as (ns' & HQ). unfold stack_malloc_post in HQ.
destruct HQ as (HWF2 & (f & ES2) & _ & Hpos & Hfrs2 & Hfresh).
eapply SRr_mono; [exact (ASM lyc Sc W regsT memT mdc pos S2 HPRE Hcnt Hpath)|].
cbv beta. intros W2 c2 HwleW (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Hres & Hz & Hflag & Hfpres & Hfr & Hpres2).
assert (Hblk : blocks S2 = blocks Sc) by (rewrite ES2; reflexivity).
assert (Eab2 : ablocks B lyc S2 = ablocks B lyc Sc) by (unfold ablocks; rewrite Hblk; reflexivity).
assert (Hnev2 : st_nev S2 = st_nev Sc) by (rewrite ES2; reflexivity).
assert (Hbb : blocks_bytes S2 = blocks_bytes Sc) by (rewrite ES2; reflexivity).
assert (Hsecs2 : st_secs S2 = st_secs Sc) by (rewrite ES2; reflexivity).
assert (HJ1 : ajournal segs B ESTACK (spZ regsT) [] lyc Sc W memT mdc [(cid, pos)] lyc S2 W mem2 md2 0).
{ eapply (call_effect_journal segs B LAWS segs_low errno_low ESTACK lyc Sc W regsT memT mdc lyc S2 W mem2 md2 (fun _ => False) [] [(cid, pos)] 0);
[exact HAR2 | apply layout_le_refl | apply wle_refl | apply same_io_materialized; exact Hsame | | exact Hpres2 | exact HAR | exact HstkC
| cbn; exact Hfrs2 | zlia | zlia | rewrite Hsecs2; zlia | intros a [] | | ].
- intros a H0 H1 H2 H3 _. apply (Hfr a H0 H1 H2). intros H. apply H3. left. exact H.
- intros p n i Hp Hnp. exfalso. apply Hnp. rewrite Eab2. exact Hp.
- rewrite ES2. apply (qtight_ext Sc); [reflexivity | reflexivity | reflexivity | exact HQT]. }
split; [reflexivity|]. exists S2, regs2, mem2, md2, pos.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ rewrite Hsp' in HJ1. replace k with (k + 0) by zlia. change ((cid, pos) :: own) with ([(cid, pos)] ++ own).
eapply (ajournal_sub segs B LAWS segs_low); [exact HJ | exact HJ1 | zlia | zlia | intros a (rg & [] & _)]. }
split; [exact HP|]. split; [exact Hres|]. split; [exact Eab2|]. split; [exact Hfrs2|]. split; [exact Hfresh|].
split; [exact Hnev2|]. split; [exact Hbb|]. split; [exact Hz|]. split; [exact Hflag|].
rewrite Hsp' in HJ1. split; [| split; [exact HJ1 | exists f; exact ES2]].
eapply (acall_kept_of_journal segs B segs_low); [exact HJ1 | exact HAR | intros a (rg & [] & _) | | exact sink_closed_nil].
intros b m i Hb Hi _. rewrite Eab2. exact Hb.
Qed.

(* ============================== 2. the three wrappers ============================== *)
(* The shape of lib/Reusable/YCbq.v:2262-2310 (aj_bcmp_at). *)
Lemma aj_strcspn_at : forall pc, astrcspn_realizes segs B pc ->
forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x y (str cs : list byte) (o : Z) raw,
ajournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
getr regsT 10 = w64 x -> getr regsT 11 = w64 y ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 2 * ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
awrap_str segs W memT regsT x str -> awrap_str segs W memT regsT y cs -> (length cs = 1)%nat ->
aro_unowned segs B (aview segs (w_H W) memT) ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\ same_io mdc md2 /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 (Z.of_nat (cspn_len cs str)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o) -> aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
(forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof.
intros pc AM W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x y str cs o raw
HJ Ha0 Ha1 Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hsx Hsy Hlen Hro.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & _ & _ & _ & _ & _ & Hpres & Hstatic & F5 & HQT).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
assert (ESTACK = 4096) as Hes by reflexivity. assert (ASTACK = 16384) as Has by reflexivity.
assert (HPRE : ecall_pre segs B lyc Sc W regsT memT mdc).
{ eapply (ecall_pre_at segs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k regsT o); try eassumption; [zlia|]. rewrite Hra. exact Hraw. }
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
assert (Hlo2 : ly_stk_lo lyc + 2 * ESTACK <= spZ regsT) by (rewrite Eslo, Hsp'; zlia).
assert (Hpres2E : forall a, spZ regsT - 2 * ESTACK <= a < spZ regsT -> apresent (w_H W) memT a) by (intros a Ha; apply Hpres; rewrite Hsp' in Ha; zlia).
eapply SRr_mono.
{ exact (AM lyc Sc W regsT memT mdc x y str cs HPRE Hlo2 Hpres2E Ha0 Ha1 Hsx Hsy Hlen Hro). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Hres & Hfr & Hpres2).
rewrite Hsp' in Hfr.
split; [reflexivity|]. exists regs2, mem2, md2.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ eapply (ajournal_after_write segs B LAWS segs_low STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k mem2 md2
(fun a => sp0 + o - 2 * ESTACK <= a < sp0 + o) Sc own HJ).
- intros a Ha Hna. apply (Hfr a Ha). exact Hna.
- exact Hpres2.
- exact Hsame.
- intros a Ha; left; left; zlia.
- exact HAR2.
- reflexivity. - reflexivity. - zlia. - exact Hfrs. - exact HQT. }
split; [apply same_io_materialized; exact Hsame|].
split; [exact HP|]. split; [exact Hres|]. split; [exact Hfr | exact Hpres2].
Qed.

Lemma aj_strncmp_at : forall pc, astrncmp_realizes segs B pc ->
forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x y n (ls rs : list byte) (d : Z) (o : Z) raw,
ajournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
getr regsT 10 = w64 x -> getr regsT 11 = w64 y -> getr regsT 12 = w64 n -> 0 <= n < 2 ^ 32 ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 2 * ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
awrap_str segs W memT regsT x ls -> awrap_str segs W memT regsT y rs ->
amem_range x (Z.of_nat (length ls) + 8) -> amem_range y (Z.of_nat (length rs) + 8) ->
strncmp_model (ls ++ [Z_to_bv 8 0]) (rs ++ [Z_to_bv 8 0]) n = Some d ->
aro_unowned segs B (aview segs (w_H W) memT) ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\ same_io mdc md2 /\
aregs_preserved regsT regs2 /\ (exists v : word, getr regs2 10 = v /\ (v = w64 0 <-> d = 0)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o) -> aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
(forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof.
intros pc AM W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x y n ls rs d o raw
HJ Ha0 Ha1 Ha2 Hn Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hsx Hsy Hmx Hmy Hcmp Hro.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & _ & _ & _ & _ & _ & Hpres & Hstatic & F5 & HQT).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
assert (ESTACK = 4096) as Hes by reflexivity. assert (ASTACK = 16384) as Has by reflexivity.
assert (HPRE : ecall_pre segs B lyc Sc W regsT memT mdc).
{ eapply (ecall_pre_at segs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k regsT o); try eassumption; [zlia|]. rewrite Hra. exact Hraw. }
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
assert (Hlo2 : ly_stk_lo lyc + 2 * ESTACK <= spZ regsT) by (rewrite Eslo, Hsp'; zlia).
assert (Hpres2E : forall a, spZ regsT - 2 * ESTACK <= a < spZ regsT -> apresent (w_H W) memT a) by (intros a Ha; apply Hpres; rewrite Hsp' in Ha; zlia).
eapply SRr_mono.
{ exact (AM lyc Sc W regsT memT mdc x y n ls rs d HPRE Hlo2 Hpres2E Ha0 Ha1 Ha2 Hn Hsx Hsy Hmx Hmy Hcmp Hro). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Hres & Hfr & Hpres2).
rewrite Hsp' in Hfr.
split; [reflexivity|]. exists regs2, mem2, md2.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ eapply (ajournal_after_write segs B LAWS segs_low STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k mem2 md2
(fun a => sp0 + o - 2 * ESTACK <= a < sp0 + o) Sc own HJ).
- intros a Ha Hna. apply (Hfr a Ha). exact Hna.
- exact Hpres2.
- exact Hsame.
- intros a Ha; left; left; zlia.
- exact HAR2.
- reflexivity. - reflexivity. - zlia. - exact Hfrs. - exact HQT. }
split; [apply same_io_materialized; exact Hsame|].
split; [exact HP|]. split; [exact Hres|]. split; [exact Hfr | exact Hpres2].
Qed.

(* The strlen wrapper on a C string in the shape of the two others (awrap_str): it returns the length. *)
Lemma pp_first_byte_of_awrap : forall W mem regs x (l : list byte),
awrap_str segs W mem regs x l ->
first_byte segs W mem x (Z.of_nat (length l) + 1) 0 (Z.of_nat (length l)).
Proof.
intros W mem regs x l (Hx & Hnul & Hl32 & Hl63 & HG & _).
assert (HL : length (map (fun b : byte => bv_unsigned b) l ++ [0]) = S (length l)) by (rewrite length_app, length_map; cbn [length]; lia).
split; [lia|]. split.
- intros i Hi. replace (x + i) with (x + Z.of_nat (Z.to_nat i)) by lia.
  rewrite (pp_aview_garr8 segs (w_H W) mem x _ (Z.to_nat i) HG) by lia.
  exists (nth (Z.to_nat i) (map (fun b : byte => bv_unsigned b) l ++ [0]) 0). split; [reflexivity|].
  change (map (fun b : byte => bv_unsigned b) l) with (pin_zbytes l). apply pp_zb_nz; [exact Hnul | lia].
- intros _.
  rewrite (pp_aview_garr8 segs (w_H W) mem x _ (length l) HG) by lia.
  change (map (fun b : byte => bv_unsigned b) l) with (pin_zbytes l). rewrite pp_zb_ge by lia. reflexivity.
Qed.

Lemma aj_strlen_at : forall pc, astrlen_realizes segs B pc ->
forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x (l : list byte) (o : Z) raw,
ajournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
getr regsT 10 = w64 x ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 2 * ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
awrap_str segs W memT regsT x l ->
aro_unowned segs B (aview segs (w_H W) memT) ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\ same_io mdc md2 /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 (Z.of_nat (length l)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o) -> aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
(forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof.
intros pc AM W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x l o raw
HJ Ha0 Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hsx Hro.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & _ & _ & _ & _ & _ & Hpres & Hstatic & F5 & HQT).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
assert (ESTACK = 4096) as Hes by reflexivity. assert (ASTACK = 16384) as Has by reflexivity.
assert (HPRE : ecall_pre segs B lyc Sc W regsT memT mdc).
{ eapply (ecall_pre_at segs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k regsT o); try eassumption; [zlia|]. rewrite Hra. exact Hraw. }
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
assert (Hlo2 : ly_stk_lo lyc + 2 * ESTACK <= spZ regsT) by (rewrite Eslo, Hsp'; zlia).
assert (Hpres2E : forall a, spZ regsT - 2 * ESTACK <= a < spZ regsT -> apresent (w_H W) memT a) by (intros a Ha; apply Hpres; rewrite Hsp' in Ha; zlia).
pose proof (pp_first_byte_of_awrap W memT regsT x l Hsx) as HFB.
destruct Hsx as (Hx & Hnul & Hl32 & Hl63 & HG & Hsrc & Hwin & Hamr & Hra_x & Hhull & Htail).
eapply SRr_mono.
{ exact (AM lyc Sc W regsT memT mdc x (Z.of_nat (length l)) HPRE Hlo2 Hpres2E Ha0 Hx ltac:(lia) Hl32 Hl63 HFB Hsrc Hwin Hamr Hra_x Hhull Htail Hro). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Hres & Hfr & Hpres2).
rewrite Hsp' in Hfr.
split; [reflexivity|]. exists regs2, mem2, md2.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ eapply (ajournal_after_write segs B LAWS segs_low STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k mem2 md2
(fun a => sp0 + o - 2 * ESTACK <= a < sp0 + o) Sc own HJ).
- intros a Ha Hna. apply (Hfr a Ha). exact Hna.
- exact Hpres2.
- exact Hsame.
- intros a Ha; left; left; zlia.
- exact HAR2.
- reflexivity. - reflexivity. - zlia. - exact Hfrs. - exact HQT. }
split; [apply same_io_materialized; exact Hsame|].
split; [exact HP|]. split; [exact Hres|]. split; [exact Hfr | exact Hpres2].
Qed.

(* ============================== 3. what a step keeps of the caller's memory ============================== *)
(* grant's CtrlParseLib.v:379-386 (pz_kept_refl). *)
Lemma pz_kept_refl : forall lyc Sc W memc slo shi (Eo : Z -> Prop),
(forall a, slo <= a < shi -> apresent (w_H W) memc a) ->
acall_kept segs B lyc Sc W memc W memc slo shi Eo.
Proof.
intros lyc Sc W memc slo shi Eo Hp. unfold acall_kept.
split; [intros; reflexivity|]. split; [intros; reflexivity|]. split; [intros; reflexivity|]. split; [intros; reflexivity|].
split; [intros a _ _ H; exact H|]. intros a Ha; exact (Hp a Ha).
Qed.
(* grant's CtrlParseLib.v:387-405 (pz_kept_trans), with the two later memories in any worlds. *)
Lemma pz_kept_trans : forall lyc Sc W memc WX memX WY memY slo shi slo' shi' (Eo Eo' : Z -> Prop),
alloc_ceiling <= slo -> shi <= 2 ^ 64 ->
acall_kept segs B lyc Sc W memc WX memX slo shi Eo ->
acall_kept segs B lyc Sc WX memX WY memY slo' shi' Eo' ->
slo <= slo' -> shi' <= shi -> (forall a, Eo' a -> Eo a) ->
acall_kept segs B lyc Sc W memc WY memY slo shi Eo.
Proof.
intros lyc Sc W memc WX memX WY memY slo shi slo' shi' Eo Eo' Hce Hshi (K1 & K2 & K3 & K4 & K5 & K6) (L1 & L2 & L3 & L4 & L5 & L6) Hlo Hhi HE.
split; [|split; [|split; [|split; [|split]]]].
- intros a Ha Hw. rewrite L1 by lia. apply K1; assumption.
- intros b m i Hb Hi Hn. rewrite (L2 b m i Hb Hi) by (intros X; exact (Hn (HE _ X))). apply (K2 b m i Hb Hi Hn).
- intros a Hi Hno He. rewrite L3 by assumption. apply K3; assumption.
- intros cid pos a Hin Hr Hn. rewrite (L4 cid pos a Hin Hr) by (intros X; exact (Hn (HE _ X))). apply (K4 cid pos a Hin Hr Hn).
- intros a Ha Hw Hp. apply L5; [lia | intros [? ?]; apply Hw; lia |]. apply K5; assumption.
- intros a Ha. destruct (Z_lt_ge_dec a slo') as [H1|H1]; [|destruct (Z_lt_ge_dec a shi') as [H2|H2]].
+ apply L5; [lia | intros [? ?]; lia |]. apply K6. lia.
+ apply L6. lia.
+ apply L5; [lia | intros [? ?]; lia |]. apply K6. lia.
Qed.
(* grant's CtrlParseLib.v:406-437 (pz_kept_step). *)
Lemma pz_kept_step : forall lyc Sc W memc mdc WX memX WY memY slo shi (Eo Zs : Z -> Prop),
AR segs B lyc Sc W memc mdc ->
alloc_ceiling <= slo -> shi <= 2 ^ 64 ->
acall_kept segs B lyc Sc W memc WX memX slo shi Eo ->
(forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview segs (w_H WY) memY a = aview segs (w_H WX) memX a) ->
(forall a, alloc_ceiling <= a < 2 ^ 64 -> apresent (w_H WX) memX a -> apresent (w_H WY) memY a) ->
(forall a, Zs a -> alloc_ceiling <= a < 2 ^ 64 -> slo <= a < shi) ->
(forall b m i, In (b, m) (ablocks B lyc Sc) -> 0 <= i < req_size m -> Zs (b + i) -> Eo (b + i)) ->
(forall a, Zs a -> in_img segs a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) -> False) ->
(forall cid pos a, In (cid, pos) (frames Sc) ->
(in_zr a (frame_rng lyc (cid, pos)) \/ in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8)) -> Zs a -> Eo a) ->
acall_kept segs B lyc Sc W memc WY memY slo shi Eo.
Proof.
intros lyc Sc W memc mdc WX memX WY memY slo shi Eo Zs HAR Hcs Hshi (K1 & K2 & K3 & K4 & K5 & K6) Hkp Hgr HZw HZb HZi HZf.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
split; [|split; [|split; [|split; [|split]]]].
- intros a Ha Hw. rewrite Hkp; [apply K1; assumption | lia | intros HZ; exact (Hw (HZw a HZ Ha))].
- intros b m i Hb Hi Hn. destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b m HAR Hb) as (_ & H4096 & Hce & _).
rewrite Hkp; [apply (K2 b m i Hb Hi Hn) | lia | intros HZ; exact (Hn (HZb b m i Hb Hi HZ))].
- intros a Hi Hno He. pose proof (segs_low a Hi) as Hlow. unfold kLowMemEnd in Hlow.
rewrite Hkp; [apply K3; assumption | lia | intros HZ; exact (HZi a HZ Hi Hno He)].
- intros cid pos a Hin Hr Hn. destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (F4096 & Fce & _).
pose proof (fs_frame_bytes_nonneg cid) as Hfs.
assert (Ha : 0 <= a < 2 ^ 64).
{ destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr; [lia|].
pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) Hfs) as Hse.
assert (Hd : (frame_addr lyc cid pos + fs_frame_bytes cid) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
pose proof (Z.div_pos (frame_addr lyc cid pos) 8 ltac:(lia) ltac:(lia)).
unfold shadow_addr, SHADOW_OFF in *. change (2 ^ 47 / 8) with (2 ^ 44) in Hd. lia. }
rewrite Hkp; [apply (K4 cid pos a Hin Hr Hn) | exact Ha | intros HZ; exact (Hn (HZf cid pos a Hin Hr HZ))].
- intros a Ha Hw Hp. apply Hgr; [exact Ha|]. apply K5; assumption.
- intros a Ha. apply Hgr; [lia|]. apply K6. exact Ha.
Qed.
(* grant's CtrlParseLib.v:440-472 (pz_kept_run): one step keeps the caller's memory when every byte it may
   change is in the call's stack window, in the caller's cells Eo, or in the function's own frame NF. *)
Lemma pz_kept_run : forall lyc Sc W memc mdc WX memX WY memY slo shi (Eo NF Zs : Z -> Prop),
AR segs B lyc Sc W memc mdc ->
alloc_ceiling <= slo -> shi <= 2 ^ 64 ->
(forall a, Eo a -> a < alloc_ceiling) -> (forall a, Eo a -> in_img segs a -> False) ->
(forall b m i, In (b, m) (ablocks B lyc Sc) -> 0 <= i < req_size m -> NF (b + i) -> False) ->
(forall a, NF a -> in_img segs a -> False) ->
(forall cid pos a, In (cid, pos) (frames Sc) ->
(in_zr a (frame_rng lyc (cid, pos)) \/ in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8)) -> NF a -> False) ->
(forall a, NF a -> a < alloc_ceiling) ->
(forall a, Zs a -> (slo <= a < shi) \/ Eo a \/ NF a) ->
acall_kept segs B lyc Sc W memc WX memX slo shi Eo ->
(forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview segs (w_H WY) memY a = aview segs (w_H WX) memX a) ->
(forall a, alloc_ceiling <= a < 2 ^ 64 -> apresent (w_H WX) memX a -> apresent (w_H WY) memY a) ->
acall_kept segs B lyc Sc W memc WY memY slo shi Eo.
Proof.
intros lyc Sc W memc mdc WX memX WY memY slo shi Eo NF Zs HAR Hce Hshi HEc HEi HNb HNi HNf HNc HZ KP Hkp Hgr.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
apply (pz_kept_step lyc Sc W memc mdc WX memX WY memY slo shi Eo Zs HAR Hce Hshi KP Hkp Hgr).
- intros a Ha Hc. destruct (HZ a Ha) as [Hw | [Ho | Hn]]; [exact Hw | pose proof (HEc a Ho); lia | pose proof (HNc a Hn); lia].
- intros b m i Hb Hi Ha. destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b m HAR Hb) as (_ & H4096 & Hbc & _).
destruct (HZ _ Ha) as [Hw | [Ho | Hn]]; [lia | exact Ho | exfalso; exact (HNb b m i Hb Hi Hn)].
- intros a Ha Hi _ _. pose proof (segs_low a Hi) as Hlow. unfold kLowMemEnd in Hlow.
destruct (HZ a Ha) as [Hw | [Ho | Hn]]; [lia | exact (HEi a Ho Hi) | exact (HNi a Hn Hi)].
- intros cid pos a Hin Hr Ha. destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (G4096 & Gce & _).
pose proof (fs_frame_bytes_nonneg cid) as Hfs.
destruct (HZ a Ha) as [Hw | [Ho | Hn]]; [|exact Ho | exfalso; exact (HNf cid pos a Hin Hr Hn)].
exfalso. destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr; [lia|].
pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) Hfs) as Hse.
assert (Hd : (frame_addr lyc cid pos + fs_frame_bytes cid) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
unfold shadow_addr, SHADOW_OFF in *. change (2 ^ 47 / 8) with (2 ^ 44) in Hd. lia.
Qed.
(* grant's CtrlParseLib.v:474-481 (pz_kept_frame_byte). *)
Lemma pz_kept_frame_byte : forall lyc Sc W memc WX memX slo shi (Eo : Z -> Prop) cid pos a,
acall_kept segs B lyc Sc W memc WX memX slo shi Eo -> In (cid, pos) (frames Sc) ->
frame_addr lyc cid pos <= a < frame_addr lyc cid pos + fs_frame_bytes cid -> ~ Eo a ->
aview segs (w_H WX) memX a = aview segs (w_H W) memc a.
Proof.
intros lyc Sc W memc WX memX slo shi Eo cid pos a (_ & _ & _ & K4 & _) Hin Ha Hn.
apply (K4 cid pos a Hin); [left; unfold in_zr, frame_rng; cbn [fst snd]; lia | exact Hn].
Qed.
(* grant's CtrlParseLib.v:482-506 (pz_kept_ra): the shadow of caller frame bytes outside Eo stays. *)
Lemma pz_kept_ra : forall lyc Sc W memc mdc WX memX slo shi (Eo : Z -> Prop) cid pos a n,
AR segs B lyc Sc W memc mdc ->
acall_kept segs B lyc Sc W memc WX memX slo shi Eo -> In (cid, pos) (frames Sc) ->
frame_addr lyc cid pos <= a -> a + n <= frame_addr lyc cid pos + fs_frame_bytes cid ->
(forall x, a <= x < a + n -> ~ Eo (shadow_addr x)) ->
range_addressable (aview segs (w_H W) memc) SHADOW_OFF a n ->
range_addressable (aview segs (w_H WX) memX) SHADOW_OFF a n.
Proof.
intros lyc Sc W memc mdc WX memX slo shi Eo cid pos a n HAR (_ & _ & _ & K4 & _) Hin Hlo Hhi Hn HRA x Hx.
destruct (HRA x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
destruct (al_frames _ _ LAWS lyc Sc W memc mdc cid pos HAR Hin) as (Hal & _ & _ & _).
destruct (frame_al64 segs B lyc Sc W memc mdc cid pos HAR Hin) as (_ & Hfs64 & Hfs).
set (F := frame_addr lyc cid pos) in *.
assert (HR : in_zr (shadow_of_addr SHADOW_OFF x) (shadow_addr F, fs_frame_bytes cid / 8)).
{ unfold in_zr, shadow_of_addr, shadow_addr. cbn [fst snd].
pose proof (Z.div_mod F 8 ltac:(lia)) as DF. pose proof (Z.div_mod (fs_frame_bytes cid) 8 ltac:(lia)) as DS.
assert (HF8 : F mod 8 = 0).
{ pose proof (Z.div_mod F 32 ltac:(lia)) as D32. rewrite Hal, Z.add_0_r in D32. rewrite D32. replace (32 * (F / 32)) with ((4 * (F / 32)) * 8) by lia. apply Z_mod_mult. }
assert (HS8 : fs_frame_bytes cid mod 8 = 0).
{ pose proof (Z.div_mod (fs_frame_bytes cid) 64 ltac:(lia)) as D64. rewrite Hfs64, Z.add_0_r in D64. rewrite D64. replace (64 * (fs_frame_bytes cid / 64)) with ((8 * (fs_frame_bytes cid / 64)) * 8) by lia. apply Z_mod_mult. }
split.
- assert (F / 8 <= x / 8) by (apply Z.div_le_mono; lia). lia.
- assert (x / 8 < F / 8 + fs_frame_bytes cid / 8) by (apply Z.div_lt_upper_bound; lia). lia. }
rewrite <- Hs. apply (K4 cid pos _ Hin (or_intror HR)). unfold shadow_of_addr. change (SHADOW_OFF + x / 8) with (shadow_addr x). apply Hn. exact Hx.
Qed.
(* grant's CtrlParseLib.v:518-525 (pz_own_sep). *)
Lemma pz_own_sep : forall ly S W mem md c p Sc c' p',
AR segs B ly S W mem md -> frames S = (c, p) :: frames Sc -> In (c', p') (frames Sc) ->
zdisjoint (frame_rng ly (c, p)) (frame_rng ly (c', p')).
Proof.
intros ly S W mem md c p Sc c' p' HAR Hfr Hin.
destruct (in_split _ _ Hin) as (l2 & l3 & E). rewrite E in Hfr.
exact (sep_frames_pos segs B LAWS ly S W mem md (c, p) (c', p') [] l2 l3 HAR Hfr).
Qed.

(* The read-only premise of a wrapper call, carried along the kept fact's image clause. *)
Lemma pp_aro_kept : forall lyc Sc W memc WX memX slo shi (Eo : Z -> Prop),
aro_unowned segs B (aview segs (w_H W) memc) ->
acall_kept segs B lyc Sc W memc WX memX slo shi Eo ->
aro_unowned segs B (aview segs (w_H WX) memX).
Proof.
intros lyc Sc W memc WX memX slo shi Eo HR (_ & _ & K3 & _).
apply (aro_unowned_keep segs B _ _ HR). intros a (sg & Hin & _ & Hr) Ho He.
apply K3; [exists sg; split; [exact Hin | exact Hr] | exact Ho | exact He].
Qed.

(* The out-cells of a live call: below the allocation ceiling and apart from every heap block. *)
Lemma pp_oc_sep : forall lyc Sc W memc mdc (live : bool) mo lb cidm posm cidl posl,
AR segs B lyc Sc W memc mdc -> pp_oc_frames lyc Sc live mo lb cidm posm cidl posl ->
(forall a, (live = true /\ pin_out_cell mo lb a) -> a < alloc_ceiling) /\
(forall b m i, In (b, m) (ablocks B lyc Sc) -> 0 <= i < req_size m -> ~ (live = true /\ pin_out_cell mo lb (b + i))).
Proof.
intros lyc Sc W memc mdc live mo lb cidm posm cidl posl HAR HOC. split.
- intros a [Hl Ha]. destruct (HOC Hl) as (Hm & Hm1 & Hm2 & Hb & Hb1 & Hb2).
  destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cidm posm HAR Hm) as (_ & Mce & _).
  destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cidl posl HAR Hb) as (_ & Lce & _).
  unfold pin_out_cell in Ha. lia.
- intros b m i Hin Hi [Hl Ha]. destruct (HOC Hl) as (Hm & Hm1 & Hm2 & Hb & Hb1 & Hb2).
  pose proof (sep_block_frame segs B LAWS lyc Sc W memc mdc b m cidm posm HAR Hin Hm) as Dm.
  pose proof (sep_block_frame segs B LAWS lyc Sc W memc mdc b m cidl posl HAR Hin Hb) as Dl.
  unfold zdisjoint in Dm, Dl. cbn [fst snd] in Dm, Dl. unfold pin_out_cell in Ha. lia.
Qed.

(* The four memory clauses of pin_post_parse (PPgCSpec.v:393-404) from the kept fact whose caller cells
   are the out-cells of a live call. *)
Lemma pp_post_mem_of_kept : forall lyc Sc W memc mdc W2 mem2 slo shi (live : bool) mo lb cidm posm cidl posl,
AR segs B lyc Sc W memc mdc -> pp_oc_frames lyc Sc live mo lb cidm posm cidl posl ->
acall_kept segs B lyc Sc W memc W2 mem2 slo shi (fun a => live = true /\ pin_out_cell mo lb a) ->
(forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (slo <= a < shi) -> ~ pin_out_cell mo lb a ->
 aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a) /\
(forall b m i, In (b, m) (ablocks B lyc Sc) -> 0 <= i < req_size m ->
 aview segs (w_H W2) mem2 (b + i) = aview segs (w_H W) memc (b + i)) /\
(forall c p a, In (c, p) (frames Sc) ->
 (in_zr a (frame_rng lyc (c, p)) \/ in_zr a (shadow_addr (frame_addr lyc c p), fs_frame_bytes c / 8)) ->
 ~ pin_out_cell mo lb a -> aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a) /\
(forall a, in_img segs a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
 aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a).
Proof.
intros lyc Sc W memc mdc W2 mem2 slo shi live mo lb cidm posm cidl posl HAR HOC (K1 & K2 & K3 & K4 & _).
destruct (pp_oc_sep lyc Sc W memc mdc live mo lb cidm posm cidl posl HAR HOC) as (_ & Hb).
split; [|split; [|split]].
- intros a Ha Hw _. exact (K1 a Ha Hw).
- intros b m i Hin Hi. exact (K2 b m i Hin Hi (Hb b m i Hin Hi)).
- intros c p a Hin Hr Hn. apply (K4 c p a Hin Hr). intros [_ H]. exact (Hn H).
- exact K3.
Qed.

(* ======================= the wrappers' string premise ======================= *)
(* The wrappers' string premise from its parts. *)
Lemma pp_awrap_parts : forall W mem regs x (l : list byte),
0 < x -> ~ In (Z_to_bv 8 0) l -> Z.of_nat (length l) + 1 < 2 ^ 32 -> x + Z.of_nat (length l) + 1 <= 2 ^ 63 ->
garr8 segs (mrestrict (w_H W) mem) x (pin_zbytes l ++ [0]) ->
(forall a, x <= a <= x + Z.of_nat (length l) -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs)) ->
amem_range x (Z.of_nat (length l) + 1) ->
range_addressable (aview segs (w_H W) mem) SHADOW_OFF x (Z.of_nat (length l) + 1) ->
shadow_hull_vis (aview segs (w_H W) mem) x (Z.of_nat (length l) + 1) ->
pin_str_tail (aview segs (w_H W) mem) (x + Z.of_nat (length l)) ->
awrap_str segs W mem regs x l.
Proof.
intros W mem regs x l Hx Hnul H32 H63 HG Hwin Hamr HRA HSV HT.
assert (Hes : ESTACK = 4096) by reflexivity.
assert (HL : length (pin_zbytes l ++ [0]) = S (length l)) by (unfold pin_zbytes; rewrite length_app, length_map; cbn [length]; lia).
split; [exact Hx|]. split; [exact Hnul|]. split; [exact H32|]. split; [exact H63|]. split; [exact HG|]. split.
{ intros a Ha. split.
  - replace a with (x + Z.of_nat (Z.to_nat (a - x))) by lia.
    rewrite (pp_aview_garr8 segs (w_H W) mem x _ (Z.to_nat (a - x)) HG) by lia. discriminate.
  - intros Hw. apply (Hwin a); lia. }
split; [exact Hwin|]. split; [exact Hamr|]. split; [exact HRA|]. split; [exact HSV|]. exact HT.
Qed.
(* From a read-only string at the current memory (pin_ro_str, which F-RO-LAW gives at every state). *)
Lemma pp_awrap_of_ro : forall W mem regs x (l : list byte),
pin_ro_str segs (mrestrict (w_H W) mem) (aview segs (w_H W) mem) x l ->
~ In (Z_to_bv 8 0) l ->
(forall a, x <= a <= x + Z.of_nat (length l) -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs)) ->
awrap_str segs W mem regs x l.
Proof.
intros W mem regs x l (Hx & H63 & H32 & Hamr & HG & HRA & HSV & HT) Hnul Hwin.
apply (pp_awrap_parts W mem regs x l Hx Hnul H32 H63 HG Hwin); [| exact HRA | exact HSV | exact HT].
apply (pin_amem_range_le _ _ (Z.of_nat (length l) + 8)); [lia | exact Hamr].
Qed.
(* From the spec string's facts (pin_spec_str) at the current memory, for a call whose 2 * ESTACK window lies
   inside the window those facts name. *)
Lemma pp_awrap_of_spec : forall W mem regs0 STKf regs sa (s : list byte),
pin_spec_str segs (mrestrict (w_H W) mem) (aview segs (w_H W) mem) regs0 STKf sa s ->
spZ regs0 - STKf <= spZ regs - 2 * ESTACK -> spZ regs <= spZ regs0 ->
awrap_str segs W mem regs sa s.
Proof.
intros W mem regs0 STKf regs sa s (Hnul & Hx & H63 & H32 & HG & HRA & HSV & HT & Hamr & Hwin0) H1 H2.
apply (pp_awrap_parts W mem regs sa s Hx Hnul H32 H63 HG); [| exact Hamr | exact HRA | exact HSV | exact HT].
intros a Ha Hw. apply (Hwin0 a Ha). lia.
Qed.
(* A string inside a heap block, with its NUL, has its length + 8 bytes in the application memory range
   (the strncmp wrapper's amem_range premise). *)
Lemma pp_amem_blk : forall ly S W mem md b m x n,
AR segs B ly S W mem md -> In (b, m) (ablocks B ly S) -> b <= x -> x + n + 1 <= b + req_size m ->
amem_range x (n + 8).
Proof.
intros ly S W mem md b m x n HAR Hin Hb Hx.
destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hin) as (_ & H4096 & Hce & Happ & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold amem_range, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ |- *. rewrite C4, C5. lia.
Qed.
End h.

(* ============================== 3. the class-0 frame of image A ============================== *)
Section t.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.

(* Two states journalled from the same start share the side stack's base (layout_le keeps ly_F). *)
Lemma pp_lyF : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
STK' sp0' FP' W0' mem0' md0' own' lyN SN WN memN mdN k',
ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
ajournal tfibsegs B STK' sp0' FP' ly S W0' mem0' md0' own' lyN SN WN memN mdN k' ->
ly_F lyN = ly_F lyc.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k STK' sp0' FP' W0' mem0' md0' own' lyN SN WN memN mdN k'
(_ & (_ & _ & _ & _ & _ & E1 & _) & _) (_ & (_ & _ & _ & _ & _ & E2 & _) & _).
rewrite E1, E2. reflexivity.
Qed.
Lemma pp_frame_addr_lyF : forall lyN lyc c p, ly_F lyN = ly_F lyc ->
frame_addr lyN c p = frame_addr lyc c p /\ flag_addr lyN c p = flag_addr lyc c p.
Proof. intros lyN lyc c p E. unfold frame_addr, flag_addr. rewrite E. split; reflexivity. Qed.

(* The class-0 frame taken by reac_box_pin_parse: its place, its shadow bytes and its flag byte, from the
   allocator relation at any state whose side stack has the same base. *)
Lemma pz_frame0 : forall lyc lyN S2 W2 mem2 md2 fpos,
AR tfibsegs B lyN S2 W2 mem2 md2 -> In (0, fpos) (frames S2) -> ly_F lyN = ly_F lyc -> frame_flag_lawP tfibsegs B ->
frame_addr lyc 0 fpos mod 64 = 0 /\ 4096 <= frame_addr lyc 0 fpos /\ frame_addr lyc 0 fpos + 64 <= alloc_ceiling /\
in_app (frame_addr lyc 0 fpos) 64 /\ off_img (frame_addr lyc 0 fpos) 64 /\
kLowShadowBeg < SHADOW_OFF + frame_addr lyc 0 fpos / 8 /\ SHADOW_OFF + frame_addr lyc 0 fpos / 8 + 8 <= kHighShadowEnd /\
4096 <= flag_addr lyc 0 fpos /\ flag_addr lyc 0 fpos < alloc_ceiling /\ zone2 (flag_addr lyc 0 fpos) 1 /\
app_addr (flag_addr lyc 0 fpos) /\ ~ in_img tfibsegs (flag_addr lyc 0 fpos) /\
~ (frame_addr lyc 0 fpos <= flag_addr lyc 0 fpos < frame_addr lyc 0 fpos + 64).
Proof.
intros lyc lyN S2 W2 mem2 md2 fpos HAR2 Hfin HlyF FFL.
destruct (pp_frame_addr_lyF lyN lyc 0 fpos HlyF) as [EFA EFL].
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (al_frames _ _ LAWS _ _ _ _ _ 0 fpos HAR2 Hfin) as (HFal & HFapp & HFpres & HFSpres).
destruct (frames_bounds tfibsegs B LAWS _ _ _ _ _ 0 fpos HAR2 Hfin) as (HF4096 & HFceil & _).
pose proof (frm_off_img B _ _ _ _ _ 0 fpos HAR2 Hfin) as HFimg.
destruct (FFL _ _ _ _ _ 0 fpos HAR2 Hfin) as (_ & HFLown & (HFLapp & HFLimg) & (HFL4096 & HFLz & HFLce)).
destruct (frame_al64 tfibsegs B _ _ _ _ _ 0 fpos HAR2 Hfin) as (HF64 & _ & _).
rewrite ?EFA in HFapp, HFpres, HF4096, HFceil, HFimg, HF64.
rewrite ?EFL in HFLown, HFLapp, HFLimg, HFL4096, HFLz, HFLce.
change (fs_frame_bytes 0) with 64 in HFapp, HFceil, HFimg, HFpres.
set (F := frame_addr lyc 0 fpos) in *. set (FL := flag_addr lyc 0 fpos) in *.
assert (HFS : SHADOW_OFF + F / 8 + 8 <= kHighShadowEnd /\ kLowShadowBeg < SHADOW_OFF + F / 8).
{ assert (Hd : (F + 8 * 8) / 8 <= 140737479966720 / 8) by (apply Z.div_le_mono; lia).
rewrite Z.div_add in Hd by lia. change (140737479966720 / 8) with 17592184995840 in Hd.
assert (0 <= F / 8) by (apply Z.div_pos; lia).
unfold SHADOW_OFF, kHighShadowEnd, kLowShadowBeg. lia. }
split; [exact HF64|]. split; [exact HF4096|]. split; [exact HFceil|]. split; [exact HFapp|]. split; [exact HFimg|].
split; [exact (proj2 HFS)|]. split; [exact (proj1 HFS)|].
split; [exact HFL4096|]. split; [exact HFLce|]. split; [exact HFLz|]. split; [exact HFLapp|]. split; [exact HFLimg|].
intros Hin. exact (proj2 (HFpres FL Hin) HFLown).
Qed.

(* grant's CtrlParseLib.v:528-593 (pz_nf_sep), class 0, with the allocator relation at the journal's end
   (layout lyN, blocks a permutation of the entry ones): the own frame, its shadow bytes and its flag byte
   are apart from every heap block, the image, every caller frame and its shadow bytes, and lie below the
   allocation ceiling. *)
Lemma pz_nf_sep : forall lyc lyN Sc S2 W mem2 md2 fpos F FL,
AR tfibsegs B lyN S2 W mem2 md2 ->
frames S2 = (0, fpos) :: frames Sc -> Permutation (ablocks B lyN S2) (ablocks B lyc Sc) -> ly_F lyN = ly_F lyc ->
F = frame_addr lyc 0 fpos -> FL = flag_addr lyc 0 fpos ->
frame_flag_lawP tfibsegs B ->
(forall b m i, In (b, m) (ablocks B lyc Sc) -> 0 <= i < req_size m -> pp_nf F FL (b + i) -> False) /\
(forall a, pp_nf F FL a -> in_img tfibsegs a -> False) /\
(forall cid pos a, In (cid, pos) (frames Sc) ->
(in_zr a (frame_rng lyc (cid, pos)) \/ in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8)) -> pp_nf F FL a -> False) /\
(forall a, pp_nf F FL a -> a < alloc_ceiling).
Proof.
intros lyc lyN Sc S2 W mem2 md2 fpos F FL HAR2 Hfrs Hperm HlyF -> -> FFL.
assert (EFA : forall c p, frame_addr lyN c p = frame_addr lyc c p) by (intros c p; exact (proj1 (pp_frame_addr_lyF lyN lyc c p HlyF))).
assert (EFL : forall c p, flag_addr lyN c p = flag_addr lyc c p) by (intros c p; exact (proj2 (pp_frame_addr_lyF lyN lyc c p HlyF))).
assert (Hbin : forall b m, In (b, m) (ablocks B lyc Sc) -> In (b, m) (ablocks B lyN S2))
by (intros b m Hb; exact (Permutation_in _ (Permutation_sym Hperm) Hb)).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hfin : In (0, fpos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ 0 fpos HAR2 Hfin) as (HFal & HFapp & HFpres & HFSpres).
destruct (frames_bounds tfibsegs B LAWS _ _ _ _ _ 0 fpos HAR2 Hfin) as (HF4096 & HFceil & _).
pose proof (frm_off_img B _ _ _ _ _ 0 fpos HAR2 Hfin) as HFimg.
destruct (FFL _ _ _ _ _ 0 fpos HAR2 Hfin) as (_ & HFLown & (HFLapp & HFLimg) & (HFL4096 & _ & HFLce)).
destruct (frame_al64 tfibsegs B _ _ _ _ _ 0 fpos HAR2 Hfin) as (HF64 & _ & _).
rewrite ?EFA in HFapp, HFpres, HF4096, HFceil, HFimg, HF64.
rewrite ?EFL in HFLown, HFLapp, HFLimg, HFL4096, HFLce.
change (fs_frame_bytes 0) with 64 in HFapp, HFceil, HFimg, HFpres.
set (F := frame_addr lyc 0 fpos) in *. set (FL := flag_addr lyc 0 fpos) in *.
unfold in_app, off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp, HFimg.
assert (HFS : SHADOW_OFF + F / 8 + 8 <= kHighShadowEnd /\ kLowShadowBeg < SHADOW_OFF + F / 8).
{ assert (Hd : (F + 8 * 8) / 8 <= 140737479966720 / 8) by (apply Z.div_le_mono; lia).
rewrite Z.div_add in Hd by lia. change (140737479966720 / 8) with 17592184995840 in Hd.
assert (0 <= F / 8) by (apply Z.div_pos; lia).
unfold SHADOW_OFF, kHighShadowEnd, kLowShadowBeg. lia. }
unfold kHighShadowEnd, kLowShadowBeg, SHADOW_OFF in HFS.
split; [|split; [|split]].
- intros b m i Hb Hi Hn. apply Hbin in Hb.
destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR2 Hb) as (_ & Hb4096 & Hbce & Hbapp & Hbown & _).
pose proof (sep_block_frame tfibsegs B LAWS _ _ _ _ _ b m 0 fpos HAR2 Hb Hfin) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite EFA in Hd. change (fs_frame_bytes 0) with 64 in Hd. fold F in Hd.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hbapp.
destruct Hn as [Hn|[Hn|Hn]]; [lia | unfold SHADOW_OFF in Hn; lia |].
exact (proj2 (Hbown (b + i) ltac:(lia)) ltac:(rewrite Hn; exact HFLown)).
- intros a Hn Hi. pose proof (tfib_img_range a Hi) as Hr.
unfold TFIB_IMG_LO, TFIB_IMG_END, YImgTop.IMG_LO, YImgTop.IMG_TOP in Hr.
destruct Hn as [Hn|[Hn|Hn]]; [lia | unfold SHADOW_OFF in Hn; lia | subst a; exact (HFLimg Hi)].
- intros cid pos a Hin Hr Hn.
assert (Hin2 : In (cid, pos) (frames S2)) by (rewrite Hfrs; right; exact Hin).
destruct (al_frames _ _ LAWS _ _ _ _ _ cid pos HAR2 Hin2) as (HGal & HGapp & HGpres & HGSpres).
destruct (frame_al64 tfibsegs B _ _ _ _ _ cid pos HAR2 Hin2) as (HG64 & HGs64 & HGs).
pose proof (pz_own_sep tfibsegs B LAWS _ _ _ _ _ 0 fpos Sc cid pos HAR2 Hfrs Hin) as Hd.
unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd. rewrite !EFA in Hd. change (fs_frame_bytes 0) with 64 in Hd. fold F in Hd.
rewrite ?EFA in HGapp, HGpres, HGSpres, HG64.
set (G := frame_addr lyc cid pos) in *. set (gs := fs_frame_bytes cid) in *.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HGapp.
destruct Hn as [Hn|[Hn|Hn]].
+ destruct Hr as [Hr|Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr; [lia|].
pose proof (shadow_range_end G gs ltac:(lia)) as Hse. unfold shadow_addr in Hse, Hr. fold G in Hr.
assert ((G + gs) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia). assert (0 <= G / 8) by (apply Z.div_pos; lia).
change (2 ^ 47 / 8) with (2 ^ 44) in *. unfold SHADOW_OFF in Hr, Hse. lia.
+ destruct Hr as [Hr|Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr; [unfold SHADOW_OFF in Hn; lia|].
unfold shadow_addr in Hr. fold G in Hr.
pose proof (Z.div_mod F 64 ltac:(lia)) as DF. pose proof (Z.div_mod G 64 ltac:(lia)) as DG.
pose proof (Z.div_mod gs 64 ltac:(lia)) as DS. rewrite HF64, Z.add_0_r in DF. rewrite HG64, Z.add_0_r in DG. rewrite HGs64, Z.add_0_r in DS.
assert (EF : F / 8 = 8 * (F / 64)) by (rewrite DF at 1; replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by lia; apply Z.div_mul; lia).
assert (EG : G / 8 = 8 * (G / 64)) by (rewrite DG at 1; replace (64 * (G / 64)) with ((8 * (G / 64)) * 8) by lia; apply Z.div_mul; lia).
assert (ES : gs / 8 = 8 * (gs / 64)) by (rewrite DS at 1; replace (64 * (gs / 64)) with ((8 * (gs / 64)) * 8) by lia; apply Z.div_mul; lia).
unfold SHADOW_OFF in Hn, Hr. lia.
+ subst a. destruct Hr as [Hr|Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr.
* exact (proj2 (HGpres FL ltac:(fold G gs; lia)) HFLown).
* unfold shadow_addr in Hr. fold G in Hr.
exact (proj2 (HGSpres (FL - shadow_addr G) ltac:(unfold shadow_addr; fold G; lia))
ltac:(replace (shadow_addr G + (FL - shadow_addr G)) with FL by lia; exact HFLown)).
- intros a [Hn|[Hn|Hn]]; [lia | unfold SHADOW_OFF in Hn; lia | lia].
Qed.

(* grant's CtrlParseLib.v:596-611 (pz_kept_own), class 0: one step keeps the caller's memory when each byte
   it may change is in the call's stack window, in the caller cells Eo, or in the own frame. *)
Lemma pz_kept_own : forall lyc lyN Sc S2 W memc mdc W2 mem2 md2 WX memX WY memY slo shi fpos F FL (Eo Zs : Z -> Prop),
AR tfibsegs B lyc Sc W memc mdc -> AR tfibsegs B lyN S2 W2 mem2 md2 ->
frames S2 = (0, fpos) :: frames Sc -> Permutation (ablocks B lyN S2) (ablocks B lyc Sc) -> ly_F lyN = ly_F lyc ->
F = frame_addr lyc 0 fpos -> FL = flag_addr lyc 0 fpos -> frame_flag_lawP tfibsegs B ->
alloc_ceiling <= slo -> shi <= 2 ^ 64 ->
(forall a, Eo a -> a < alloc_ceiling) -> (forall a, Eo a -> in_img tfibsegs a -> False) ->
(forall a, Zs a -> (slo <= a < shi) \/ Eo a \/ pp_nf F FL a) ->
acall_kept tfibsegs B lyc Sc W memc WX memX slo shi Eo ->
(forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview tfibsegs (w_H WY) memY a = aview tfibsegs (w_H WX) memX a) ->
(forall a, alloc_ceiling <= a < 2 ^ 64 -> apresent (w_H WX) memX a -> apresent (w_H WY) memY a) ->
acall_kept tfibsegs B lyc Sc W memc WY memY slo shi Eo.
Proof.
intros lyc lyN Sc S2 W memc mdc W2 mem2 md2 WX memX WY memY slo shi fpos F FL Eo Zs HAR HAR2 Hfrs Hperm HlyF EF EFL FFL
Hce Hshi HEc HEi HZ KP Hkp Hgr.
destruct (pz_nf_sep lyc lyN Sc S2 W2 mem2 md2 fpos F FL HAR2 Hfrs Hperm HlyF EF EFL FFL) as (N1 & N2 & N3 & N4).
exact (pz_kept_run tfibsegs B LAWS tfib_segs_low lyc Sc W memc mdc WX memX WY memY slo shi Eo (pp_nf F FL) Zs
HAR Hce Hshi HEc HEi N1 N2 N3 N4 HZ KP Hkp Hgr).
Qed.

(* The out-cells of a live call are not image bytes (caller frames are off the image). *)
Lemma pp_oc_img : forall lyc Sc W memc mdc (live : bool) mo lb cidm posm cidl posl,
AR tfibsegs B lyc Sc W memc mdc -> pp_oc_frames lyc Sc live mo lb cidm posm cidl posl ->
forall a, (live = true /\ pin_out_cell mo lb a) -> in_img tfibsegs a -> False.
Proof.
intros lyc Sc W memc mdc live mo lb cidm posm cidl posl HAR HOC a [Hl Ha] Hi.
destruct (HOC Hl) as (Hm & Hm1 & Hm2 & Hb & Hb1 & Hb2).
pose proof (frm_off_img B _ _ _ _ _ cidm posm HAR Hm) as Om. pose proof (frm_off_img B _ _ _ _ _ cidl posl HAR Hb) as Ol.
pose proof (tfib_img_range a Hi) as Hr. unfold TFIB_IMG_LO, TFIB_IMG_END, YImgTop.IMG_LO, YImgTop.IMG_TOP in Hr.
unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in Om, Ol. unfold pin_out_cell in Ha. lia.
Qed.

(* The out-cells' frames from the contract's live premise (tpin_parse_specX, PPgCSpec.v:493-501) and the
   caller's journal (the frames of Sc are own ++ frames S). *)
Lemma pp_oc_frames_of_pre : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
sa mo lb (s : list byte) cidm posm cidl posl,
ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
(pin_parse_live sa mo lb = true ->
 mo mod 8 = 0 /\ lb mod 8 = 0 /\ (mo + 8 <= lb \/ lb + 8 <= mo) /\
 In (cidm, posm) own /\ 0 <= cidm /\ frame_addr lyc cidm posm mod 8 = 0 /\
 frame_addr lyc cidm posm <= mo /\ mo + 8 <= frame_addr lyc cidm posm + fs_frame_bytes cidm /\
 In (cidl, posl) own /\ 0 <= cidl /\ frame_addr lyc cidl posl mod 8 = 0 /\
 frame_addr lyc cidl posl <= lb /\ lb + 8 <= frame_addr lyc cidl posl + fs_frame_bytes cidl /\
 afobj tfibsegs B lyc Sc W memc mo 8 /\ afobj tfibsegs B lyc Sc W memc lb 8 /\
 (forall x, pin_out_cell mo lb x -> ~ (spZ regs - T_parse_STK <= x < spZ regs)) /\
 (forall x, pin_out_cell mo lb x -> ~ (sa <= x <= sa + Z.of_nat (length s)))) ->
pp_oc_frames lyc Sc (pin_parse_live sa mo lb) mo lb cidm posm cidl posl.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs sa mo lb s cidm posm cidl posl HJ HL Hl.
pose proof HJ as (_ & _ & _ & _ & _ & Hfrs & _).
destruct (HL Hl) as (_ & _ & _ & Hm & _ & _ & Hm1 & Hm2 & Hb & _ & _ & Hb1 & Hb2 & _).
assert (Hin : forall c, In c own -> In c (frames Sc)) by (intros c Hc; rewrite Hfrs; apply in_or_app; left; exact Hc).
split; [exact (Hin _ Hm)|]. split; [exact Hm1|]. split; [exact Hm2|].
split; [exact (Hin _ Hb)|]. split; [exact Hb1 | exact Hb2].
Qed.

(* One step of the walk keeps the caller's memory in the form the walk carries (the call's window
   [spZ regs - T_parse_STK, spZ regs), the out-cells of a live call excluded): pz_kept_own with the caller
   cells the out-cells, its two side conditions on them from pp_oc_sep and pp_oc_img. *)
Lemma pp_KE_step : forall lyc Sc W memc mdc lyN SN W2 mem2 md2 WX memX WY memY fpos F FL sa mo lb
(regs : bvmap 5 word) cidm posm cidl posl (Zs : Z -> Prop),
AR tfibsegs B lyc Sc W memc mdc -> AR tfibsegs B lyN SN W2 mem2 md2 ->
frames SN = (0, fpos) :: frames Sc -> Permutation (ablocks B lyN SN) (ablocks B lyc Sc) -> ly_F lyN = ly_F lyc ->
F = frame_addr lyc 0 fpos -> FL = flag_addr lyc 0 fpos -> frame_flag_lawP tfibsegs B ->
alloc_ceiling <= spZ regs - T_parse_STK -> spZ regs <= 2 ^ 64 ->
pp_oc_frames lyc Sc (pin_parse_live sa mo lb) mo lb cidm posm cidl posl ->
(forall a, Zs a -> (spZ regs - T_parse_STK <= a < spZ regs) \/ (pin_parse_live sa mo lb = true /\ pin_out_cell mo lb a) \/
 pp_nf F FL a) ->
acall_kept tfibsegs B lyc Sc W memc WX memX (spZ regs - T_parse_STK) (spZ regs)
 (fun a => pin_parse_live sa mo lb = true /\ pin_out_cell mo lb a) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview tfibsegs (w_H WY) memY a = aview tfibsegs (w_H WX) memX a) ->
(forall a, alloc_ceiling <= a < 2 ^ 64 -> apresent (w_H WX) memX a -> apresent (w_H WY) memY a) ->
acall_kept tfibsegs B lyc Sc W memc WY memY (spZ regs - T_parse_STK) (spZ regs)
 (fun a => pin_parse_live sa mo lb = true /\ pin_out_cell mo lb a).
Proof.
intros lyc Sc W memc mdc lyN SN W2 mem2 md2 WX memX WY memY fpos F FL sa mo lb regs cidm posm cidl posl Zs
HAR HAR2 Hfrs Hperm HlyF EF EFL FFL Hce Hshi HOC HZ KP Hkp Hgr.
destruct (pp_oc_sep tfibsegs B LAWS lyc Sc W memc mdc _ mo lb cidm posm cidl posl HAR HOC) as (HEc & _).
exact (pz_kept_own lyc lyN Sc SN W memc mdc W2 mem2 md2 WX memX WY memY _ _ fpos F FL _ Zs
HAR HAR2 Hfrs Hperm HlyF EF EFL FFL Hce Hshi HEc (pp_oc_img lyc Sc W memc mdc _ mo lb cidm posm cidl posl HAR HOC)
HZ KP Hkp Hgr).
Qed.
End t.
End b.

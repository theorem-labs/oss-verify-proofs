(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the loop-body segment of fuzz_reply's gestures_end walk (lane W4). *)
(* Structure (not citation: another framework).  The step order and the shadow checks of this file are the ones
   proved at halts level on the same runs in a working branch 38a6eaf28b2
   lib/A/Prog/gestures_end_b.v:
     - one pass of the loop (0x825c0 -> gesture_end -> free (held[i]) -> 0x82610): gse_step :2542-2652;
     - the loop from its head, by induction on the keys left, with the two exits (back to 0x825c0, or 0x82638):
       gse_loop :2655-2759.
   The SRr form (a loop lemma from the loop head, a fresh symbolic state seated there, the induction on the
   entries left) is the one of proofs/cgif/cgif_file_fuzzer/lib/A/AC8b.v tcbb_loopX and of
   lib/A/W_check_bounded.v cb_loopX. *)
(* gse_loop_at (W_gse_cut.v:159), the loop head 0x825c0 of gestures_end with i < nheld keys still to end:
     0x825c0  load8 check of s->held, held[i]'s load8 check
     0x825e4  gesture_end (held[i])            (Section hypothesis GE, pb_gesture_end)
     0x825e8  the same two load8 checks, then  ld a0, held[i]
     0x8260c  free (held[i])                   (AFREE: the key's block is live)
     0x82610  nheld's load4 check, i++, 8i += 8
     0x82630  blt s5, nheld -> 0x825c0 (the invariant at i + 1, induction on length keys - i)
              else j 0x82638 (the Section hypothesis GSE_TAIL at i = length keys)
   Every __asan_report_* branch is NOT TAKEN: the three shadow entries of gl_SH (W_gestures_end.v) cover the
   granules of s->held, s->nheld and held[i], so the token engine decides each check inside paj_run_tok.
   The loop is proved over any allocator relation ARx (route (b), step 3; CONVERSION.md (sha256 1015972e02a9; internal record)) as
   pb_gse_loop_x : gse_loop_at_x, with GE : ge_spec_x, the free rules in their caller-context form over one context
   list CTX_AFREE with this piece's free site HCTX_gse_loop, GSE_TAIL_X : gse_tail_at_x, HP0,
   IMGC / BLKN, and two facts on the program statics PST: PSTR (no ROM byte is one; ajournal_gx_rom_view_x) and
   HEND5P (no byte of " end\0" is one; the literal is kept through gesture_end's journal).  pb_gse_loop, the AR
   statement, is re-derived from it at ARi0 (Section cAR). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep gestures_end_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_syms W_listing W_pl W_kit W_contract W_rep W_journal W_gse_cut W_gestures_end.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_kit_x W_journal_x W_contract_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_contract_xR.
(* C3: gse_room threads the live bytes by each key's gesture_end net change (ge_tr_net) and the key's free *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_tr_peak.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ------------------------------------------------------------------ list helpers *)
Lemma gll_skipn_S : forall (X : Type) (l : list X) (i : nat) x,
nth_error l i = Some x -> skipn i l = x :: skipn (S i) l.
Proof.
intros X l. induction l as [|y l IH]; intros i x Hn; [destruct i; discriminate|].
destruct i as [|i]; cbn [nth_error skipn] in Hn |- *; [injection Hn as <-; reflexivity | exact (IH i x Hn)].
Qed.
Lemma gll_firstn_S : forall (X : Type) (l : list X) (i : nat) x,
nth_error l i = Some x -> firstn (S i) l = firstn i l ++ [x].
Proof.
intros X l. induction l as [|y l IH]; intros i x Hn; [destruct i; discriminate|].
destruct i as [|i]; cbn [nth_error firstn] in Hn |- *;
[injection Hn as <-; reflexivity | cbn [app]; rewrite (IH i x Hn); reflexivity].
Qed.
Lemma gll_nodup_app : forall (X : Type) (l1 l2 : list X), List.NoDup (l1 ++ l2) -> forall x, In x l1 -> ~ In x l2.
Proof.
intros X l1. induction l1 as [|y l1 IH]; intros l2 HN x Hx; [destruct Hx|].
cbn [app] in HN. inversion HN as [|? ? Hni HN'].
destruct Hx as [<- | Hx]; [intros Hc; apply Hni, in_or_app; right; exact Hc | exact (IH l2 HN' x Hx)].
Qed.
Lemma gll_kblks_cons : forall k ks, kblks (k :: ks) = (key_addr k, Z.of_nat (length (key_text k)) + 1) :: kblks ks.
Proof. reflexivity. Qed.
Lemma gll_swap_app : forall (X : Type) (l1 l2 l3 : list X), Permutation (l1 ++ l2 ++ l3) (l2 ++ l1 ++ l3).
Proof. intros X l1 l2 l3. rewrite !app_assoc. apply Permutation_app_tail. apply Permutation_app_comm. Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PI).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).
Definition A_gse_ret1 : Z := A_gse_loop + 40.   (* 0x825e8: gesture_end's return address *)
Definition A_gse_ret2 : Z := A_gse_loop + 80.   (* 0x82610: free's return address *)
(* the shadow address the loop head carries in s2 / s6 *)
Lemma gll_shift : forall (E : env) (n : nat) v,
ew E 19 = Z_to_bv 64 SB -> ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
U E (SAlu ALU_ADD (SAlu ALU_SRL (SOff n 0) (SLit 3)) (SOff 19 0)) = v / 8 + SB.
Proof.
intros E n v E19 Hn Hv. rewrite !U_SAlu, (U_atom E n v Hn Hv), (U_atom E 19 SB E19) by (unfold SB; lia).
rewrite U_lit by lia. cbn [zalu_raw]. change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia.
change (2 ^ 3) with 8. unfold zcanon, M64.
assert (Hd : 0 <= v / 8 < 2 ^ 61) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
rewrite (Z.mod_small (v / 8)) by lia. apply Z.mod_small. unfold SB in *. lia.
Qed.
(* ---- the model's arithmetic is non-negative, for any meter with its laws (the walk's MT, and W_contract_x's MT_rk,
   the allocator-call count the room round's RM charges) ---- *)
Section nn.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Lemma gll_sl_run_cap_nonneg : forall f mx no cap rem j o, 0 <= mx -> 0 <= no -> 0 <= cap ->
0 <= fst (snd (send_line_b_c.sl_run f mx no cap rem j o)).
Proof.
induction f as [|f IH]; intros mx no cap rem j o Hmx Hno Hcap; cbn [send_line_b_c.sl_run]; [cbn; lia|].
destruct (rem <=? 0) eqn:Er; [cbn; lia|]. apply Z.leb_gt in Er.
assert (Hn : 0 <= (if negb (mx =? 0) && (mx <? rem) then mx else rem)) by (destruct (negb (mx =? 0) && (mx <? rem)); lia).
destruct (cap <? no + _); cbn [fst snd]; apply IH; lia.
Qed.
Lemma gll_sl_cap_nonneg : forall c mx no cap len, 0 <= mx -> 0 <= no -> 0 <= cap -> 0 <= sl_cap c mx no cap len.
Proof.
intros c mx no cap len Hmx Hno Hcap. unfold sl_cap, send_line_b_c.send_line_cap.
destruct (sl_live c len); [apply gll_sl_run_cap_nonneg; lia | lia].
Qed.
Lemma gll_sl_no_nonneg : forall c no len, 0 <= no -> 0 <= len -> 0 <= sl_no c no len.
Proof. intros c no len H1 H2. unfold sl_no. destruct (sl_live c len); lia. Qed.
Lemma gll_sl_cost_run_nonneg : forall f mx no cap rem, 0 <= mx -> 0 <= no -> 0 <= cap -> 0 <= sl_cost_run MT f mx no cap rem.
Proof.
induction f as [|f IH]; intros mx no cap rem Hmx Hno Hcap; cbn [sl_cost_run]; [lia|].
destruct (rem <=? 0) eqn:Er; [lia|]. apply Z.leb_gt in Er.
assert (Hn : 0 <= (if negb (mx =? 0) && (mx <? rem) then mx else rem)) by (destruct (negb (mx =? 0) && (mx <? rem)); lia).
pose proof (mo_free_nonneg MT MTL) as Hf.
destruct (cap <? no + _).
- pose proof (mo_malloc_nonneg MT MTL ((no + (if negb (mx =? 0) && (mx <? rem) then mx else rem)) * 2) ltac:(lia)) as Hm.
  pose proof (IH mx (no + (if negb (mx =? 0) && (mx <? rem) then mx else rem))
    ((no + (if negb (mx =? 0) && (mx <? rem) then mx else rem)) * 2)
    (rem - (if negb (mx =? 0) && (mx <? rem) then mx else rem)) Hmx ltac:(lia) ltac:(lia)). lia.
- apply IH; lia.
Qed.
Lemma gll_sl_cost_nonneg : forall c mx no cap len, 0 <= mx -> 0 <= no -> 0 <= cap -> 0 <= sl_cost MT c mx no cap len.
Proof. intros. unfold sl_cost. destruct (sl_live c len); [apply gll_sl_cost_run_nonneg; lia | lia]. Qed.
Lemma gll_ge_no_nonneg : forall c no len, 0 <= no -> 0 <= len -> 0 <= ge_no c no len.
Proof. intros c no len H1 H2. unfold ge_no. apply gll_sl_no_nonneg; [apply gll_sl_no_nonneg; lia | lia]. Qed.
Lemma gll_ge_cap_nonneg : forall c mx no cap len, 0 <= mx -> 0 <= no -> 0 <= cap -> 0 <= len -> 0 <= ge_cap c mx no cap len.
Proof.
intros c mx no cap len Hmx Hno Hcap Hl. unfold ge_cap.
apply gll_sl_cap_nonneg; [lia | apply gll_sl_no_nonneg; lia | apply gll_sl_cap_nonneg; lia].
Qed.
Lemma gll_ge_cost_nonneg : forall c mx no cap len, 0 <= mx -> 0 <= no -> 0 <= cap -> 0 <= len -> 0 <= ge_cost MT c mx no cap len.
Proof.
intros c mx no cap len Hmx Hno Hcap Hl. unfold ge_cost.
pose proof (gll_sl_cost_nonneg c mx no cap len Hmx Hno Hcap).
pose proof (gll_sl_cost_nonneg (sl_ctl c len) mx (sl_no c no len) (sl_cap c mx no cap len) 5 Hmx
  ltac:(apply gll_sl_no_nonneg; lia) ltac:(apply gll_sl_cap_nonneg; lia)). lia.
Qed.
Lemma gll_cost_nonneg : forall xs c mx no cap, 0 <= mx -> 0 <= no -> 0 <= cap -> 0 <= gse_cost MT c mx no cap xs.
Proof.
induction xs as [|x xs IH]; intros c mx no cap Hmx Hno Hcap; cbn [gse_cost]; [pose proof (mo_free_nonneg MT MTL); lia|].
pose proof (mo_free_nonneg MT MTL).
pose proof (gll_ge_cost_nonneg c mx no cap (Z.of_nat (length x)) Hmx Hno Hcap ltac:(lia)).
pose proof (IH (ge_ctl c (Z.of_nat (length x))) mx (ge_no c no (Z.of_nat (length x)))
  (ge_cap c mx no cap (Z.of_nat (length x))) Hmx ltac:(apply gll_ge_no_nonneg; lia)
  ltac:(apply gll_ge_cap_nonneg; lia)). lia.
Qed.
End nn.
Section c.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Context {hl : Z}.
Variable MT : ameter_ops.
Variable RP : roomp.
Variable MMAX : Z.
Variable RG : rep_globals.
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
Hypothesis HP0 : forall ly S Hp W mem md, ARx ly S Hp W mem md -> Hp = [].
Hypothesis TL : PALib B.
Hypothesis HG : gx_ok SEGS B (G_SL B RG).
Hypothesis MTL : ameter_laws MT.
Hypothesis GE : ge_spec_x B PST ARx MT RP MMAX RG (BASE + AF_fr_gesture_end).
(* the free rules in their caller-context form (a Theorem Labs lane's 21:20Z ruling): one context list per allocator entry,
   and the free call site of this piece, 0x8260c, as a closed singleton of its return address 0x82610 = gestures_end
   + 0xbc (ATopKeeper's K0 table CTX_AFREE, lib/A/ACk0.v) *)
Variable CTX_AFREE : list (list Z).
Hypothesis AFREE : afree_cf_rule_c_x SEGS B PST ARx MT RP CTX_AFREE.
Hypothesis AFREEN : afree_null_cf_rule_c_x SEGS B PST ARx MT RP CTX_AFREE.
Hypothesis HCTX_gse_loop : In [BASE + AF_fr_gestures_end + 0xbc] CTX_AFREE.
Hypothesis HROMO : rom_out SEGS B (G_SL B RG).
Hypothesis HOUTG : forall r a, In r (aout_fp B RG 0 0) -> fst r <= a < snd r -> ~ (as_errno B <= a < as_errno B + 4) ->
  in_img SEGS a /\ ~ in_rom SEGS a /\ ~ Exists (in_zr a) (as_owned_static B).
(* " end\0" lies in the image (true at every placement: it is .rodata).  The zero-shadow claim that stood here before
   is FALSE at the instance (partial granule: shadow byte 5 at 0x7fffc1e0, W3's measurement) and was never needed. *)
Hypothesis HEND5I : forall a, VAL A_lit_end5 <= a < VAL A_lit_end5 + 5 -> in_img SEGS a.
(* HEND5G holds for EXACTLY [VAL A_lit_end5, VAL A_lit_end5 + 5) = [0x20f00, 0x20f05) on both images and MUST NOT BE
   WIDENED: its `~ owned_static` clause is TRUE (StartupTrace's tfib_lit_end5_not_owned_static, a working branch
   5fab70f4113; ZeroGlobals and W1Verify measured the same rows) only because owned_static's rows (0x20ee1, 0x1f) and
   (0x20f05, 0x1b) - the literal's two redzones - end and start exactly at its edges.  One byte more on either side,
   or rounding the range to 8 bytes or an aligned word, makes that clause FALSE. *)
Hypothesis HEND5G : forall a, VAL A_lit_end5 <= a < VAL A_lit_end5 + 5 ->
  ~ inG (G_SL B RG) a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
(* the program statics PST hold no ROM byte and no byte of " end\0" (both .rodata; at PST := [] trivially) *)
Hypothesis PSTR : forall a, in_rom SEGS a -> ~ Exists (in_zr a) PST.
Hypothesis HEND5P : forall a, VAL A_lit_end5 <= a < VAL A_lit_end5 + 5 -> ~ Exists (in_zr a) PST.
(* the stretch after the loop, 0x82638 onwards: lane GseTail (lib/A/W_gse_tail.v), in its generic form *)
Hypothesis GSE_TAIL_X : gse_tail_at_x B PST ARx MT RP MMAX RG (BASE + A_gse_tail).
Hypothesis IMGC : forall ly S Hp W mem md, ARx ly S Hp W mem md ->
fst (ly_img ly) <= 0x10000 /\ 0x5fb000 <= fst (ly_img ly) + snd (ly_img ly).
Hypothesis BLKN : forall ly S Hp W mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL. Let HBfree := pal_free B TL.
Let RUN := paj_run_x_x B PST ARx LAWS (G_SL B RG) HG 0 [].
Let RUNTO := paj_run_to_x_x B PST ARx LAWS (G_SL B RG) HG 0 [].
Let BR := paj_branch (PI := PI).

(* ------------------------------------------------------------------ blocks *)
(* Two distinct live blocks are disjoint (the allocator law's pairwise separation, at any two positions). *)
Lemma gll_disj_x : forall ly' S' Hp' (W' : world SEGS) mem' md' p n q m,
ARx ly' S' Hp' W' mem' md' -> In (p, n) (ablocks B ly' S') -> In (q, m) (ablocks B ly' S') -> (p, n) <> (q, m) ->
p + req_size n <= q \/ q + req_size m <= p.
Proof.
intros ly' S' Hp' W' mem' md' p n q m HAR H1 H2 Hne.
pose proof (sep_blocks_x SEGS B ARx LAWS ly' S' Hp' W' mem' md' p n q m HAR H1 H2 Hne) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. exact Hd.
Qed.

Lemma gll_room_mono : forall xs bb bb' c mx no cap, bb <= bb' ->
gse_room MMAX bb' c mx no cap xs -> gse_room MMAX bb c mx no cap xs.
Proof.
induction xs as [|x xs IH]; intros bb bb' c mx no cap Hle HR; [exact I|].
destruct HR as [HR1 HR2]. split; [unfold ge_room in *; lia|].
apply (IH _ (bb' + tr_net (ge_tr c mx no cap (Z.of_nat (length x))) - (Z.of_nat (length x) + 1))); [lia | exact HR2].
Qed.
(* ---- the capacity a key's gesture_end adds is one of the requests its trace makes (a Theorem Labs lane's ge_room form).
   Until lib/A/W_ge_room.v lands, ge_cap_grow_le_tr is proved here. *)
Lemma gll_tr_alloc_app : forall (P : Type) (l1 l2 : list (RelayRunT.rev P)),
tr_alloc (l1 ++ l2) = tr_alloc l1 + tr_alloc l2.
Proof.
intros P l1 l2. unfold tr_alloc. induction l1 as [|ev l1 IH]; cbn [app fold_right]; [lia|].
rewrite IH. destruct ev; lia.
Qed.
Lemma gll_sl_run_cap_indep : forall f mx no cap rem j o j' o',
fst (snd (send_line_b_c.sl_run f mx no cap rem j o)) = fst (snd (send_line_b_c.sl_run f mx no cap rem j' o')).
Proof.
induction f as [|f IH]; intros mx no cap rem j o j' o'; cbn [send_line_b_c.sl_run]; [reflexivity|].
destruct (rem <=? 0); [reflexivity|].
destruct (cap <? no + (if negb (mx =? 0) && (mx <? rem) then mx else rem)); cbn [fst snd]; apply IH.
Qed.
Lemma gll_sl_run_tr : forall f mx no cap rem j o, 0 <= mx -> 0 <= no -> 0 <= cap ->
fst (snd (send_line_b_c.sl_run f mx no cap rem j o)) - cap
  <= tr_alloc (fst (send_line_b_c.sl_run f mx no cap rem j o)).
Proof.
induction f as [|f IH]; intros mx no cap rem j o Hmx Hno Hcap; cbn [send_line_b_c.sl_run]; [cbn; lia|].
destruct (rem <=? 0) eqn:Er; [cbn; lia|]. apply Z.leb_gt in Er.
assert (Hn : 0 <= (if negb (mx =? 0) && (mx <? rem) then mx else rem))
  by (destruct (negb (mx =? 0) && (mx <? rem)); lia).
destruct (cap <? no + (if negb (mx =? 0) && (mx <? rem) then mx else rem)) eqn:Ec.
- cbn [fst snd].
  lazymatch goal with
  | |- fst (snd (send_line_b_c.sl_run f ?a ?b ?cc ?dd ?jj ?oo)) - _ <= _ =>
    pose proof (IH a b cc dd jj oo Hmx ltac:(lia) ltac:(lia)) as Hih
  end.
  unfold tr_alloc in Hih |- *. destruct (cap =? 0); cbn; lia.
- apply IH; [exact Hmx | lia | exact Hcap].
Qed.
Lemma gll_sl_cap_tr : forall live mx no cap len j o, 0 <= mx -> 0 <= no -> 0 <= cap ->
send_line_b_c.send_line_cap live mx no cap len - cap
  <= tr_alloc (send_line_b_c.send_line_tr live mx no cap len j o).
Proof.
intros live mx no cap len j o Hmx Hno Hcap.
unfold send_line_b_c.send_line_cap, send_line_b_c.send_line_tr. destruct live; [|cbn; lia].
rewrite (gll_sl_run_cap_indep (Z.to_nat len) mx no cap len 0 RelayRunF.adr0 j o).
apply gll_sl_run_tr; lia.
Qed.
(* the second send of gesture_end is live exactly when the first is (a key is never empty) *)
Lemma gll_live_eq : forall c XL, XL <> 0 -> sl_live (sl_ctl c XL) 5 = sl_live c XL.
Proof.
intros c XL HX. unfold sl_live, sl_ctl, send_line_c.send_live, send_line_c.send_off.
cbn [ct_cl ct_br ct_dd].
replace (XL =? 0) with false by (symmetry; apply Z.eqb_neq; exact HX).
replace (5 =? 0) with false by reflexivity.
destruct (ct_cl c <? 0); cbn [orb negb andb]; [reflexivity|].
destruct (ct_br c =? 1) eqn:Ebr; cbn [orb negb andb]; [rewrite Ebr; reflexivity|].
destruct (ct_dd c =? 0) eqn:Edd; cbn [orb negb andb]; [|rewrite Bool.andb_false_r; reflexivity].
replace (ct_dd c) with 0 by (symmetry; apply Z.eqb_eq; exact Edd). cbn. reflexivity.
Qed.
Lemma gll_ge_cap_tr : forall c mx no cap XL, 0 <= mx -> 0 <= no -> 0 <= cap -> 0 < XL ->
ge_cap c mx no cap XL - cap <= tr_alloc (ge_tr c mx no cap XL).
Proof.
intros c mx no cap XL Hmx Hno Hcap HX.
pose proof (gll_sl_cap_nonneg c mx no cap XL Hmx Hno Hcap) as H2. unfold sl_cap in H2.
pose proof (gll_sl_cap_tr (sl_live c XL) mx no cap XL 0 RelayRunF.adr0 Hmx Hno Hcap) as H1.
unfold ge_cap, ge_tr, gesture_end_b_c.gesture_end_tr, sl_cap, sl_no.
rewrite gll_tr_alloc_app, (gll_live_eq c XL ltac:(lia)).
destruct (sl_live c XL) eqn:Elv.
- lazymatch goal with
  | |- _ - _ <= _ + tr_alloc (send_line_b_c.send_line_tr ?lv ?m ?nn ?cc ?ln ?jj ?oo) =>
    pose proof (gll_sl_cap_tr lv m nn cc ln jj oo Hmx ltac:(lia) ltac:(lia)) as H3
  end. lia.
- cbn. lia.
Qed.

(* ------------------------------------------------------------------ the output stream, kept *)
Lemma gll_aout_facts : forall ly' S' (W' : world SEGS) mem' c O' mx' no' cap' out',
aout_at B RG ly' S' W' mem' c O' mx' no' cap' out' ->
0 <= mx' <= 255 /\ Z.of_nat (length O') = no' /\
((cap' = 0 /\ out' = 0 /\ no' = 0) \/ (0 < cap' /\ no' <= cap' /\ In (out', cap') (ablocks B ly' S'))).
Proof.
intros ly' S' W' mem' c O' mx' no' cap' out'
(_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hmx & Hno & Hd).
split; [exact Hmx|]. split; [exact Hno|].
destruct Hd as [Hd | (H1 & H2 & H3 & _)]; [left; exact Hd | right; split; [exact H1 | split; [exact H2 | exact H3]]].
Qed.
(* every byte of the output's footprint is one the reader already sees *)
Lemma gll_aout_some : forall ly' S' (W' : world SEGS) mem' c O' mx' no' cap' out',
aout_at B RG ly' S' W' mem' c O' mx' no' cap' out' ->
forall r a, In r (aout_fp B RG cap' out') -> fst r <= a < snd r -> aview SEGS (w_H W') mem' a <> None.
Proof.
intros ly' S' W' mem' c O' mx' no' cap' out'
(H1 & _ & H3 & _ & H5 & _ & H7 & _ & H9 & _ & H11 & _ & H13 & _ & H15 & _ & H17 & _ & _ & _ & _ & _ & _ & _ & Hno & Hd)
r a Hr Ha.
unfold aout_fp in Hr. cbn [In] in Hr.
assert (VM : forall b (n : nat) v, val_mem SEGS (arm W' mem') b n v -> b <= a < b + Z.of_nat n ->
  aview SEGS (w_H W') mem' a <> None).
{ intros b n v Hv Hb. replace a with (b + (a - b)) by lia. exact (gse_view_some (w_H W') mem' b n v (a - b) Hv ltac:(lia)). }
destruct Hr as [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | Hr]]]]]]]]]; cbn [fst snd] in Ha.
- exact (VM _ 8%nat _ H1 ltac:(cbn; lia)).
- exact (VM _ 8%nat _ H3 ltac:(cbn; lia)).
- exact (VM _ 8%nat _ H5 ltac:(cbn; lia)).
- exact (VM _ 8%nat _ H7 ltac:(cbn; lia)).
- exact (VM _ 4%nat _ H9 ltac:(cbn; lia)).
- exact (VM _ 1%nat _ H11 ltac:(cbn; lia)).
- exact (VM _ 1%nat _ H13 ltac:(cbn; lia)).
- exact (VM _ 1%nat _ H15 ltac:(cbn; lia)).
- exact (VM _ 4%nat _ H17 ltac:(cbn; lia)).
- destruct (Z.eqb_spec cap' 0) as [Hc0 | Hc0]; [destruct Hr|].
  destruct Hr as [<- | []]. cbn [fst snd] in Ha.
  destruct Hd as [(Hz & _) | (_ & _ & _ & junk & Hj & Hgo)]; [lia|].
  replace a with (out' + (a - out')) by lia.
  apply (gse_view_garr8 (w_H W') mem' out' _ (a - out') Hgo).
  unfold bzs. rewrite length_map, length_app, Nat2Z.inj_add. lia.
Qed.
(* the output's footprint is off the read-only segments and inside the address space *)
Lemma gll_aout_rom_x : forall ly' S' Hp' (W' : world SEGS) mem' md' c O' mx' no' cap' out',
ARx ly' S' Hp' W' mem' md' -> aout_at B RG ly' S' W' mem' c O' mx' no' cap' out' ->
forall r a, In r (aout_fp B RG cap' out') -> fst r <= a < snd r -> 0 <= a < 2 ^ 64 /\ ~ in_rom SEGS a.
Proof.
intros ly' S' Hp' W' mem' md' c O' mx' no' cap' out' HAR HOUT r a Hr Ha.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (gse_aout_fp_cases B RG cap' out' r Hr) as [Hc | (Hc & ->)].
- destruct (Z_le_gt_dec (as_errno B) a) as [E1 | E1]; [destruct (Z_lt_ge_dec a (as_errno B + 4)) as [E2 | E2]|].
  + assert (HIe : inG (G_SL B RG) a).
    { unfold G_SL. apply Exists_exists. exists (as_errno B, 4).
      split; [cbn [In]; tauto | unfold in_zr; cbn [fst snd]; lia]. }
    destruct (HG a HIe) as [Hi _]. pose proof (pa_img_range a Hi).
    split; [lia|]. intros Hrom. destruct (HROMO a Hrom) as (Hng & _). exact (Hng HIe).
  + destruct (HOUTG r a Hc Ha ltac:(lia)) as (Hi & Hro & _). pose proof (pa_img_range a Hi). split; [lia | exact Hro].
  + destruct (HOUTG r a Hc Ha ltac:(lia)) as (Hi & Hro & _). pose proof (pa_img_range a Hi). split; [lia | exact Hro].
- cbn [fst snd] in Ha.
  destruct (gll_aout_facts _ _ _ _ _ _ _ _ _ _ HOUT) as (_ & _ & [(Hz & _) | (_ & _ & Hin)]); [lia|].
  destruct (alx_blocks _ _ _ LAWS ly' S' Hp' W' mem' md' out' cap' HAR Hin) as (_ & Hp4 & Hpc & _).
  pose proof (req_size_pos cap' ltac:(lia)) as [_ Hrs].
  pose proof (blk_off_imgP_x B ARx LAWS IMGC BLKN ly' S' Hp' W' mem' md' out' cap' HAR Hin) as Hoff. unfold off_img in Hoff.
  split; [lia|]. intros Hrom.
  assert (Hi : in_img SEGS a) by (destruct Hrom as (sg & Hsg & _ & Hr'); exists sg; split; [exact Hsg | lia]).
  pose proof (pa_img_range a Hi). lia.
Qed.
Lemma gll_aout_kept : forall ly1 S1 (W1 : world SEGS) mem1 ly2 S2 (W2 : world SEGS) mem2 c O' mx' no' cap' out',
aout_at B RG ly1 S1 W1 mem1 c O' mx' no' cap' out' ->
(forall r a, In r (aout_fp B RG cap' out') -> fst r <= a < snd r ->
   aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W1) mem1 a) ->
(forall r a, In r (aout_fp B RG cap' out') -> fst r <= a < snd r -> 0 <= a < 2 ^ 64 /\ ~ in_rom SEGS a) ->
(forall b, In b (aout_blks cap' out') -> In b (ablocks B ly2 S2)) ->
aout_at B RG ly2 S2 W2 mem2 c O' mx' no' cap' out'.
Proof.
intros ly1 S1 W1 mem1 ly2 S2 W2 mem2 c O' mx' no' cap' out' HOUT KV KR HB.
apply (aout_at_kept B RG ly1 S1 W1 mem1 ly2 S2 W2 mem2 c O' mx' no' cap' out' HOUT); [|exact HB].
intros r Hr a Ha. destruct (KR r a Hr Ha) as [Ha64 Hrom].
exact (gse_abyte_kept W1 W2 mem1 mem2 a Ha64 (KV r a Hr Ha)
  (gll_aout_some ly1 S1 W1 mem1 c O' mx' no' cap' out' HOUT r a Hr Ha) Hrom).
Qed.

(* ------------------------------------------------------------------ gesture_end at the loop's frame *)
(* gesture_end's contract GE through W_gestures_end.v's gse_callS_x, with the call made 80 bytes below the caller's sp
   (the loop body's own frame).  The room round: GE's kr, its RM premise and count premise (ge_spec_x's, at its named
   peak ge_pk), and its post's RM, are the lemma's. *)
Lemma gll_ge_x : forall W regsc memc mdc STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc k raw c O mx no cap out x q m (kr : nat),
ajournal_gx_x SEGS B PST ARx (G_SL B RG) 0 [] STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memc mdc k ->
spZ regsc = sp0 - 80 -> GE_STK + 80 <= STK ->
getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
getr regsc 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
s0Z regsc < alloc_ceiling ->
getr regsc 10 = w64 q ->
aout_at B RG lyc Sc W memc c O mx no cap out ->
garr8 SEGS (arm W memc) q (bzs (x ++ [Z_to_bv 8 0])) -> ~ In (Z_to_bv 8 0) x ->
14 <= Z.of_nat (length x) <= APARTIAL ->
In (q, m) (ablocks B lyc Sc) -> q <> out -> Z.of_nat (length x) + 1 <= req_size m ->
garr8 SEGS (arm W memc) (VAL A_lit_end5) (bzs END5) -> rom_view SEGS W memc ->
ge_room MMAX (blocks_bytes Sc) c mx no cap (Z.of_nat (length x)) ->
mo_ok MT Sc (ge_cost MT c mx no cap (Z.of_nat (length x))) ->
rp_RM RP Sc (Z.to_nat (ge_cost MT_rk c mx no cap (Z.of_nat (length x))) + kr) ->
cnt_ok_pk RP ge_pk (ablocks B lyc Sc) ->
(forall a, inFP (ablocks_fp (aout_blks cap out)) a ->
 (inFP FP a /\ exists b n, In (b, n) (ablocks B lyc Sc) /\ b <= a < b + req_size n) \/
 in_tmp_block (ablocks B ly S) (ablocks B lyc Sc) a) ->
SRr SEGS W (mkCfg (mkst regsc (Z_to_bv 64 (BASE + AF_fr_gesture_end)) memc (seg_rom SEGS)) mdc)
(fun W2 c2 => exists ly2 S2 Hp2 regs2 mem2 md2 k1 out',
 c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
 ajournal_gx_x SEGS B PST ARx (G_SL B RG) 0 [] STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 (k + k1) /\
 ajournal_gx_x SEGS B PST ARx (G_SL B RG) 0 [] GE_STK (sp0 + -80) (ablocks_fp (aout_blks cap out)) lyc Sc Hpc W memc mdc []
   ly2 S2 Hp2 W2 mem2 md2 k1 /\
 aregs_preserved regsc regs2 /\ apres_kept B W memc W2 mem2 /\
 mo_le MT Sc S2 (ge_cost MT c mx no cap (Z.of_nat (length x))) /\
 rp_RM RP S2 kr /\
 (exists rest, Permutation (ablocks B lyc Sc) (aout_blks cap out ++ rest) /\
   Permutation (ablocks B ly2 S2) (aout_blks (ge_cap c mx no cap (Z.of_nat (length x))) out' ++ rest)) /\
 aout_at B RG ly2 S2 W2 mem2 (ge_ctl c (Z.of_nat (length x))) (ge_O c O x) mx (ge_no c no (Z.of_nat (length x)))
   (ge_cap c mx no cap (Z.of_nat (length x))) out').
Proof.
intros W regsc memc mdc STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc k raw c O mx no cap out x q m kr
  HJ Hsp HSTK Hgp Htp Hra Hraw Hra4 Hs0 H10 HOUT GK NZ X1 Hq Hqo Hqm G5 HROM ROOM MOK HRM HCNT HF.
eapply SRr_mono.
{ eapply (gse_callS_x B PST ARx LAWS (G_SL B RG) W regsc memc (Z_to_bv 64 (BASE + AF_fr_gesture_end)) STK sp0 FP ly S Hp W0
    mem md own lyc Sc Hpc mdc k GE_STK (ablocks_fp (aout_blks cap out)) (-80) raw []
    (fun ly2 S2 W2 regs2 mem2 md2 => exists out', apres_kept B W memc W2 mem2 /\
      mo_le MT Sc S2 (ge_cost MT c mx no cap (Z.of_nat (length x))) /\
      rp_RM RP S2 kr /\
      (exists rest, Permutation (ablocks B lyc Sc) (aout_blks cap out ++ rest) /\
        Permutation (ablocks B ly2 S2) (aout_blks (ge_cap c mx no cap (Z.of_nat (length x))) out' ++ rest)) /\
      aout_at B RG ly2 S2 W2 mem2 (ge_ctl c (Z.of_nat (length x))) (ge_O c O x) mx (ge_no c no (Z.of_nat (length x)))
        (ge_cap c mx no cap (Z.of_nat (length x))) out')
    HG HJ).
  - lia.
  - reflexivity.
  - lia.
  - unfold GE_STK, GE_FRAME, SL_STK, SL_FRAME, ASTACK, ESTACK. lia.
  - lia.
  - exact Hgp.
  - exact Htp.
  - exact Hra.
  - exact Hraw.
  - exact Hra4.
  - apply achain_low. exact Hs0.
  - intros HPRE1. eapply SRr_mono.
    { exact (GE W lyc Sc Hpc regsc memc mdc [] c O mx no cap out q x q m HPRE1 H10 HOUT GK NZ X1 Hq Hqo
        ltac:(lia) ltac:(lia) G5 HROM ROOM MOK kr HRM HCNT). }
    cbv beta.
    intros W3 c3 _ (ly3 & S3 & Hp3 & regs3 & mem3 & md3 & k3 & out3 & -> & HJ3 & HP3 & HA3 & HM3 & HR3 & HPm3 & HO3).
    exists ly3, S3, Hp3, regs3, mem3, md3, k3. split; [rewrite Hra; reflexivity|]. split; [exact HJ3|]. split; [exact HP3|].
    exists out3. split; [exact HA3|]. split; [exact HM3|]. split; [exact HR3|]. split; [exact HPm3 | exact HO3].
  - exact HF. }
cbv beta. intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HJ2 & HJc2 & HP2 & (out' & HA & HM & HR & HPm & HO)).
exists ly2, S2, Hp2, regs2, mem2, md2, k1, out'. split; [reflexivity|]. split; [exact HJ2|].
split; [exact HJc2|]. split; [exact HP2|]. split; [exact HA|]. split; [exact HM|]. split; [exact HR|].
split; [exact HPm | exact HO].
Qed.

(* ------------------------------------------------------------------ the seat at 0x825c0 *)
(* s0 = SA + 48 (atom 8), s1 = SA + 40 (atom 9), s3 = SB (atom 19), s4 = 8i (atom 20), s5 = i (atom 21),
   s2 = shadow (s0) and s6 = shadow (s1) (gl_regs); atom 32 = held, 33 = held + 8i (the alias), 34 = held[i],
   35 = nheld (W_gestures_end.v gl_regions / gl_facts / gl_SH). *)
Lemma gll_seat : forall (Wc : world SEGS) (regsc : bvmap 5 word) memc SA hp ka nh (i : Z),
getr regsc 8 = w64 (SA + 48) -> getr regsc 9 = w64 (SA + 40) ->
getr regsc 18 = w64 ((SA + 48) / 8 + SB) -> getr regsc 19 = w64 SB ->
getr regsc 20 = w64 (8 * i) -> getr regsc 21 = w64 i ->
getr regsc 22 = w64 ((SA + 40) / 8 + SB) ->
4096 <= SA -> SA mod 8 = 0 -> SA + 56 <= 140737479966720 ->
(SA + 56 <= 2147450880 \/ 17594333495296 <= SA) ->
4096 <= hp -> hp mod 8 = 0 -> hp + 8 * i + 8 <= 140737479966720 ->
(hp + 8 * i + 8 <= 2147450880 \/ 17594333495296 <= hp) ->
(hp + 8 * i + 8 <= SA + 40 \/ SA + 52 <= hp + 8 * i) ->
4096 <= ka -> ka mod 16 = 0 -> ka <= 140737479966720 ->
0 <= i -> 8 * i <= 2 ^ 29 -> i <= 2 ^ 26 -> 0 <= nh <= 2 ^ 26 ->
val_mem SEGS (arm Wc memc) (SA + 40) 8 hp ->
val_mem SEGS (arm Wc memc) (SA + 48) 4 nh ->
val_mem SEGS (arm Wc memc) (hp + 8 * i) 8 ka ->
range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF (SA + 40) 16 ->
range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF (hp + 8 * i) 8 ->
st_ok_pi SEGS VAL (Eimg (Ereg regsc (gl_extra hp (hp + 8 * i) ka nh))) ss_gl
  (restrict (w_H Wc) (mkst regsc (Z_to_bv 64 (BASE + A_gse_loop)) memc (seg_rom SEGS)))
/\ sh_ok SEGS BxL gl_SH (Eimg (Ereg regsc (gl_extra hp (hp + 8 * i) ka nh))) (mrestrict (w_H Wc) memc).
Proof.
intros Wc regsc memc SA hp ka nh i R8 R9 R18 R19 R20 R21 R22
HSA0 HSA8 HSAC HSAZ Hhp0 Hhp8 HhpC HhpZ HDIS Hka0 Hka16 HkaC Hi0 Hi8 Hi26 Hnh Mhp Mnh Mka RA1 RA2.
pose proof pa_B_ok as HBASE. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regsc (gl_extra hp (hp + 8 * i) ka nh))).
assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E m = getr regsc rr).
{ intros m rr Hm. subst E. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hm. }
assert (E8 : ew E 8 = Z_to_bv 64 (SA + 48)) by (rewrite (EEo 8%nat 8%bv eq_refl); exact R8).
assert (E9 : ew E 9 = Z_to_bv 64 (SA + 40)) by (rewrite (EEo 9%nat 9%bv eq_refl); exact R9).
assert (E19 : ew E 19 = Z_to_bv 64 SB) by (rewrite (EEo 19%nat 19%bv eq_refl); exact R19).
assert (E20 : ew E 20 = Z_to_bv 64 (8 * i)) by (rewrite (EEo 20%nat 20%bv eq_refl); exact R20).
assert (E21 : ew E 21 = Z_to_bv 64 i) by (rewrite (EEo 21%nat 21%bv eq_refl); exact R21).
assert (E32 : ew E 32 = Z_to_bv 64 hp) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsc _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (hp + 8 * i)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsc _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 ka) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsc _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 nh) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsc _ 3)).
assert (QB : 0 <= SA / 8 <= 17592186044415)
  by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
assert (QH : 0 <= hp / 8 <= 17592186044415)
  by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
assert (QB1 : 0 <= (SA + 48) / 8 <= 17592186044415)
  by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
assert (QB2 : 0 <= (SA + 40) / 8 <= 17592186044415)
  by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
assert (V18 : getr regsc 18 = sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 8 0) (SLit 3)) (SOff 19 0))).
{ apply bv_eq. fold (U E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 8 0) (SLit 3)) (SOff 19 0))).
  rewrite (gll_shift E 8%nat (SA + 48) E19 E8 ltac:(lia)), R18.
  rewrite unsigned_lit_small by (unfold SB in *; lia). reflexivity. }
assert (V22 : getr regsc 22 = sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 9 0) (SLit 3)) (SOff 19 0))).
{ apply bv_eq. fold (U E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 9 0) (SLit 3)) (SOff 19 0))).
  rewrite (gll_shift E 9%nat (SA + 40) E19 E9 ltac:(lia)), R22.
  rewrite unsigned_lit_small by (unfold SB in *; lia). reflexivity. }
split.
- unfold ss_gl, gl_regs. apply pa_entry_st_ok_full.
  + apply regs_ok_pin;
    [apply regs_ok_pin; [subst E; apply regs_ok_Eimg_Ereg | intros X; discriminate X | exact V18]
    | intros X; discriminate X | exact V22].
  + vm_compute. reflexivity.
  + unfold gl_regions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * cbn [base_val]. rewrite E9, unsigned_lit_small by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (SA + 40) 0 8 (SOff 32 0) hp);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      rewrite Z.add_0_r. exact Mhp.
    * cbn [base_val]. rewrite E8, unsigned_lit_small by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (SA + 48) 0 4 (SOff 35 0) nh);
      [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      rewrite Z.add_0_r. exact Mnh.
    * cbn [base_val]. rewrite E33, unsigned_lit_small by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (hp + 8 * i) 0 8 (SOff 34 0) ka);
      [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      rewrite Z.add_0_r. exact Mka.
  + apply pairwise_disjoint_of_extents. unfold gl_regions, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. cbn [base_val].
    rewrite E8, E9, E33, !unsigned_lit_small by lia.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    revert HSA0 HSA8 HSAC HSAZ Hhp0 Hhp8 HhpC HhpZ HDIS Hi0 Hi8. clear. intros.
    repeat split; lia.
  + split; [|split; [exact I|]].
    * cbn [gl_facts f_atoms atoms_ok]. unfold afact_ok, PTRF. cbn [af_lo af_hi af_al2].
      rewrite E8, E9, E19, E20, E21, E32, E33, E34, E35, !unsigned_lit_small by (unfold SB; lia).
      change (2 ^ 3) with 8. change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
      revert HSA0 HSA8 HSAC Hhp0 Hhp8 HhpC Hka0 Hka16 HkaC Hi0 Hi8 Hi26 Hnh. clear. unfold SB. intros.
      repeat match goal with |- _ /\ _ => split end; try lia.
      -- replace (SA + 48) with ((SA / 8 + 6) * 8) by (pose proof (Z.div_mod SA 8 ltac:(lia)); lia).
         apply Z_mod_mult.
      -- replace (SA + 40) with ((SA / 8 + 5) * 8) by (pose proof (Z.div_mod SA 8 ltac:(lia)); lia).
         apply Z_mod_mult.
      -- rewrite Z.mul_comm. apply Z_mod_mult.
      -- replace (hp + 8 * i) with ((hp / 8 + i) * 8) by (pose proof (Z.div_mod hp 8 ltac:(lia)); lia).
         apply Z_mod_mult.
    * cbn [gl_facts f_alias alias_ok]. split; [|exact I].
      apply U_inj. rewrite U_SAlu. cbn [zalu_raw].
      rewrite (U_atom E 32 hp E32), (U_atom E 20 (8 * i) E20), (U_atom E 33 (hp + 8 * i) E33) by lia.
      apply zcanon_id. unfold M64. lia.
- assert (HBx : U E BxL = SHADOW_OFF)
    by (unfold BxL; rewrite (U_atom E 19 SB E19) by (unfold SB; lia); reflexivity).
  unfold sh_ok, gl_SH. constructor; [|constructor; [|constructor; [|constructor]]].
  + apply (shent_ok_of_range SEGS (w_H Wc) memc E BxL 9 (SA + 40) 16 (SA + 40) 0 8 RA1 HBx);
    [rewrite (U_atom E 9 (SA + 40) E9) by lia; reflexivity | lia | lia |].
    intros x Hx. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia.
  + apply (shent_ok_of_range SEGS (w_H Wc) memc E BxL 8 (SA + 40) 16 (SA + 48) 0 8 RA1 HBx);
    [rewrite (U_atom E 8 (SA + 48) E8) by lia; reflexivity | lia | lia |].
    intros x Hx. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia.
  + apply (shent_ok_of_range SEGS (w_H Wc) memc E BxL 33 (hp + 8 * i) 8 (hp + 8 * i) 0 8 RA2 HBx);
    [rewrite (U_atom E 33 (hp + 8 * i) E33) by lia; reflexivity | lia | lia |].
    intros x Hx. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia.
Qed.

(* the runs of the loop body write nothing: every region of ss_gl has an empty write window *)
Ltac gll_outw :=
let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
intros (r & Hin & Hr); cbn [ss_mem add_cond In] in Hin;
repeat (destruct Hin as [<- | Hin];
[ cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hr; lia | ]);
destruct Hin.

(* ------------------------------------------------------------------ the loop *)
Lemma gll_loop_x : forall (d : nat) W ly S0 Hp regs mem md ch SA TB e c O mx no cap out rest (i : nat)
  Wc lyc Sc Hpk regsc memc mdc k outi (kr : nat),
(length (re_keys e) - i <= d)%nat ->
gse_pre_x B ARx MT RP MMAX RG W ly S0 Hp regs mem md ch SA TB e c O mx no cap out rest kr ->
(i < length (re_keys e))%nat ->
gse_inv_x B PST ARx MT RP MMAX RG W ly S0 Hp regs mem md SA TB e c O mx no cap out rest i Wc lyc Sc Hpk regsc memc mdc k
  outi kr ->
getr regsc 20 = w64 (8 * Z.of_nat i) -> getr regsc 21 = w64 (Z.of_nat i) ->
getr regsc 22 = w64 ((SA + 40) / 8 + SB) -> getr regsc 23 = w64 3 ->
SRr SEGS Wc (mkCfg (mkst regsc (Z_to_bv 64 (BASE + A_gse_loop)) memc (seg_rom SEGS)) mdc)
  (gse_post_x B PST ARx MT RP RG regs ly S0 Hp W mem md SA TB e c O mx no cap out rest kr).
Proof.
induction d as [|d IH]; intros W ly S0 Hp regs mem md ch SA TB e c O mx no cap out rest i
  Wc lyc Sc Hpk regsc memc mdc k outi kr Hd HPREB Hilt HINV R20 R21 R22 R23; [lia|].
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : GSE_STK = 16608) by reflexivity. assert (WG : GE_STK = 16528) by reflexivity.
assert (ER1 : A_gse_ret1 = 764) by (vm_compute; reflexivity).
assert (ER2 : A_gse_ret2 = 804) by (vm_compute; reflexivity).
assert (EAT : A_gse_tail = 844) by (vm_compute; reflexivity).
pose proof HPREB as (HPRE & H10 & HinTB & HT1 & HT2 & HSA8 & HEB0 & HAW0 & HHELD & HOUT0 & HPERM0 & G50 & HROM0 & ROOM0 & MOK0
  & RM0 & CNT0).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (HLO : alloc_ceiling + GSE_STK <= spZ regs) by lia.
unfold gse_inv_x in HINV. cbv zeta in HINV.
destruct HINV as (HJ & HPK & HML & HMOK & HRM & HROOM & HPERM & HOUT & HEB & HAW & GHP & FKEYS & G5 & HROM & HSP
  & R3 & R4 & R8 & R9 & R18 & R19 & R2427 & SL1 & SL8 & SL9 & SL18 & SL19 & SL20 & SL21 & SL22 & SL23).
(* the block list at the loop head in the cut's form, for the room round's counts (gse_cnt_at) *)
pose proof HPERM as HPERMi.
assert (HARc : ARx lyc Sc Hpk Wc memc mdc) by (eapply ajournal_gx_AR_x; exact HJ).
destruct HHELD as (Hp1 & Hp2 & Hnh26 & HHP & HNDa & HNDt & FK0).
(* the key at index i *)
destruct (nth_error (re_keys e) i) as [ki|] eqn:Eki;
  [|exfalso; apply nth_error_None in Eki; lia].
pose proof (gll_skipn_S _ (re_keys e) i ki Eki) as ESK.
assert (Exs : nth_error (gse_keys e) i = Some (key_text ki)) by (unfold gse_keys; apply map_nth_error; exact Eki).
pose proof (gll_skipn_S _ (gse_keys e) i (key_text ki) Exs) as ESX.
pose proof (gll_firstn_S _ (gse_keys e) i (key_text ki) Exs) as EFX.
(* the held array is a live block (the key list is not empty) *)
destruct HHP as [(Hz & Hke) | (Hnz & HinHP0 & Hkh & Hkh8 & GHP0)]; [rewrite Hke in Hilt; cbn in Hilt; lia|].
rewrite ESK in FKEYS. inversion FKEYS as [|k0 ks0 KOKi FKREST Heqf]; subst k0 ks0.
destruct KOKi as (GKEY & KNZ & KLEN).
set (L := Z.of_nat (length (key_text ki))) in *.
set (ka := key_addr ki) in *.
set (hp := re_hp e) in *. set (kh := re_kh e) in *.
set (r0 := gse_run c O mx no cap (firstn i (gse_keys e))) in *.
set (KS := kblks (skipn (S i) (re_keys e))) in *.
set (OB := aout_blks (gse_cap r0) outi) in *.
(* the block list at the loop head *)
rewrite ESK in HPERM. rewrite gll_kblks_cons in HPERM.
unfold gse_hpblk in HPERM. rewrite (proj2 (Z.eqb_neq hp 0) Hnz) in HPERM. cbn [app] in HPERM.
fold L in HPERM. fold ka in HPERM. fold KS in HPERM.
assert (HinTBc : In (TB, ATABLE) (ablocks B lyc Sc))
  by (eapply Permutation_in; [apply Permutation_sym; exact HPERM | left; reflexivity]).
assert (HinHPc : In (hp, kh) (ablocks B lyc Sc))
  by (eapply Permutation_in; [apply Permutation_sym; exact HPERM | right; left; reflexivity]).
assert (HinKAc : In (ka, L + 1) (ablocks B lyc Sc))
  by (eapply Permutation_in; [apply Permutation_sym; exact HPERM | right; right; left; reflexivity]).
assert (HinKSc : forall bb, In bb KS -> In bb (ablocks B lyc Sc)).
{ intros bb Hbb. eapply Permutation_in; [apply Permutation_sym; exact HPERM|].
  right; right; right. apply in_or_app. left. exact Hbb. }
assert (HinOBc : forall bb, In bb OB -> In bb (ablocks B lyc Sc)).
{ intros bb Hbb. eapply Permutation_in; [apply Permutation_sym; exact HPERM|].
  right; right; right. apply in_or_app. right. apply in_or_app. left. exact Hbb. }
(* distinctness, from NoDup of the live blocks *)
pose proof (gse_nodup_x B ARx LAWS BLKN lyc Sc Hpk Wc memc mdc HARc) as ND.
apply (Permutation_NoDup HPERM) in ND.
inversion ND as [|? ? NI_TB ND1].
inversion ND1 as [|? ? NI_HP ND2].
inversion ND2 as [|? ? NI_KA ND3].
assert (NI_KS' : forall bb, In bb KS -> ~ In bb OB).
{ intros bb Hbb Hcc. apply (gll_nodup_app _ KS (OB ++ rest) ND3 bb Hbb). apply in_or_app. left. exact Hcc. }
assert (DTB : (TB, ATABLE) <> (ka, L + 1)) by (intros Hcc; apply NI_TB; right; left; exact (eq_sym Hcc)).
assert (DHP : (hp, kh) <> (ka, L + 1)) by (intros Hcc; apply NI_HP; left; exact (eq_sym Hcc)).
assert (DKS : forall bb, In bb KS -> bb <> (ka, L + 1)).
{ intros bb Hbb Hcc. apply NI_KA. apply in_or_app. left. rewrite <- Hcc. exact Hbb. }
(* numeric facts on the three blocks *)
destruct (alx_blocks _ _ _ LAWS lyc Sc Hpk Wc memc mdc TB ATABLE HARc HinTBc) as (HTB16 & HTB4 & HTBc & HTBa & _ & _).
destruct (alx_blocks _ _ _ LAWS lyc Sc Hpk Wc memc mdc hp kh HARc HinHPc) as (HHP16 & HHP4 & HHPc & HHPa & _ & _).
destruct (alx_blocks _ _ _ LAWS lyc Sc Hpk Wc memc mdc ka (L + 1) HARc HinKAc) as (HKA16 & HKA4 & HKAc & HKAa & _ & _).
change (req_size ATABLE) with 896 in HTBc, HTBa.
assert (HRKH : req_size kh = kh) by (unfold req_size; destruct (Z.eqb_spec kh 0); lia).
assert (HRKA : req_size (L + 1) = L + 1) by (unfold req_size; destruct (Z.eqb_spec (L + 1) 0); lia).
rewrite HRKH in HHPc, HHPa. rewrite HRKA in HKAc, HKAa.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HTBa, HHPa, HKAa.
assert (RSA : 4096 <= SA /\ SA + 56 <= TB + 896 /\ SA + 56 <= alloc_ceiling /\ SA + 56 <= 140737479966720)
  by (unfold AENT, ATABLE in *; lia).
destruct RSA as (RSA0 & RSA1 & RSA2 & RSA3).
assert (HiN : Z.of_nat i < re_nheld e) by (unfold re_nheld; lia).
assert (Hi8L : 8 * Z.of_nat i + 8 <= kh) by (unfold re_nheld in Hkh; lia).
(* the held slot and the entry's two fields, as the seat needs them *)
pose proof HEB as HEB2. rewrite gse_entry_split in HEB2. unfold bzs in HEB2. rewrite !map_app in HEB2.
apply garr8_app in HEB2 as [_ HEB2]. rewrite length_map, (gse_epre_len e Hp1) in HEB2.
apply garr8_app in HEB2 as [Ghp HEB2]. apply garr8_app in HEB2 as [Gnh _].
rewrite length_map, OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.length_le8 in Gnh.
change (SA + Z.of_nat 40) with (SA + 40) in Ghp, Gnh. replace (SA + 40 + Z.of_nat 8) with (SA + 48) in Gnh by lia.
assert (Mhp : val_mem SEGS (arm Wc memc) (SA + 40) 8 hp).
{ apply gse_garr8_le; [|lia].
  unfold OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.le8, word_to_le_bytes in Ghp.
  rewrite unsigned_lit_small in Ghp by lia. exact Ghp. }
assert (Mnh : val_mem SEGS (arm Wc memc) (SA + 48) 4 (re_nheld e)).
{ apply gse_garr8_le; [|unfold re_nheld in *; lia].
  unfold OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.le4 in Gnh.
  rewrite unsigned_lit_small in Gnh by (unfold re_nheld in *; lia). exact Gnh. }
assert (Mka : val_mem SEGS (arm Wc memc) (hp + 8 * Z.of_nat i) 8 ka).
{ exact (gse_key_ptr (arm Wc memc) hp (re_keys e) i ki GHP Eki ltac:(unfold ka; lia)). }
(* the two shadow ranges *)
assert (RA1 : range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF (SA + 40) 16).
{ apply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 lyc Sc Hpk Wc memc mdc TB ATABLE (SA + 40) 16 HARc HinTBc);
  change (req_size ATABLE) with 896; unfold AENT, ATABLE in *; lia. }
assert (RA2 : range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF (hp + 8 * Z.of_nat i) 8).
{ apply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 lyc Sc Hpk Wc memc mdc hp kh (hp + 8 * Z.of_nat i) 8 HARc
    HinHPc);
  [lia | rewrite HRKH; lia]. }
(* the table block and the held array are apart *)
assert (HDIS : hp + 8 * Z.of_nat i + 8 <= SA + 40 \/ SA + 52 <= hp + 8 * Z.of_nat i).
{ destruct (gll_disj_x lyc Sc Hpk Wc memc mdc TB ATABLE hp kh HARc HinTBc HinHPc
    ltac:(intros Hc; apply NI_TB; left; exact (eq_sym Hc)))
  as [Hdd | Hdd]; change (req_size ATABLE) with 896 in Hdd; rewrite ?HRKH in Hdd;
  unfold AENT, ATABLE in *; lia. }
destruct (gll_seat Wc regsc memc SA hp ka (re_nheld e) (Z.of_nat i)
  R8 R9 R18 R19 R20 R21 R22 ltac:(unfold AENT, ATABLE in *; lia) HSA8 ltac:(unfold AENT, ATABLE in *; lia)
  ltac:(unfold AENT, ATABLE in *; lia) HHP4 ltac:(pose proof (Z.div_mod hp 8 ltac:(lia)); pose proof (Z.div_mod hp 16 ltac:(lia));
    pose proof (Z.mod_pos_bound hp 8 ltac:(lia)); lia)
  ltac:(lia) ltac:(lia) HDIS HKA4 HKA16 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
  ltac:(unfold re_nheld in *; lia) Mhp Mnh Mka RA1 RA2) as [HS SHOK].
remember (Eimg (Ereg regsc (gl_extra hp (hp + 8 * Z.of_nat i) ka (re_nheld e)))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regsc (gl_extra hp (hp + 8 * Z.of_nat i) ka (re_nheld e))) E)
  by (rewrite HE; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E m = getr regsc rr).
{ intros m rr Hm. rewrite HE. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hm. }
assert (E2 : ew E 2 = getr regsc 2) by (exact (EEo 2%nat 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regsc 3) by (exact (EEo 3%nat 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regsc 4) by (exact (EEo 4%nat 4%bv eq_refl)).
assert (E8 : ew E 8 = Z_to_bv 64 (SA + 48)) by (rewrite (EEo 8%nat 8%bv eq_refl); exact R8).
assert (E9 : ew E 9 = Z_to_bv 64 (SA + 40)) by (rewrite (EEo 9%nat 9%bv eq_refl); exact R9).
assert (E19 : ew E 19 = Z_to_bv 64 SB) by (rewrite (EEo 19%nat 19%bv eq_refl); exact R19).
assert (E20 : ew E 20 = Z_to_bv 64 (8 * Z.of_nat i)) by (rewrite (EEo 20%nat 20%bv eq_refl); exact R20).
assert (E21 : ew E 21 = Z_to_bv 64 (Z.of_nat i)) by (rewrite (EEo 21%nat 21%bv eq_refl); exact R21).
assert (E33 : ew E 33 = Z_to_bv 64 (hp + 8 * Z.of_nat i))
  by (rewrite HE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsc _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 ka)
  by (rewrite HE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsc _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 (re_nheld e))
  by (rewrite HE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsc _ 3)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs - GSE_FRAME) by (rewrite E2; exact HSP).
clear HE.
(* ---- 0x825c0 -> gesture_end's entry *)
paj_run_to_tok_x RUNTO HS HJ SHOK Bspan AF_fr_gesture_end. { apply awr_ok_x_of0. awr_ok_tac. }
assert (KR1 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H Wc) (ms_mem ms) a = aview SEGS (w_H Wc) memc a).
{ intros a Ha. apply (aview_kept_out E _ (w_H Wc) memc (ms_mem ms) HFr a Ha). gll_outw. }
assert (PK1 : apres_kept B Wc memc Wc (ms_mem ms)).
{ apply gse_apres_grows. lazymatch goal with
  | K : mem_grows (mrestrict (w_H Wc) memc) (mrestrict (w_H Wc) (ms_mem ms)) |- _ => exact K end. }
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3.
prreg HS (4%bv : bv 5) P4. prreg HS (8%bv : bv 5) P8. prreg HS (10%bv : bv 5) P10.
pmkst HS.
(* ---- gesture_end (held[i]) *)
assert (ROOMi : ge_room MMAX (blocks_bytes Sc) (gse_c r0) mx (gse_no r0) (gse_cap r0) L /\
  gse_room MMAX (blocks_bytes Sc + tr_net (ge_tr (gse_c r0) mx (gse_no r0) (gse_cap r0) L) - (L + 1))
    (ge_ctl (gse_c r0) L) mx (ge_no (gse_c r0) (gse_no r0) L) (ge_cap (gse_c r0) mx (gse_no r0) (gse_cap r0) L)
    (skipn (S i) (gse_keys e))).
{ rewrite ESX in HROOM. cbn [gse_room] in HROOM. exact HROOM. }
destruct ROOMi as [ROOMi ROOMr].
assert (MOKi : mo_ok MT Sc (gse_cost MT (gse_c r0) mx (gse_no r0) (gse_cap r0)
  (key_text ki :: skipn (S i) (gse_keys e)))) by (rewrite <- ESX; exact HMOK).
cbn [gse_cost] in MOKi. fold L in MOKi.
destruct (gll_aout_facts lyc Sc Wc memc _ _ _ _ _ _ HOUT) as (Hmx & HnoO & Hblk).
assert (Hno0 : 0 <= gse_no r0) by lia.
assert (Hcap0 : 0 <= gse_cap r0) by (destruct Hblk; lia).
assert (HCRest : 0 <= gse_cost MT (ge_ctl (gse_c r0) L) mx (ge_no (gse_c r0) (gse_no r0) L)
  (ge_cap (gse_c r0) mx (gse_no r0) (gse_cap r0) L) (skipn (S i) (gse_keys e))).
{ apply (gll_cost_nonneg MT MTL); [lia | apply gll_ge_no_nonneg; lia | apply gll_ge_cap_nonneg; lia]. }
(* the room round: RM at the loop head carries this key's gesture_end, its free (MT_rk's mo_free is 1) and the calls
   after them; gesture_end is called with kr := 1 + krf, the free with kr := krf *)
assert (Hge_rk : 0 <= ge_cost MT_rk (gse_c r0) mx (gse_no r0) (gse_cap r0) L)
  by (apply (gll_ge_cost_nonneg MT_rk gse_rk_laws); lia).
assert (Hrest_rk : 0 <= gse_cost MT_rk (ge_ctl (gse_c r0) L) mx (ge_no (gse_c r0) (gse_no r0) L)
  (ge_cap (gse_c r0) mx (gse_no r0) (gse_cap r0) L) (skipn (S i) (gse_keys e)))
  by (apply (gll_cost_nonneg MT_rk gse_rk_laws); [lia | apply gll_ge_no_nonneg; lia | apply gll_ge_cap_nonneg; lia]).
pose (krf := (Z.to_nat (gse_cost MT_rk (ge_ctl (gse_c r0) L) mx (ge_no (gse_c r0) (gse_no r0) L)
  (ge_cap (gse_c r0) mx (gse_no r0) (gse_cap r0) L) (skipn (S i) (gse_keys e))) + kr)%nat).
assert (RMi : rp_RM RP Sc (Z.to_nat (ge_cost MT_rk (gse_c r0) mx (gse_no r0) (gse_cap r0) L) + (1 + krf))).
{ assert (EQ : (Z.to_nat (gse_cost MT_rk (gse_c r0) mx (gse_no r0) (gse_cap r0) (skipn i (gse_keys e))) + kr =
    Z.to_nat (ge_cost MT_rk (gse_c r0) mx (gse_no r0) (gse_cap r0) L) + (1 + krf))%nat).
  { rewrite ESX. cbn [gse_cost]. fold L. unfold krf. change (mo_free MT_rk) with 1. lia. }
  rewrite <- EQ. exact HRM. }
pose proof (mo_free_nonneg MT MTL) as HMF.
assert (MOKge : mo_ok MT Sc (ge_cost MT (gse_c r0) mx (gse_no r0) (gse_cap r0) L))
  by (apply (mo_ok_le MT MTL Sc _ _ MOKi); lia).
assert (HKAout : ka <> outi).
{ destruct Hblk as [(Hc0 & Ho0 & _) | (Hc0 & _ & Hin)]; [lia|].
  assert (HinOB : In (outi, gse_cap r0) OB)
    by (unfold OB, aout_blks; rewrite (proj2 (Z.eqb_neq (gse_cap r0) 0) ltac:(lia)); left; reflexivity).
  assert (Hne : (ka, L + 1) <> (outi, gse_cap r0))
    by (intros Hc; apply NI_KA; rewrite Hc; apply in_or_app; right; apply in_or_app; left; exact HinOB).
  pose proof (req_size_pos (gse_cap r0) ltac:(lia)) as [Hq1 _].
  destruct (gll_disj_x lyc Sc Hpk Wc memc mdc ka (L + 1) outi (gse_cap r0) HARc HinKAc (HinOBc _ HinOB) Hne)
    as [Hd1 | Hd1];
  rewrite ?HRKA in Hd1; lia. }
eapply SRr_bind.
{ eapply (gll_ge_x Wc (ms_regs ms) (ms_mem ms) _ GSE_STK (spZ regs) (gse_FP SA e cap out) ly S0 Hp W mem md [] lyc Sc Hpk k
    (Z_to_bv 64 (BASE + A_gse_ret1)) (gse_c r0) (gse_O r0) mx (gse_no r0) (gse_cap r0) outi
    (key_text ki) ka (L + 1) (1 + krf)%nat HJ).
  - change (spZ (ms_regs ms)) with (bv_unsigned (getr (ms_regs ms) 2)). rewrite P2, Usp. unfold GSE_FRAME. lia.
  - lia.
  - rewrite P3, E3, R3. exact Hgp.
  - rewrite P4, E4, R4. exact Htp.
  - rewrite ER1. exact P1.
  - rewrite ER1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite ER1, unsigned_lit_small by lia. lia.
  - unfold s0Z. rewrite P8, E8.
    rewrite unsigned_lit_small by (unfold AENT, ATABLE in *; lia). unfold AENT, ATABLE in *. lia.
  - rewrite P10, E34. reflexivity.
  - apply (gll_aout_kept lyc Sc Wc memc lyc Sc Wc (ms_mem ms) _ _ _ _ _ _ HOUT);
    [intros rr a Hrr Ha; apply KR1; destruct (gll_aout_rom_x lyc Sc Hpk Wc memc mdc _ _ _ _ _ _ HARc HOUT rr a Hrr Ha); lia
    | exact (gll_aout_rom_x lyc Sc Hpk Wc memc mdc _ _ _ _ _ _ HARc HOUT)
    | intros bb Hbb; exact (HinOBc bb Hbb)].
  - apply (gse_garr8_kept (w_H Wc) (w_H Wc) memc (ms_mem ms) ka _ GKEY).
    intros b Hb. unfold bzs in Hb. rewrite length_map, length_app in Hb. cbn [length] in Hb. apply KR1. lia.
  - exact KNZ.
  - exact KLEN.
  - exact HinKAc.
  - exact HKAout.
  - rewrite HRKA. lia.
  - apply (gse_garr8_kept (w_H Wc) (w_H Wc) memc (ms_mem ms) _ _ G5).
    intros b Hb. change (Z.of_nat (length (bzs END5))) with 5 in Hb.
    pose proof (pa_img_range _ (HEND5I b ltac:(lia))). apply KR1. lia.
  - intros a Hin'.
    assert (HI : 0x10000 <= a < 0x5fb000)
      by (destruct Hin' as (sg & Hsg & _ & Hr'); exact (pa_img_range a ltac:(exists sg; split; [exact Hsg | exact Hr']))).
    rewrite KR1 by lia. exact (HROM a Hin').
  - exact ROOMi.
  - exact MOKge.
  - exact RMi.
  - (* the room round: gesture_end's count premise, from the entry's (gse_cnt_at; the peaks are read off the premises) *)
    eapply (gse_cnt_at RP _ _ e (ablocks B ly S0) (ablocks B lyc Sc) TB i cap out (gse_cap r0) outi rest);
    [| exact HPERM0 | exact HPERMi | exact CNT0]; intros P; cbv [ge_pk gse_pk]; lia.
  - (* the out block's footprint is the caller's, or a block the caller never had *)
    intros a Ha. apply inFP_ablocks_fp_inv in Ha as (p & n & Hpin & Hpa).
    assert (Hpc : In (p, n) (ablocks B lyc Sc)) by (exact (HinOBc (p, n) Hpin)).
    assert (DEC : forall u v : Z * Z, {u = v} + {u <> v}) by (decide equality; apply Z.eq_dec).
    destruct (in_dec DEC (p, n) (ablocks B ly S0)) as [IN0 | NIN0].
    + left. split; [|exists p, n; split; [exact Hpc | exact Hpa]].
      apply (Permutation_in _ HPERM0) in IN0.
      destruct IN0 as [IN0 | IN0].
      * exfalso. injection IN0 as <- <-. apply NI_TB.
        right. right. apply in_or_app. right. apply in_or_app. left. exact Hpin.
      * apply in_app_or in IN0 as [IN0 | IN0].
        { unfold gse_FP. apply (proj2 (inFP_cons _ _ _ _)). right.
          replace a with (p + (a - p)) by lia.
          apply (inFP_ablocks_fp (gse_blks e ++ aout_blks cap out) p n (a - p));
          [apply in_or_app; left; exact IN0 | lia]. }
        apply in_app_or in IN0 as [IN0 | IN0].
        { unfold gse_FP. apply (proj2 (inFP_cons _ _ _ _)). right.
          replace a with (p + (a - p)) by lia.
          apply (inFP_ablocks_fp (gse_blks e ++ aout_blks cap out) p n (a - p));
          [apply in_or_app; right; exact IN0 | lia]. }
        exfalso. apply (gll_nodup_app _ (KS ++ OB) rest ltac:(rewrite <- app_assoc; exact ND3) (p, n));
        [apply in_or_app; right; exact Hpin | exact IN0].
    + right. exists p, n. split; [exact Hpc | split; [exact NIN0 | exact Hpa]]. }
cbv beta. intros W2 c2 Hwle2
  (ly2 & S2 & Hg2 & regs2 & mem2 & md2 & k1 & out2 & -> & HJ2 & HJc2 & HP2 & HAK2 & HM2 & HRM2 & (R1 & HPa & HPb) & HO2).
assert (HAR2 : ARx ly2 S2 Hg2 W2 mem2 md2) by (eapply ajournal_gx_AR_x; exact HJ2).
fold L in HM2. fold L in HPb. fold L in HO2.
set (cap2 := ge_cap (gse_c r0) mx (gse_no r0) (gse_cap r0) L) in *.
set (OB2 := aout_blks cap2 out2) in *.
(* the blocks the call kept *)
assert (KEEPB : forall bb, In bb (ablocks B lyc Sc) -> ~ In bb OB -> In bb (ablocks B ly2 S2)).
{ intros bb Hb Hnb. assert (Hb1 : In bb (OB ++ R1)) by (eapply Permutation_in; [exact HPa | exact Hb]).
  apply in_app_or in Hb1 as [Hb1 | Hb1]; [exfalso; exact (Hnb Hb1)|].
  eapply Permutation_in; [apply Permutation_sym; exact HPb|]. apply in_or_app. right. exact Hb1. }
assert (NI_OB : forall bb, In bb OB -> ~ In bb R1).
{ intros bb Hbb. apply (gll_nodup_app _ OB R1); [|exact Hbb].
  apply (Permutation_NoDup HPa). exact (gse_nodup_x B ARx LAWS BLKN lyc Sc Hpk Wc memc mdc HARc). }
assert (NI_OB2 : forall bb, In bb OB2 -> ~ In bb R1).
{ intros bb Hbb. apply (gll_nodup_app _ OB2 R1); [|exact Hbb].
  apply (Permutation_NoDup HPb). exact (gse_nodup_x B ARx LAWS BLKN ly2 S2 Hg2 W2 mem2 md2 HAR2). }
assert (HR1 : Permutation R1 ((TB, ATABLE) :: (hp, kh) :: (ka, L + 1) :: KS ++ rest)).
{ apply (Permutation_app_inv_l OB). eapply perm_trans; [apply Permutation_sym; exact HPa|].
  eapply perm_trans; [exact HPERM|].
  change ((TB, ATABLE) :: (hp, kh) :: (ka, L + 1) :: KS ++ OB ++ rest)
    with (((TB, ATABLE) :: (hp, kh) :: (ka, L + 1) :: KS) ++ OB ++ rest).
  apply gll_swap_app. }
assert (HinTB2 : In (TB, ATABLE) (ablocks B ly2 S2))
  by (apply KEEPB; [exact HinTBc | intros Hc; apply (NI_OB _ Hc); apply (Permutation_in _ (Permutation_sym HR1)); left; reflexivity]).
assert (HinHP2 : In (hp, kh) (ablocks B ly2 S2))
  by (apply KEEPB; [exact HinHPc | intros Hc; apply (NI_OB _ Hc); apply (Permutation_in _ (Permutation_sym HR1)); right; left; reflexivity]).
assert (HinKA2 : In (ka, L + 1) (ablocks B ly2 S2))
  by (apply KEEPB; [exact HinKAc | intros Hc; apply (NI_OB _ Hc); apply (Permutation_in _ (Permutation_sym HR1)); right; right; left; reflexivity]).
assert (HinKS2 : forall bb, In bb KS -> In bb (ablocks B ly2 S2)).
{ intros bb Hbb. apply KEEPB; [exact (HinKSc bb Hbb)|]. intros Hc. apply (NI_OB _ Hc).
  apply (Permutation_in _ (Permutation_sym HR1)). right; right; right. apply in_or_app. left. exact Hbb. }
(* nothing of the caller's data is inside the out block the callee used *)
assert (NFP1 : forall p n a, In (p, n) (ablocks B lyc Sc) -> ~ In (p, n) OB -> p <= a < p + req_size n ->
  ~ inFP (ablocks_fp OB) a).
{ intros p n a Hpc Hnb Hpa Hc. apply inFP_ablocks_fp_inv in Hc as (q & m & Hqin & Hqa).
  assert (Hqc : In (q, m) (ablocks B lyc Sc)) by (exact (HinOBc (q, m) Hqin)).
  assert (Hne : (p, n) <> (q, m)) by (intros Hcc; injection Hcc as <- <-; exact (Hnb Hqin)).
  destruct (gll_disj_x lyc Sc Hpk Wc memc mdc p n q m HARc Hpc Hqc Hne); lia. }
assert (NI_TB' : ~ In (TB, ATABLE) OB)
  by (intros Hc; apply (NI_OB _ Hc); apply (Permutation_in _ (Permutation_sym HR1)); left; reflexivity).
assert (NI_HP' : ~ In (hp, kh) OB)
  by (intros Hc; apply (NI_OB _ Hc); apply (Permutation_in _ (Permutation_sym HR1)); right; left; reflexivity).
assert (NI_KA' : ~ In (ka, L + 1) OB)
  by (intros Hc; apply (NI_OB _ Hc); apply (Permutation_in _ (Permutation_sym HR1)); right; right; left; reflexivity).
(* the bytes the gesture_end call kept *)
assert (KGE : forall p n j, In (p, n) (ablocks B lyc Sc) -> In (p, n) (ablocks B ly2 S2) -> ~ In (p, n) OB ->
  0 <= j < req_size n -> aview SEGS (w_H W2) mem2 (p + j) = aview SEGS (w_H Wc) (ms_mem ms) (p + j)).
{ intros p n j Hb1 Hb2 Hb3 Hj.
  apply (gse_keep_blk_x B PST ARx LAWS IMGC BLKN (G_SL B RG) 0 [] GE_STK (spZ regs + -80) (ablocks_fp OB)
    lyc Sc Hpk Wc (ms_mem ms) mdc [] ly2 S2 Hg2 W2 mem2 md2 k1 p n j HG HJc2 Hb1 Hb2 Hj).
  exact (NFP1 p n (p + j) Hb1 Hb3 ltac:(lia)). }
assert (KGEa : forall p n a, In (p, n) (ablocks B lyc Sc) -> In (p, n) (ablocks B ly2 S2) -> ~ In (p, n) OB ->
  p <= a < p + req_size n -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H Wc) (ms_mem ms) a).
{ intros p n a Hb1 Hb2 Hb3 Ha. replace a with (p + (a - p)) by lia. apply (KGE p n (a - p)); [exact Hb1 | exact Hb2 | exact Hb3 | lia]. }
assert (KGEi : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) ->
  ~ (as_errno B <= a < as_errno B + 4) -> ~ Exists (in_zr a) PST -> ~ inG (G_SL B RG) a ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H Wc) (ms_mem ms) a).
{ intros a Hi Ho He Hq Hng.
  apply (gse_keep_img_x B PST ARx (G_SL B RG) 0 [] GE_STK (spZ regs + -80) (ablocks_fp OB) lyc Sc Hpk Wc (ms_mem ms) mdc
    [] ly2 S2 Hg2 W2 mem2 md2 k1 HJc2 a Hi Ho He Hq); [|exact Hng].
  apply gse_fp_spares. intros bb Hbb. destruct bb as [bp bn]. cbn [fst].
  destruct (alx_blocks _ _ _ LAWS lyc Sc Hpk Wc memc mdc bp bn HARc (HinOBc (bp, bn) Hbb)) as (_ & Hb4 & _). exact Hb4. }
assert (KGEh : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (spZ regs - 80 - GE_STK <= a < spZ regs - 80) ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H Wc) (ms_mem ms) a).
{ intros a Ha Hno.
  apply (gse_keep_high_x B PST ARx (G_SL B RG) 0 [] GE_STK (spZ regs + -80) (ablocks_fp OB) lyc Sc Hpk Wc (ms_mem ms) mdc
    [] ly2 S2 Hg2 W2 mem2 md2 k1 HG HJc2 a Ha ltac:(lia)). }
(* ---- back at 0x825e8: the two checks again, then free (held[i]) *)
jafter_call_keep_pi HS 36%nat regs2 (mrestrict (w_H W2) mem2) HP2 [0; 1; 2]%nat HS2.
match type of HS2 with ?ty -> _ => assert (HRK : ty); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| | | apply Forall_nil];
  split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; intros a Ha; try lia.
  - rewrite E9, unsigned_lit_small in Ha by lia. apply (mbyte_of_aview SEGS).
    apply (KGEa TB ATABLE a HinTBc HinTB2 NI_TB'). change (req_size ATABLE) with 896. unfold AENT, ATABLE in *. lia.
  - rewrite E8, unsigned_lit_small in Ha by lia. apply (mbyte_of_aview SEGS).
    apply (KGEa TB ATABLE a HinTBc HinTB2 NI_TB'). change (req_size ATABLE) with 896. unfold AENT, ATABLE in *. lia.
  - rewrite E33, unsigned_lit_small in Ha by lia. apply (mbyte_of_aview SEGS).
    apply (KGEa hp kh a HinHPc HinHP2 NI_HP'). rewrite HRKH. lia. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 36 (map (getr regs2) CLOB)) as Ea eqn:HEa in HS.
assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDa : forall n, (n < 36)%nat -> ew Ea n = ew E n) by (intros n Hn; rewrite HEa; apply YN3v.ew_havoc_old; exact Hn).
assert (HAEa : env_agree 32 (Ereg regsc (gl_extra hp (hp + 8 * Z.of_nat i) ka (re_nheld e))) Ea)
  by (rewrite HEa; apply env_agree_havoc_ge; [cbv; lia | exact HAE]).
clear HEa.
assert (SHOKa : sh_ok SEGS BxL gl_SH Ea (mrestrict (w_H W2) mem2)).
{ assert (HBxa : U Ea BxL = SHADOW_OFF)
    by (unfold BxL; rewrite (U_atom Ea 19 SB ltac:(rewrite OLDa by (cbv; lia); exact E19)) by (unfold SB; lia); reflexivity).
  unfold sh_ok, gl_SH. constructor; [|constructor; [|constructor; [|constructor]]].
  - apply (shent_ok_of_range SEGS (w_H W2) mem2 Ea BxL 9 (SA + 40) 16 (SA + 40) 0 8
      ltac:(apply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly2 S2 Hg2 W2 mem2 md2 TB ATABLE (SA + 40) 16 HAR2
          HinTB2);
        change (req_size ATABLE) with 896; unfold AENT, ATABLE in *; lia) HBxa);
    [rewrite (U_atom Ea 9 (SA + 40) ltac:(rewrite OLDa by (cbv; lia); exact E9)) by lia; reflexivity | lia | lia |].
    intros xx Hxx. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia.
  - apply (shent_ok_of_range SEGS (w_H W2) mem2 Ea BxL 8 (SA + 40) 16 (SA + 48) 0 8
      ltac:(apply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly2 S2 Hg2 W2 mem2 md2 TB ATABLE (SA + 40) 16 HAR2
          HinTB2);
        change (req_size ATABLE) with 896; unfold AENT, ATABLE in *; lia) HBxa);
    [rewrite (U_atom Ea 8 (SA + 48) ltac:(rewrite OLDa by (cbv; lia); exact E8)) by lia; reflexivity | lia | lia |].
    intros xx Hxx. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia.
  - apply (shent_ok_of_range SEGS (w_H W2) mem2 Ea BxL 33 (hp + 8 * Z.of_nat i) 8 (hp + 8 * Z.of_nat i) 0 8
      ltac:(apply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly2 S2 Hg2 W2 mem2 md2 hp kh (hp + 8 * Z.of_nat i) 8
          HAR2 HinHP2);
        [lia | rewrite HRKH; lia]) HBxa);
    [rewrite (U_atom Ea 33 (hp + 8 * Z.of_nat i)
       ltac:(rewrite OLDa by (cbv; lia); exact E33)) by lia; reflexivity | lia | lia |].
    intros xx Hxx. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia. }
paj_run_tok_x RUN HS HJ2 SHOKa Bspan. { apply awr_ok_x_of0. awr_ok_tac. }
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3.
prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8. prreg HS (10%bv : bv 5) Q10.
assert (KR2 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W2) (ms_mem ms0) a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha. apply (aview_kept_out Ea _ (w_H W2) mem2 (ms_mem ms0) HFr0 a Ha). gll_outw. }
assert (PK2 : apres_kept B W2 mem2 W2 (ms_mem ms0)).
{ apply gse_apres_grows. lazymatch goal with
  | K : mem_grows (mrestrict (w_H W2) mem2) (mrestrict (w_H W2) (ms_mem ms0)) |- _ => exact K end. }
pose proof HJ2 as HAR2b. apply ajournal_gx_AR_x in HAR2b.
(* the block list at the free: the key first, then what survives it *)
assert (PERMX : Permutation (ablocks B ly2 S2)
  ((ka, L + 1) :: ((TB, ATABLE) :: (hp, kh) :: KS ++ OB2 ++ rest))).
{ eapply perm_trans; [exact HPb|].
  eapply perm_trans; [apply Permutation_app_head; exact HR1|].
  eapply perm_trans; [apply Permutation_app_comm|]. cbn [app].
  eapply perm_trans;
  [apply perm_skip, perm_skip, perm_skip; rewrite <- app_assoc;
   apply Permutation_app_head, Permutation_app_comm|].
  eapply perm_trans; [apply perm_skip, perm_swap|]. apply perm_swap. }
(* the same block list in the cut's form, for the free's count (gse_cnt_at) *)
assert (PERMY : Permutation (ablocks B ly2 S2)
  ((TB, ATABLE) :: gse_hpblk hp kh ++ kblks (skipn i (re_keys e)) ++ OB2 ++ rest)).
{ rewrite ESK, gll_kblks_cons. unfold gse_hpblk. rewrite (proj2 (Z.eqb_neq hp 0) Hnz). cbn [app].
  fold ka. fold L. fold KS.
  eapply perm_trans; [exact PERMX|]. eapply perm_trans; [apply perm_swap|]. apply perm_skip. apply perm_swap. }
assert (MOKfree : mo_ok MT S2 (mo_free MT)).
{ apply (mo_ok_le MT MTL S2 _ (mo_free MT + gse_cost MT (ge_ctl (gse_c r0) L) mx (ge_no (gse_c r0) (gse_no r0) L)
    cap2 (skipn (S i) (gse_keys e)))); [|lia].
  apply (mo_ok_step MT MTL Sc S2 (ge_cost MT (gse_c r0) mx (gse_no r0) (gse_cap r0) L) _);
  [apply (mo_ok_le MT MTL Sc _ _ MOKi); lia | exact HM2]. }
pmkst HS. rewrite HBfree.
eapply SRr_bind.
{ eapply (gse_free_x B PST ARx MT RP LAWS CTX_AFREE AFREE AFREEN IMGC BLKN (G_SL B RG) W2 (ms_regs ms0) (ms_mem ms0) GSE_STK
    (spZ regs) (gse_FP SA e cap out) ly S0 Hp W mem md [] ly2 S2 Hg2 _ (k + k1) ka (L + 1)
    ((TB, ATABLE) :: (hp, kh) :: KS ++ OB2 ++ rest) (-80) (Z_to_bv 64 (BASE + A_gse_ret2)) [] krf HJ2).
  - unfold gse_hpblk. rewrite (proj2 (Z.eqb_neq ka 0) ltac:(lia)). cbn [app]. exact PERMX.
  - rewrite Q10, OLDa by (cbv; lia). exact E34.
  - change (spZ (ms_regs ms0)) with (bv_unsigned (getr (ms_regs ms0) 2)).
    rewrite Q2, OLDa by (cbv; lia). rewrite Usp. unfold GSE_FRAME. lia.
  - reflexivity.
  - lia.
  - unfold ASTACK. lia.
  - rewrite Q3, OLDa by (cbv; lia). rewrite E3, R3. exact Hgp.
  - rewrite Q4, OLDa by (cbv; lia). rewrite E4, R4. exact Htp.
  - rewrite ER2. exact Q1.
  - rewrite ER2. apply ret_ok_codeptr_v; [lia | reflexivity].
  - eapply (achain_chain_pre ly2 _ (spZ (ms_regs ms0)) (s0Z (ms_regs ms0)) []).
    + apply achain_low. unfold s0Z. rewrite Q8, OLDa by (cbv; lia). rewrite E8.
      rewrite unsigned_lit_small by lia. lia.
    + change (spZ (ms_regs ms0)) with (bv_unsigned (getr (ms_regs ms0) 2)).
      rewrite Q2, OLDa by (cbv; lia). rewrite Usp. unfold GSE_FRAME. lia.
    + reflexivity.
    + unfold raZ. rewrite Q1. rewrite unsigned_lit_small by lia. lia.
  - (* the free's caller context: the chain is [], the trace the singleton [gestures_end + 0xbc] (ra 0x82610) *)
    cbn [spine map]. replace (raZ (ms_regs ms0)) with (BASE + AF_fr_gestures_end + 0xbc); [exact HCTX_gse_loop|].
    unfold raZ. rewrite Q1, unsigned_lit_small by lia. first [lia | unfold AF_fr_gestures_end in *; lia].
  - exact HRM2.
  - (* the room round: the free's count, from the entry's *)
    unfold cnt_ok. eapply (gse_cnt_at RP _ _ e (ablocks B ly S0) (ablocks B ly2 S2) TB i cap out cap2 out2 rest);
    [| exact HPERM0 | exact PERMY | exact CNT0]; intros P; cbv [gse_pk]; lia.
  - intros _ j Hj. unfold gse_FP. apply (proj2 (inFP_cons _ _ _ _)). right.
    apply (inFP_ablocks_fp (gse_blks e ++ aout_blks cap out) ka (L + 1) j); [|exact Hj].
    apply in_or_app. left. rewrite gse_blks_split. apply in_or_app. right.
    exact (in_map (fun kk => (key_addr kk, Z.of_nat (length (key_text kk)) + 1)) (re_keys e) ki
      (nth_error_In _ _ Eki)).
  - exact MOKfree. }
cbv beta.
intros W3 c3 Hwle3 (ly3 & S3 & Hg3 & regs3 & mem3 & md3 & -> & HJ3 & HP3 & HPerm3 & HK3 & HM3 & HRM3 & HE3 & HPK3).
destruct HK3 as (HK3a & HK3b & HK3c & HK3d & HK3e & HK3f).
assert (HAR3 : ARx ly3 S3 Hg3 W3 mem3 md3) by (eapply ajournal_gx_AR_x; exact HJ3).
assert (KFR : forall p n a, In (p, n) (ablocks B ly2 S2) -> (p, n) <> (ka, L + 1) -> p <= a < p + req_size n ->
  aview SEGS (w_H W3) mem3 a = aview SEGS (w_H W2) (ms_mem ms0) a).
{ intros p n a Hq1 Hq2 Hqa. replace a with (p + (a - p)) by lia.
  apply (HK3b p n (a - p) Hq1 ltac:(lia)). intros (Hz & Hr).
  destruct (gll_disj_x ly2 S2 Hg2 W2 (ms_mem ms0) _ p n ka (L + 1) HAR2b Hq1 HinKA2 Hq2) as [Hdd | Hdd];
  rewrite ?HRKA in Hdd; lia. }
(* the bytes of a block that both calls kept, from the loop head to after the free *)
assert (KBLK : forall p n a, In (p, n) (ablocks B lyc Sc) -> ~ In (p, n) OB -> (p, n) <> (ka, L + 1) ->
  p <= a < p + req_size n -> aview SEGS (w_H W3) mem3 a = aview SEGS (w_H Wc) memc a).
{ intros p n a Hq1 Hq2 Hq3 Hqa.
  destruct (alx_blocks _ _ _ LAWS lyc Sc Hpk Wc memc mdc p n HARc Hq1) as (_ & Hq4 & Hqc & _).
  assert (Hq2' : In (p, n) (ablocks B ly2 S2)) by (apply KEEPB; [exact Hq1 | exact Hq2]).
  rewrite (KFR p n a Hq2' Hq3 Hqa), (KR2 a ltac:(lia)), (KGEa p n a Hq1 Hq2' Hq2 Hqa).
  apply KR1. lia. }
assert (KIMG : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) ->
  ~ (as_errno B <= a < as_errno B + 4) -> ~ Exists (in_zr a) PST -> ~ inG (G_SL B RG) a ->
  aview SEGS (w_H W3) mem3 a = aview SEGS (w_H Wc) memc a).
{ intros a Hi Ho He Hq Hng. pose proof (pa_img_range a Hi).
  rewrite (HK3c a Hi Ho He), (KR2 a ltac:(lia)), (KGEi a Hi Ho He Hq Hng). apply KR1. lia. }
assert (KHI : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (spZ regs - 80 - GE_STK <= a < spZ regs - 80) ->
  aview SEGS (w_H W3) mem3 a = aview SEGS (w_H Wc) memc a).
{ intros a Ha Hno.
  rewrite (HK3a a Ha ltac:(unfold ASTACK; lia)), (KR2 a ltac:(lia)), (KGEh a Ha Hno). apply KR1. lia. }
(* ---- back at 0x82610: nheld's load4 check, i++, 8i += 8, and the branch *)
assert (HinTB3 : In (TB, ATABLE) (ablocks B ly3 S3))
  by (eapply Permutation_in; [apply Permutation_sym; exact HPerm3 | left; reflexivity]).
assert (HinHP3 : In (hp, kh) (ablocks B ly3 S3))
  by (eapply Permutation_in; [apply Permutation_sym; exact HPerm3 | right; left; reflexivity]).
assert (HinKS3 : forall bb, In bb KS -> In bb (ablocks B ly3 S3)).
{ intros bb Hbb. eapply Permutation_in; [apply Permutation_sym; exact HPerm3|].
  right; right. apply in_or_app. left. exact Hbb. }
assert (HinOB3 : forall bb, In bb OB2 -> In bb (ablocks B ly3 S3)).
{ intros bb Hbb. eapply Permutation_in; [apply Permutation_sym; exact HPerm3|].
  right; right. apply in_or_app. right. apply in_or_app. left. exact Hbb. }
jafter_call_keep_pi HS 52%nat regs3 (mrestrict (w_H W3) mem3) HP3 [0; 1; 2]%nat HS3.
match type of HS3 with ?ty -> _ => assert (HRK : ty); [|specialize (HS3 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| | | apply Forall_nil];
  split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; intros a Ha; try lia.
  - rewrite OLDa in Ha by (cbv; lia). rewrite E9, unsigned_lit_small in Ha by lia.
    apply (mbyte_of_aview SEGS).
    apply (KFR TB ATABLE a HinTB2 DTB);
    change (req_size ATABLE) with 896; lia.
  - rewrite OLDa in Ha by (cbv; lia). rewrite E8, unsigned_lit_small in Ha by lia.
    apply (mbyte_of_aview SEGS).
    apply (KFR TB ATABLE a HinTB2 DTB);
    change (req_size ATABLE) with 896; lia.
  - rewrite OLDa in Ha by (cbv; lia). rewrite E33, unsigned_lit_small in Ha by lia.
    apply (mbyte_of_aview SEGS).
    apply (KFR hp kh a HinHP2 DHP); rewrite HRKH; lia. }
clear HS. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
remember (havoc Ea 52 (map (getr regs3) CLOB)) as Eb eqn:HEb in HS.
assert (HEIb : img_env VAL A_LIM Eb) by (rewrite HEb; apply img_env_havoc; [exact HEIa | cbv; lia]).
assert (OLDb : forall n, (n < 52)%nat -> ew Eb n = ew Ea n) by (intros n Hn; rewrite HEb; apply YN3v.ew_havoc_old; exact Hn).
assert (HAEb : env_agree 32 (Ereg regsc (gl_extra hp (hp + 8 * Z.of_nat i) ka (re_nheld e))) Eb)
  by (rewrite HEb; apply env_agree_havoc_ge; [cbv; lia | exact HAEa]).
clear HEb.
assert (F8 : ew Eb 8 = Z_to_bv 64 (SA + 48)) by (rewrite OLDb, OLDa by (cbv; lia); exact E8).
assert (F9 : ew Eb 9 = Z_to_bv 64 (SA + 40)) by (rewrite OLDb, OLDa by (cbv; lia); exact E9).
assert (F19 : ew Eb 19 = Z_to_bv 64 SB) by (rewrite OLDb, OLDa by (cbv; lia); exact E19).
assert (F20 : ew Eb 20 = Z_to_bv 64 (8 * Z.of_nat i)) by (rewrite OLDb, OLDa by (cbv; lia); exact E20).
assert (F21 : ew Eb 21 = Z_to_bv 64 (Z.of_nat i)) by (rewrite OLDb, OLDa by (cbv; lia); exact E21).
assert (F33 : ew Eb 33 = Z_to_bv 64 (hp + 8 * Z.of_nat i)) by (rewrite OLDb, OLDa by (cbv; lia); exact E33).
assert (F35 : ew Eb 35 = Z_to_bv 64 (re_nheld e)) by (rewrite OLDb, OLDa by (cbv; lia); exact E35).
assert (Uspb : bv_unsigned (ew Eb 2) = spZ regs - GSE_FRAME) by (rewrite OLDb, OLDa by (cbv; lia); exact Usp).
assert (SHOKb : sh_ok SEGS BxL gl_SH Eb (mrestrict (w_H W3) mem3)).
{ assert (HBxb : U Eb BxL = SHADOW_OFF)
    by (unfold BxL; rewrite (U_atom Eb 19 SB F19) by (unfold SB; lia); reflexivity).
  unfold sh_ok, gl_SH. constructor; [|constructor; [|constructor; [|constructor]]].
  - apply (shent_ok_of_range SEGS (w_H W3) mem3 Eb BxL 9 (SA + 40) 16 (SA + 40) 0 8
      ltac:(apply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly3 S3 Hg3 W3 mem3 md3 TB ATABLE (SA + 40) 16 HAR3
          HinTB3);
        change (req_size ATABLE) with 896; lia) HBxb);
    [rewrite (U_atom Eb 9 (SA + 40) F9) by lia; reflexivity | lia | lia |].
    intros xx Hxx. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia.
  - apply (shent_ok_of_range SEGS (w_H W3) mem3 Eb BxL 8 (SA + 40) 16 (SA + 48) 0 8
      ltac:(apply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly3 S3 Hg3 W3 mem3 md3 TB ATABLE (SA + 40) 16 HAR3
          HinTB3);
        change (req_size ATABLE) with 896; lia) HBxb);
    [rewrite (U_atom Eb 8 (SA + 48) F8) by lia; reflexivity | lia | lia |].
    intros xx Hxx. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia.
  - apply (shent_ok_of_range SEGS (w_H W3) mem3 Eb BxL 33 (hp + 8 * Z.of_nat i) 8 (hp + 8 * Z.of_nat i) 0 8
      ltac:(apply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly3 S3 Hg3 W3 mem3 md3 hp kh (hp + 8 * Z.of_nat i) 8
          HAR3 HinHP3);
        [lia | rewrite HRKH; lia]) HBxb);
    [rewrite (U_atom Eb 33 (hp + 8 * Z.of_nat i) F33) by lia; reflexivity | lia | lia |].
    intros xx Hxx. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia. }
paj_run_tok_x RUN HS HJ3 SHOKb Bspan. { apply awr_ok_x_of0. awr_ok_tac. }
assert (KR3 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W3) (ms_mem ms1) a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha. apply (aview_kept_out Eb _ (w_H W3) mem3 (ms_mem ms1) HFr1 a Ha). gll_outw. }
assert (PK3 : apres_kept B W3 mem3 W3 (ms_mem ms1)).
{ apply gse_apres_grows. lazymatch goal with
  | K : mem_grows (mrestrict (w_H W3) mem3) (mrestrict (w_H W3) (ms_mem ms1)) |- _ => exact K end. }
(* ---- the invariant at i + 1, from any memory the last run reaches *)
assert (LEB : length (bzs (entry_bytes e)) = 56%nat).
{ unfold bzs. rewrite length_map, gse_entry_split, !length_app, (gse_epre_len e Hp1).
  rewrite OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.length_le8,
    OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.length_le4, Hp2. reflexivity. }
pose proof (blk_off_imgP_x B ARx LAWS IMGC BLKN lyc Sc Hpk Wc memc mdc TB ATABLE HARc HinTBc) as HTBoff.
change (req_size ATABLE) with 896 in HTBoff. unfold off_img in HTBoff.
assert (ERC : gse_c (gse_run c O mx no cap (firstn (S i) (gse_keys e))) = ge_ctl (gse_c r0) L)
  by (rewrite (gll_firstn_S _ (gse_keys e) i (key_text ki) Exs),
      (gse_run_app (firstn i (gse_keys e)) [key_text ki] c O mx no cap); reflexivity).
assert (ERO : gse_O (gse_run c O mx no cap (firstn (S i) (gse_keys e))) = ge_O (gse_c r0) (gse_O r0) (key_text ki))
  by (rewrite (gll_firstn_S _ (gse_keys e) i (key_text ki) Exs),
      (gse_run_app (firstn i (gse_keys e)) [key_text ki] c O mx no cap); reflexivity).
assert (ERN : gse_no (gse_run c O mx no cap (firstn (S i) (gse_keys e))) = ge_no (gse_c r0) (gse_no r0) L)
  by (rewrite (gll_firstn_S _ (gse_keys e) i (key_text ki) Exs),
      (gse_run_app (firstn i (gse_keys e)) [key_text ki] c O mx no cap); reflexivity).
assert (ERP : gse_cap (gse_run c O mx no cap (firstn (S i) (gse_keys e))) = cap2)
  by (rewrite (gll_firstn_S _ (gse_keys e) i (key_text ki) Exs),
      (gse_run_app (firstn i (gse_keys e)) [key_text ki] c O mx no cap); reflexivity).
assert (ERS : gse_spent MT c mx no cap (firstn (S i) (gse_keys e)) =
  gse_spent MT c mx no cap (firstn i (gse_keys e)) +
  (ge_cost MT (gse_c r0) mx (gse_no r0) (gse_cap r0) L + mo_free MT + 0))
  by (rewrite (gll_firstn_S _ (gse_keys e) i (key_text ki) Exs),
      (gse_spent_app MT (firstn i (gse_keys e)) [key_text ki] c O mx no cap); reflexivity).
assert (BB : blocks_bytes S3 <= blocks_bytes Sc + tr_net (ge_tr (gse_c r0) mx (gse_no r0) (gse_cap r0) L) - (L + 1)).
{ assert (HGT : tr_net (ge_tr (gse_c r0) mx (gse_no r0) (gse_cap r0) L) = cap2 - gse_cap r0)
    by (apply ge_tr_net; lia).
  rewrite (blocks_bytes_bsum B lyc Sc), (blocks_bytes_bsum B ly3 S3).
  rewrite (bsum_perm _ _ HPerm3), (bsum_perm _ _ HPa).
  rewrite ?bsum_cons, ?bsum_app.
  rewrite (bsum_perm _ _ HR1), ?bsum_cons, ?bsum_app. cbn [snd].
  assert (HOBz : bsum (aout_blks (gse_cap r0) outi) = gse_cap r0).
  { unfold aout_blks. destruct (Z.eqb_spec (gse_cap r0) 0); cbn [bsum fold_right snd]; lia. }
  assert (HOB2z : bsum OB2 <= cap2).
  { unfold OB2, aout_blks. destruct (Z.eqb_spec cap2 0); cbn [bsum fold_right snd]; lia. }
  lia. }
assert (FIN : forall (regs4 : bvmap 5 word) mem4 md4 kk,
  (forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W3) mem4 a = aview SEGS (w_H W3) (ms_mem ms1) a) ->
  apres_kept B W3 (ms_mem ms1) W3 mem4 ->
  ajournal_gx_x SEGS B PST ARx (G_SL B RG) 0 [] GSE_STK (spZ regs) (gse_FP SA e cap out) ly S0 Hp W mem md []
    ly3 S3 Hg3 W3 mem4 md4 kk ->
  spZ regs4 = spZ regs - GSE_FRAME ->
  getr regs4 3 = getr regs 3 -> getr regs4 4 = getr regs 4 ->
  getr regs4 8 = w64 (SA + 48) -> getr regs4 9 = w64 (SA + 40) ->
  getr regs4 18 = w64 ((SA + 48) / 8 + SB) -> getr regs4 19 = w64 SB ->
  (forall rr, 24 <= rr <= 27 -> getr regs4 (Z_to_bv 5 rr) = getr regs (Z_to_bv 5 rr)) ->
  gse_inv_x B PST ARx MT RP MMAX RG W ly S0 Hp regs mem md SA TB e c O mx no cap out rest (S i) W3 ly3 S3 Hg3 regs4 mem4 md4
    kk out2 kr).
{ intros regs4 mem4 md4 kk KV4 PK4 HJ4 Hsp4 H34 H44 H84 H94 H184 H194 H2427.
  assert (KALL : forall p n a, In (p, n) (ablocks B lyc Sc) -> ~ In (p, n) OB -> (p, n) <> (ka, L + 1) ->
    p <= a < p + req_size n -> aview SEGS (w_H W3) mem4 a = aview SEGS (w_H Wc) memc a).
  { intros p n a Hq1 Hq2 Hq3 Hqa.
    destruct (alx_blocks _ _ _ LAWS lyc Sc Hpk Wc memc mdc p n HARc Hq1) as (_ & Hq4 & Hqc & _).
    rewrite (KV4 a ltac:(lia)), (KR3 a ltac:(lia)). exact (KBLK p n a Hq1 Hq2 Hq3 Hqa). }
  assert (KALLi : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) ->
    ~ (as_errno B <= a < as_errno B + 4) -> ~ Exists (in_zr a) PST -> ~ inG (G_SL B RG) a ->
    aview SEGS (w_H W3) mem4 a = aview SEGS (w_H Wc) memc a).
  { intros a Hi Ho He Hq Hng. pose proof (pa_img_range a Hi).
    rewrite (KV4 a ltac:(lia)), (KR3 a ltac:(lia)). exact (KIMG a Hi Ho He Hq Hng). }
  assert (GEB4 : garr8 SEGS (arm W3 mem4) SA (bzs (entry_bytes e))).
  { apply (gse_garr8_kept (w_H Wc) (w_H W3) memc mem4 SA _ HEB). intros b Hb. rewrite LEB in Hb.
    apply (KALL TB ATABLE b HinTBc NI_TB' DTB). change (req_size ATABLE) with 896. lia. }
  assert (AWR4 : awr W3 mem4 SA AENT).
  { intros j Hj. unfold AENT in Hj.
    destruct (aview SEGS (w_H W3) mem4 (SA + j)) as [v|] eqn:Ev.
    - apply (gse_writable_view (w_H W3) mem4 (SA + j) v ltac:(lia) Ev).
      intros Hrom.
      assert (Hi : in_img SEGS (SA + j))
        by (destruct Hrom as (sg & Hsg & _ & Hr'); exists sg; split; [exact Hsg | lia]).
      pose proof (pa_img_range (SA + j) Hi). lia.
    - exfalso. apply (gse_view_garr8 (w_H W3) mem4 SA _ j GEB4 ltac:(rewrite LEB; lia)).
      exact Ev. }
  assert (GHP4 : garr8 SEGS (arm W3 mem4) hp (bzs (key_ptrs (re_keys e)))).
  { apply (gse_garr8_kept (w_H Wc) (w_H W3) memc mem4 hp _ GHP). intros b Hb.
    unfold bzs in Hb. rewrite length_map, gse_key_ptrs_len in Hb.
    apply (KALL hp kh b HinHPc NI_HP' DHP). rewrite HRKH. unfold re_nheld in Hkh. lia. }
  assert (FK4 : Forall (key_ok W3 mem4) (skipn (S i) (re_keys e))).
  { rewrite Forall_forall in FKREST |- *. intros kk' Hkk'.
    destruct (FKREST kk' Hkk') as (GK' & NZ' & LN').
    assert (Hkb : In (key_addr kk', Z.of_nat (length (key_text kk')) + 1) KS)
      by (unfold KS, kblks; exact (in_map _ _ _ Hkk')).
    split; [|split; [exact NZ' | exact LN']].
    apply (gse_garr8_kept (w_H Wc) (w_H W3) memc mem4 (key_addr kk') _ GK'). intros b Hb.
    unfold bzs in Hb. rewrite length_map, length_app in Hb. cbn [length] in Hb.
    apply (KALL (key_addr kk') (Z.of_nat (length (key_text kk')) + 1) b (HinKSc _ Hkb) (NI_KS' _ Hkb) (DKS _ Hkb)).
    assert (HR : req_size (Z.of_nat (length (key_text kk')) + 1) = Z.of_nat (length (key_text kk')) + 1)
      by (unfold req_size; destruct (Z.eqb_spec (Z.of_nat (length (key_text kk')) + 1) 0); lia).
    rewrite HR. lia. }
  assert (G54 : garr8 SEGS (arm W3 mem4) (VAL A_lit_end5) (bzs END5)).
  { apply (gse_garr8_kept (w_H Wc) (w_H W3) memc mem4 _ _ G5). intros b Hb.
    change (Z.of_nat (length (bzs END5))) with 5 in Hb.
    destruct (HEND5G b Hb) as (Hng & Hno & Hne).
    exact (KALLi b (HEND5I b Hb) Hno Hne (HEND5P b Hb) Hng). }
  assert (SLOT : forall off v, val_mem SEGS (arm Wc memc) (spZ regs - off) 8 v -> 8 <= off <= 72 ->
    val_mem SEGS (arm W3 mem4) (spZ regs - off) 8 v).
  { intros off v Hv Hoff. apply (gse_vm_kept (w_H Wc) (w_H W3) memc mem4 _ 8 v Hv).
    intros b Hb. rewrite (KV4 b ltac:(lia)), (KR3 b ltac:(lia)).
    apply KHI; [lia | unfold GE_STK, GE_FRAME, SL_STK, SL_FRAME, ASTACK, ESTACK; lia]. }
  unfold gse_inv_x. cbv zeta. rewrite ERC, ERO, ERN, ERP, ERS.
  split; [exact HJ4|].
  split.
  { eapply gse_apres_trans; [exact HPK|]. eapply gse_apres_trans; [exact PK1|].
    eapply gse_apres_trans; [exact HAK2|]. eapply gse_apres_trans; [exact PK2|].
    eapply gse_apres_trans; [exact HPK3|]. eapply gse_apres_trans; [exact PK3 | exact PK4]. }
  split.
  { apply (mo_le_mono MT MTL S0 S3 _ _
      (mo_le_trans MT MTL S0 Sc S3 _ _ HML (mo_le_trans MT MTL Sc S2 S3 _ _ HM2 HM3))). lia. }
  split; [exact (mo_ok_step MT MTL Sc S3 _ _ MOKi (mo_le_trans MT MTL Sc S2 S3 _ _ HM2 HM3))|].
  split; [exact HRM3|].
  split; [exact (gll_room_mono _ _ (blocks_bytes Sc + tr_net (ge_tr (gse_c r0) mx (gse_no r0) (gse_cap r0) L) - (L + 1))
    _ _ _ _ BB ROOMr)|].
  split.
  { assert (EHB : gse_hpblk hp kh = [(hp, kh)])
      by (unfold gse_hpblk; rewrite (proj2 (Z.eqb_neq hp 0) Hnz); reflexivity).
    change (gse_hpblk (re_hp e) (re_kh e)) with (gse_hpblk hp kh). rewrite EHB. cbn [app]. exact HPerm3. }
  split.
  { apply (gll_aout_kept ly2 S2 W2 mem2 ly3 S3 W3 mem4 _ _ _ _ _ _ HO2).
    - intros rr a Hrr Ha.
      destruct (gll_aout_rom_x ly2 S2 Hg2 W2 mem2 md2 _ _ _ _ _ _ HAR2 HO2 rr a Hrr Ha) as [Ha64 Hrom].
      rewrite (KV4 a Ha64), (KR3 a Ha64).
      destruct (gse_aout_fp_cases B RG cap2 out2 rr Hrr) as [Hcs | (Hcs & ->)].
      + destruct (Z_le_gt_dec (as_errno B) a) as [Ee1 | Ee1];
        [destruct (Z_lt_ge_dec a (as_errno B + 4)) as [Ee2 | Ee2]|].
        * pose proof (HE3 (a - as_errno B) ltac:(lia)) as HEx.
          replace (as_errno B + (a - as_errno B)) with a in HEx by lia.
          rewrite HEx. apply KR2. exact Ha64.
        * destruct (HOUTG rr a Hcs Ha ltac:(lia)) as (Hi & _ & Ho).
          rewrite (HK3c a Hi Ho ltac:(lia)). apply KR2. exact Ha64.
        * destruct (HOUTG rr a Hcs Ha ltac:(lia)) as (Hi & _ & Ho).
          rewrite (HK3c a Hi Ho ltac:(lia)). apply KR2. exact Ha64.
      + cbn [fst snd] in Ha.
        destruct (gll_aout_facts ly2 S2 W2 mem2 _ _ _ _ _ _ HO2) as (_ & _ & [(Hz & _) | (Hz & _ & Hin2)]); [lia|].
        assert (Hne2 : (out2, cap2) <> (ka, L + 1)).
        { intros Hcc. apply (NI_OB2 (out2, cap2));
          [change OB2 with (aout_blks cap2 out2); unfold aout_blks;
           rewrite (proj2 (Z.eqb_neq cap2 0) ltac:(lia)); left; reflexivity|].
          rewrite Hcc. apply (Permutation_in _ (Permutation_sym HR1)). right; right; left; reflexivity. }
        pose proof (req_size_pos cap2 ltac:(lia)) as [Hq1 Hq2].
        rewrite (KFR out2 cap2 a Hin2 Hne2 ltac:(lia)). apply KR2. exact Ha64.
    - exact (gll_aout_rom_x ly2 S2 Hg2 W2 mem2 md2 _ _ _ _ _ _ HAR2 HO2).
    - intros bb Hbb. apply HinOB3. exact Hbb. }
  split; [exact GEB4|]. split; [exact AWR4|]. split; [exact GHP4|]. split; [exact FK4|]. split; [exact G54|].
  split.
  { eapply ajournal_gx_rom_view_x;
    first [exact HJ4 | exact HROMO | exact PSTR | exact HROM0 | exact LAWS | exact pa_segs_low]. }
  split; [exact Hsp4|]. split; [exact H34|]. split; [exact H44|]. split; [exact H84|]. split; [exact H94|].
  split; [exact H184|]. split; [exact H194|]. split; [exact H2427|].
  split; [exact (SLOT 8 _ SL1 ltac:(lia))|].
  split; [exact (SLOT 16 _ SL8 ltac:(lia))|].
  split; [exact (SLOT 24 _ SL9 ltac:(lia))|].
  split; [exact (SLOT 32 _ SL18 ltac:(lia))|].
  split; [exact (SLOT 40 _ SL19 ltac:(lia))|].
  split; [exact (SLOT 48 _ SL20 ltac:(lia))|].
  split; [exact (SLOT 56 _ SL21 ltac:(lia))|].
  split; [exact (SLOT 64 _ SL22 ltac:(lia)) | exact (SLOT 72 _ SL23 ltac:(lia))]. }
assert (U21 : U Eb (SOff 21 1) = Z.of_nat i + 1) by (apply (U_atom_off Eb 21 (Z.of_nat i) 1 F21); lia).
assert (U35 : U Eb (SOff 35 0) = re_nheld e)
  by (apply (U_atom Eb 35 (re_nheld e) F35); unfold re_nheld in *; lia).
psrr_branch_tok RUN BR HS SHOKb Bspan.
- (* i + 1 < nheld: the invariant at i + 1 and back to 0x825c0 *)
  cbn [branch_taken] in Hc. rewrite bv_lts_signed in Hc.
  rewrite bv_signed_small in Hc by
    (repeat match goal with |- context [bv_unsigned (sv_denot ?EE ?zz)] =>
       change (bv_unsigned (sv_denot EE zz)) with (U EE zz) end;
     rewrite ?U21, ?U35; unfold re_nheld in *; lia).
  rewrite bv_signed_small in Hc by
    (repeat match goal with |- context [bv_unsigned (sv_denot ?EE ?zz)] =>
       change (bv_unsigned (sv_denot EE zz)) with (U EE zz) end;
     rewrite ?U21, ?U35; unfold re_nheld in *; lia).
  change (bv_unsigned (sv_denot Eb (SOff 21 1))) with (U Eb (SOff 21 1)) in Hc.
  change (bv_unsigned (sv_denot Eb (SOff 35 0))) with (U Eb (SOff 35 0)) in Hc.
  rewrite U21, U35 in Hc. apply Z.ltb_lt in Hc.
  assert (Hlt : (S i < length (re_keys e))%nat) by (unfold re_nheld in Hc; lia).
  paj_run_to_tok_x RUNTO HS HJ3 SHOKb Bspan A_gse_loop. { apply awr_ok_x_of0. awr_ok_tac. }
  assert (KR4 : forall a, 0 <= a < 2 ^ 64 ->
    aview SEGS (w_H W3) (ms_mem ms2) a = aview SEGS (w_H W3) (ms_mem ms1) a).
  { intros a Ha. apply (aview_kept_out Eb _ (w_H W3) (ms_mem ms1) (ms_mem ms2) HFr2 a Ha). gll_outw. }
  assert (PK4 : apres_kept B W3 (ms_mem ms1) W3 (ms_mem ms2)).
  { apply gse_apres_grows. lazymatch goal with
    | K : mem_grows (mrestrict (w_H W3) (ms_mem ms1)) (mrestrict (w_H W3) (ms_mem ms2)) |- _ => exact K end. }
  pose proof (regs_kept_of_st_ok_pi _ _ _ regsc (gl_extra hp (hp + 8 * Z.of_nat i) ka (re_nheld e))
    [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 19%bv; 23%bv; 24%bv; 25%bv; 26%bv; 27%bv] HS HAEb
    ltac:(vm_compute; reflexivity)) as HK.
  cbn [ms_regs restrict] in HK.
  prreg HS (18%bv : bv 5) N18. prreg HS (20%bv : bv 5) N20.
  prreg HS (21%bv : bv 5) N21. prreg HS (22%bv : bv 5) N22.
  pmkst HS.
  eapply (IH W ly S0 Hp regs mem md ch SA TB e c O mx no cap out rest (S i) W3 ly3 S3 Hg3
    (ms_regs ms2) (ms_mem ms2) _ _ out2 kr ltac:(lia) HPREB Hlt).
  + apply FIN.
    * intros a Ha. exact (KR4 a Ha).
    * exact PK4.
    * exact HJ3.
    * change (spZ (ms_regs ms2)) with (bv_unsigned (getr (ms_regs ms2) 2)).
      rewrite (HK 2%bv ltac:(cbv; tauto)). exact HSP.
    * rewrite (HK 3%bv ltac:(cbv; tauto)). exact R3.
    * rewrite (HK 4%bv ltac:(cbv; tauto)). exact R4.
    * rewrite (HK 8%bv ltac:(cbv; tauto)). exact R8.
    * rewrite (HK 9%bv ltac:(cbv; tauto)). exact R9.
    * rewrite N18, F8, F19. apply gse_shadow_w. lia.
    * rewrite (HK 19%bv ltac:(cbv; tauto)). exact R19.
    * intros rr Hrr. rewrite <- (R2427 rr Hrr). apply HK.
      assert (Hr4 : rr = 24 \/ rr = 25 \/ rr = 26 \/ rr = 27) by (clear - Hrr; lia).
      clear - Hr4. destruct Hr4 as [-> | [-> | [-> | ->]]]; cbn [In];
      repeat first [left; apply bv_eq; reflexivity | right].
  + rewrite N20, F20, unsigned_lit_small by lia. unfold w64. f_equal. rewrite Nat2Z.inj_succ. lia.
  + rewrite N21, F21, unsigned_lit_small by lia. unfold w64. f_equal. rewrite Nat2Z.inj_succ. lia.
  + rewrite N22, F9, F19. apply gse_shadow_w. lia.
  + rewrite (HK 23%bv ltac:(cbv; tauto)). exact R23.
- (* i + 1 = nheld: the stretch after the loop *)
  cbn [branch_taken] in Hc. rewrite bv_lts_signed in Hc.
  rewrite bv_signed_small in Hc by
    (repeat match goal with |- context [bv_unsigned (sv_denot ?EE ?zz)] =>
       change (bv_unsigned (sv_denot EE zz)) with (U EE zz) end;
     rewrite ?U21, ?U35; unfold re_nheld in *; lia).
  rewrite bv_signed_small in Hc by
    (repeat match goal with |- context [bv_unsigned (sv_denot ?EE ?zz)] =>
       change (bv_unsigned (sv_denot EE zz)) with (U EE zz) end;
     rewrite ?U21, ?U35; unfold re_nheld in *; lia).
  change (bv_unsigned (sv_denot Eb (SOff 21 1))) with (U Eb (SOff 21 1)) in Hc.
  change (bv_unsigned (sv_denot Eb (SOff 35 0))) with (U Eb (SOff 35 0)) in Hc.
  rewrite U21, U35 in Hc. apply Z.ltb_ge in Hc.
  assert (Heq : S i = length (re_keys e)) by (unfold re_nheld in Hc; lia).
  paj_run_to_tok_x RUNTO HS HJ3 SHOKb Bspan A_gse_tail. { apply awr_ok_x_of0. awr_ok_tac. }
  assert (KR4 : forall a, 0 <= a < 2 ^ 64 ->
    aview SEGS (w_H W3) (ms_mem ms2) a = aview SEGS (w_H W3) (ms_mem ms1) a).
  { intros a Ha. apply (aview_kept_out Eb _ (w_H W3) (ms_mem ms1) (ms_mem ms2) HFr2 a Ha). gll_outw. }
  assert (PK4 : apres_kept B W3 (ms_mem ms1) W3 (ms_mem ms2)).
  { apply gse_apres_grows. lazymatch goal with
    | K : mem_grows (mrestrict (w_H W3) (ms_mem ms1)) (mrestrict (w_H W3) (ms_mem ms2)) |- _ => exact K end. }
  pose proof (regs_kept_of_st_ok_pi _ _ _ regsc (gl_extra hp (hp + 8 * Z.of_nat i) ka (re_nheld e))
    [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 19%bv; 23%bv; 24%bv; 25%bv; 26%bv; 27%bv] HS HAEb
    ltac:(vm_compute; reflexivity)) as HK.
  cbn [ms_regs restrict] in HK.
  prreg HS (18%bv : bv 5) N18.
  pmkst HS.
  eapply (GSE_TAIL_X W ly S0 Hp regs mem md ch SA TB e c O mx no cap out rest W3 ly3 S3 Hg3
    (ms_regs ms2) (ms_mem ms2) _ _ out2 kr HPREB).
  rewrite <- Heq. apply FIN.
  + intros a Ha. exact (KR4 a Ha).
  + exact PK4.
  + exact HJ3.
  + change (spZ (ms_regs ms2)) with (bv_unsigned (getr (ms_regs ms2) 2)).
    rewrite (HK 2%bv ltac:(cbv; tauto)). exact HSP.
  + rewrite (HK 3%bv ltac:(cbv; tauto)). exact R3.
  + rewrite (HK 4%bv ltac:(cbv; tauto)). exact R4.
  + rewrite (HK 8%bv ltac:(cbv; tauto)). exact R8.
  + rewrite (HK 9%bv ltac:(cbv; tauto)). exact R9.
  + rewrite N18, F8, F19. apply gse_shadow_w. lia.
  + rewrite (HK 19%bv ltac:(cbv; tauto)). exact R19.
  + intros rr Hrr. rewrite <- (R2427 rr Hrr). apply HK.
    assert (Hr4 : rr = 24 \/ rr = 25 \/ rr = 26 \/ rr = 27) by (clear - Hrr; lia).
    clear - Hr4. destruct Hr4 as [-> | [-> | [-> | ->]]]; cbn [In];
    repeat first [left; apply bv_eq; reflexivity | right].
Qed.

Theorem pb_gse_loop_x : gse_loop_at_x B PST ARx MT RP MMAX RG (BASE + A_gse_loop).
Proof.
intros W ly S Hp regs mem md ch SA TB e c O mx no cap out rest i Wc lyc Sc Hpk regsc memc mdc k outi kr
  HPREB Hilt HINV R20 R21 R22 R23.
exact (gll_loop_x (length (re_keys e) - i) W ly S Hp regs mem md ch SA TB e c O mx no cap out rest i
  Wc lyc Sc Hpk regsc memc mdc k outi kr (Nat.le_refl _) HPREB Hilt HINV R20 R21 R22 R23).
Qed.

(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0): the loop at a world relation R.  The journal ajournal_gx_x becomes ajournal_gx_xR
   R, SRr SEGS becomes SRrG SEGS R, gse_inv_x / gse_post_x / the cut statements become their R twins (W_gse_cut.v,
   W_contract_xR.v), the runs and the branch are their SRrG forms (W_journal_x.v paj_run_x_xG / paj_run_to_x_xG,
   W_kit.v paj_branch_xR), gesture_end's contract is GE_R : ge_spec_xR (a Theorem Labs lane proves it in W_gesture_end.v),
   the helpers are W_gestures_end.v's R twins, and the free rules are their R forms (afree_cf_rule_c_xR /
   afree_null_cf_rule_c_xR .. RO CTX_AFREE R) with RO_ARx for their call-boundary premise RO.  The strict gll_ge_x,
   gll_loop_x and pb_gse_loop_x above keep their proofs. ---- *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
Hypothesis GE_R : ge_spec_xR B PST ARx R MT RP MMAX RG (BASE + AF_fr_gesture_end).
Variable RO : (word -> option byte) -> Prop.
Hypothesis RO_ARx : forall ly S Hp (W : world SEGS) mem md, ARx ly S Hp W mem md -> RO mem.
Hypothesis AFREE_R : afree_cf_rule_c_xR SEGS B PST ARx MT RP RO CTX_AFREE R.
Hypothesis AFREEN_R : afree_null_cf_rule_c_xR SEGS B PST ARx MT RP RO CTX_AFREE R.
Hypothesis GSE_TAIL_XR : gse_tail_at_xR B PST ARx MT RP MMAX RG R (BASE + A_gse_tail).
Let RUNG := paj_run_x_xG B PST ARx LAWS R (G_SL B RG) HG 0 [].
Let RUNTOG := paj_run_to_x_xG B PST ARx LAWS R (G_SL B RG) HG 0 [].
Let BRR := paj_branch_xR (PI := PI) (R := R).
(* :383 gll_ge_x *)
(* gesture_end's contract GE_R through W_gestures_end.v's gse_callS_x, with the call made 80 bytes below the caller's sp
   (the loop body's own frame).  The room round: GE_R's kr, its RM premise and count premise (ge_spec_xR's, at its named
   peak ge_pk), and its post's RM, are the lemma's. *)
Lemma gll_ge_xR : forall W regsc memc mdc STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc k raw c O mx no cap out x q m (kr : nat),
ajournal_gx_xR SEGS B PST ARx R (G_SL B RG) 0 [] STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memc mdc k ->
spZ regsc = sp0 - 80 -> GE_STK + 80 <= STK ->
getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
getr regsc 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
s0Z regsc < alloc_ceiling ->
getr regsc 10 = w64 q ->
aout_at B RG lyc Sc W memc c O mx no cap out ->
garr8 SEGS (arm W memc) q (bzs (x ++ [Z_to_bv 8 0])) -> ~ In (Z_to_bv 8 0) x ->
14 <= Z.of_nat (length x) <= APARTIAL ->
In (q, m) (ablocks B lyc Sc) -> q <> out -> Z.of_nat (length x) + 1 <= req_size m ->
garr8 SEGS (arm W memc) (VAL A_lit_end5) (bzs END5) -> rom_view SEGS W memc ->
ge_room MMAX (blocks_bytes Sc) c mx no cap (Z.of_nat (length x)) ->
mo_ok MT Sc (ge_cost MT c mx no cap (Z.of_nat (length x))) ->
rp_RM RP Sc (Z.to_nat (ge_cost MT_rk c mx no cap (Z.of_nat (length x))) + kr) ->
cnt_ok_pk RP ge_pk (ablocks B lyc Sc) ->
(forall a, inFP (ablocks_fp (aout_blks cap out)) a ->
 (inFP FP a /\ exists b n, In (b, n) (ablocks B lyc Sc) /\ b <= a < b + req_size n) \/
 in_tmp_block (ablocks B ly S) (ablocks B lyc Sc) a) ->
SRrG SEGS R W (mkCfg (mkst regsc (Z_to_bv 64 (BASE + AF_fr_gesture_end)) memc (seg_rom SEGS)) mdc)
(fun W2 c2 => exists ly2 S2 Hp2 regs2 mem2 md2 k1 out',
 c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
 ajournal_gx_xR SEGS B PST ARx R (G_SL B RG) 0 [] STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 (k + k1) /\
 ajournal_gx_xR SEGS B PST ARx R (G_SL B RG) 0 [] GE_STK (sp0 + -80) (ablocks_fp (aout_blks cap out)) lyc Sc Hpc W memc mdc []
   ly2 S2 Hp2 W2 mem2 md2 k1 /\
 aregs_preserved regsc regs2 /\ apres_kept B W memc W2 mem2 /\
 mo_le MT Sc S2 (ge_cost MT c mx no cap (Z.of_nat (length x))) /\
 rp_RM RP S2 kr /\
 (exists rest, Permutation (ablocks B lyc Sc) (aout_blks cap out ++ rest) /\
   Permutation (ablocks B ly2 S2) (aout_blks (ge_cap c mx no cap (Z.of_nat (length x))) out' ++ rest)) /\
 aout_at B RG ly2 S2 W2 mem2 (ge_ctl c (Z.of_nat (length x))) (ge_O c O x) mx (ge_no c no (Z.of_nat (length x)))
   (ge_cap c mx no cap (Z.of_nat (length x))) out').
Proof.
intros W regsc memc mdc STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc k raw c O mx no cap out x q m kr
  HJ Hsp HSTK Hgp Htp Hra Hraw Hra4 Hs0 H10 HOUT GK NZ X1 Hq Hqo Hqm G5 HROM ROOM MOK HRM HCNT HF.
eapply SRrG_mono.
{ eapply (gse_callS_xR B PST ARx LAWS R R_trans (G_SL B RG) W regsc memc (Z_to_bv 64 (BASE + AF_fr_gesture_end)) STK sp0 FP ly S Hp W0
    mem md own lyc Sc Hpc mdc k GE_STK (ablocks_fp (aout_blks cap out)) (-80) raw []
    (fun ly2 S2 W2 regs2 mem2 md2 => exists out', apres_kept B W memc W2 mem2 /\
      mo_le MT Sc S2 (ge_cost MT c mx no cap (Z.of_nat (length x))) /\
      rp_RM RP S2 kr /\
      (exists rest, Permutation (ablocks B lyc Sc) (aout_blks cap out ++ rest) /\
        Permutation (ablocks B ly2 S2) (aout_blks (ge_cap c mx no cap (Z.of_nat (length x))) out' ++ rest)) /\
      aout_at B RG ly2 S2 W2 mem2 (ge_ctl c (Z.of_nat (length x))) (ge_O c O x) mx (ge_no c no (Z.of_nat (length x)))
        (ge_cap c mx no cap (Z.of_nat (length x))) out')
    HG HJ).
  - lia.
  - reflexivity.
  - lia.
  - unfold GE_STK, GE_FRAME, SL_STK, SL_FRAME, ASTACK, ESTACK. lia.
  - lia.
  - exact Hgp.
  - exact Htp.
  - exact Hra.
  - exact Hraw.
  - exact Hra4.
  - apply achain_low. exact Hs0.
  - intros HPRE1. eapply SRrG_mono.
    { exact (GE_R W lyc Sc Hpc regsc memc mdc [] c O mx no cap out q x q m HPRE1 H10 HOUT GK NZ X1 Hq Hqo
        ltac:(lia) ltac:(lia) G5 HROM ROOM MOK kr HRM HCNT). }
    cbv beta.
    intros W3 c3 _ (ly3 & S3 & Hp3 & regs3 & mem3 & md3 & k3 & out3 & -> & HJ3 & HP3 & HA3 & HM3 & HR3 & HPm3 & HO3).
    exists ly3, S3, Hp3, regs3, mem3, md3, k3. split; [rewrite Hra; reflexivity|]. split; [exact HJ3|]. split; [exact HP3|].
    exists out3. split; [exact HA3|]. split; [exact HM3|]. split; [exact HR3|]. split; [exact HPm3 | exact HO3].
  - exact HF. }
cbv beta. intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HJ2 & HJc2 & HP2 & (out' & HA & HM & HR & HPm & HO)).
exists ly2, S2, Hp2, regs2, mem2, md2, k1, out'. split; [reflexivity|]. split; [exact HJ2|].
split; [exact HJc2|]. split; [exact HP2|]. split; [exact HA|]. split; [exact HM|]. split; [exact HR|].
split; [exact HPm | exact HO].
Qed.
(* :584 gll_loop_x *)
Lemma gll_loop_xR : forall (d : nat) W ly S0 Hp regs mem md ch SA TB e c O mx no cap out rest (i : nat)
  Wc lyc Sc Hpk regsc memc mdc k outi (kr : nat),
(length (re_keys e) - i <= d)%nat ->
gse_pre_x B ARx MT RP MMAX RG W ly S0 Hp regs mem md ch SA TB e c O mx no cap out rest kr ->
(i < length (re_keys e))%nat ->
gse_inv_xR B PST ARx MT RP MMAX RG R W ly S0 Hp regs mem md SA TB e c O mx no cap out rest i Wc lyc Sc Hpk regsc memc mdc k
  outi kr ->
getr regsc 20 = w64 (8 * Z.of_nat i) -> getr regsc 21 = w64 (Z.of_nat i) ->
getr regsc 22 = w64 ((SA + 40) / 8 + SB) -> getr regsc 23 = w64 3 ->
SRrG SEGS R Wc (mkCfg (mkst regsc (Z_to_bv 64 (BASE + A_gse_loop)) memc (seg_rom SEGS)) mdc)
  (gse_post_xR B PST ARx R MT RP RG regs ly S0 Hp W mem md SA TB e c O mx no cap out rest kr).
Proof.
induction d as [|d IH]; intros W ly S0 Hp regs mem md ch SA TB e c O mx no cap out rest i
  Wc lyc Sc Hpk regsc memc mdc k outi kr Hd HPREB Hilt HINV R20 R21 R22 R23; [lia|].
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : GSE_STK = 16608) by reflexivity. assert (WG : GE_STK = 16528) by reflexivity.
assert (ER1 : A_gse_ret1 = 764) by (vm_compute; reflexivity).
assert (ER2 : A_gse_ret2 = 804) by (vm_compute; reflexivity).
assert (EAT : A_gse_tail = 844) by (vm_compute; reflexivity).
pose proof HPREB as (HPRE & H10 & HinTB & HT1 & HT2 & HSA8 & HEB0 & HAW0 & HHELD & HOUT0 & HPERM0 & G50 & HROM0 & ROOM0 & MOK0
  & RM0 & CNT0).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (HLO : alloc_ceiling + GSE_STK <= spZ regs) by lia.
unfold gse_inv_xR in HINV. cbv zeta in HINV.
destruct HINV as (HJ & HPK & HML & HMOK & HRM & HROOM & HPERM & HOUT & HEB & HAW & GHP & FKEYS & G5 & HROM & HSP
  & R3 & R4 & R8 & R9 & R18 & R19 & R2427 & SL1 & SL8 & SL9 & SL18 & SL19 & SL20 & SL21 & SL22 & SL23).
(* the block list at the loop head in the cut's form, for the room round's counts (gse_cnt_at) *)
pose proof HPERM as HPERMi.
assert (HARc : ARx lyc Sc Hpk Wc memc mdc) by (eapply ajournal_gx_AR_xR; exact HJ).
destruct HHELD as (Hp1 & Hp2 & Hnh26 & HHP & HNDa & HNDt & FK0).
(* the key at index i *)
destruct (nth_error (re_keys e) i) as [ki|] eqn:Eki;
  [|exfalso; apply nth_error_None in Eki; lia].
pose proof (gll_skipn_S _ (re_keys e) i ki Eki) as ESK.
assert (Exs : nth_error (gse_keys e) i = Some (key_text ki)) by (unfold gse_keys; apply map_nth_error; exact Eki).
pose proof (gll_skipn_S _ (gse_keys e) i (key_text ki) Exs) as ESX.
pose proof (gll_firstn_S _ (gse_keys e) i (key_text ki) Exs) as EFX.
(* the held array is a live block (the key list is not empty) *)
destruct HHP as [(Hz & Hke) | (Hnz & HinHP0 & Hkh & Hkh8 & GHP0)]; [rewrite Hke in Hilt; cbn in Hilt; lia|].
rewrite ESK in FKEYS. inversion FKEYS as [|k0 ks0 KOKi FKREST Heqf]; subst k0 ks0.
destruct KOKi as (GKEY & KNZ & KLEN).
set (L := Z.of_nat (length (key_text ki))) in *.
set (ka := key_addr ki) in *.
set (hp := re_hp e) in *. set (kh := re_kh e) in *.
set (r0 := gse_run c O mx no cap (firstn i (gse_keys e))) in *.
set (KS := kblks (skipn (S i) (re_keys e))) in *.
set (OB := aout_blks (gse_cap r0) outi) in *.
(* the block list at the loop head *)
rewrite ESK in HPERM. rewrite gll_kblks_cons in HPERM.
unfold gse_hpblk in HPERM. rewrite (proj2 (Z.eqb_neq hp 0) Hnz) in HPERM. cbn [app] in HPERM.
fold L in HPERM. fold ka in HPERM. fold KS in HPERM.
assert (HinTBc : In (TB, ATABLE) (ablocks B lyc Sc))
  by (eapply Permutation_in; [apply Permutation_sym; exact HPERM | left; reflexivity]).
assert (HinHPc : In (hp, kh) (ablocks B lyc Sc))
  by (eapply Permutation_in; [apply Permutation_sym; exact HPERM | right; left; reflexivity]).
assert (HinKAc : In (ka, L + 1) (ablocks B lyc Sc))
  by (eapply Permutation_in; [apply Permutation_sym; exact HPERM | right; right; left; reflexivity]).
assert (HinKSc : forall bb, In bb KS -> In bb (ablocks B lyc Sc)).
{ intros bb Hbb. eapply Permutation_in; [apply Permutation_sym; exact HPERM|].
  right; right; right. apply in_or_app. left. exact Hbb. }
assert (HinOBc : forall bb, In bb OB -> In bb (ablocks B lyc Sc)).
{ intros bb Hbb. eapply Permutation_in; [apply Permutation_sym; exact HPERM|].
  right; right; right. apply in_or_app. right. apply in_or_app. left. exact Hbb. }
(* distinctness, from NoDup of the live blocks *)
pose proof (gse_nodup_x B ARx LAWS BLKN lyc Sc Hpk Wc memc mdc HARc) as ND.
apply (Permutation_NoDup HPERM) in ND.
inversion ND as [|? ? NI_TB ND1].
inversion ND1 as [|? ? NI_HP ND2].
inversion ND2 as [|? ? NI_KA ND3].
assert (NI_KS' : forall bb, In bb KS -> ~ In bb OB).
{ intros bb Hbb Hcc. apply (gll_nodup_app _ KS (OB ++ rest) ND3 bb Hbb). apply in_or_app. left. exact Hcc. }
assert (DTB : (TB, ATABLE) <> (ka, L + 1)) by (intros Hcc; apply NI_TB; right; left; exact (eq_sym Hcc)).
assert (DHP : (hp, kh) <> (ka, L + 1)) by (intros Hcc; apply NI_HP; left; exact (eq_sym Hcc)).
assert (DKS : forall bb, In bb KS -> bb <> (ka, L + 1)).
{ intros bb Hbb Hcc. apply NI_KA. apply in_or_app. left. rewrite <- Hcc. exact Hbb. }
(* numeric facts on the three blocks *)
destruct (alx_blocks _ _ _ LAWS lyc Sc Hpk Wc memc mdc TB ATABLE HARc HinTBc) as (HTB16 & HTB4 & HTBc & HTBa & _ & _).
destruct (alx_blocks _ _ _ LAWS lyc Sc Hpk Wc memc mdc hp kh HARc HinHPc) as (HHP16 & HHP4 & HHPc & HHPa & _ & _).
destruct (alx_blocks _ _ _ LAWS lyc Sc Hpk Wc memc mdc ka (L + 1) HARc HinKAc) as (HKA16 & HKA4 & HKAc & HKAa & _ & _).
change (req_size ATABLE) with 896 in HTBc, HTBa.
assert (HRKH : req_size kh = kh) by (unfold req_size; destruct (Z.eqb_spec kh 0); lia).
assert (HRKA : req_size (L + 1) = L + 1) by (unfold req_size; destruct (Z.eqb_spec (L + 1) 0); lia).
rewrite HRKH in HHPc, HHPa. rewrite HRKA in HKAc, HKAa.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HTBa, HHPa, HKAa.
assert (RSA : 4096 <= SA /\ SA + 56 <= TB + 896 /\ SA + 56 <= alloc_ceiling /\ SA + 56 <= 140737479966720)
  by (unfold AENT, ATABLE in *; lia).
destruct RSA as (RSA0 & RSA1 & RSA2 & RSA3).
assert (HiN : Z.of_nat i < re_nheld e) by (unfold re_nheld; lia).
assert (Hi8L : 8 * Z.of_nat i + 8 <= kh) by (unfold re_nheld in Hkh; lia).
(* the held slot and the entry's two fields, as the seat needs them *)
pose proof HEB as HEB2. rewrite gse_entry_split in HEB2. unfold bzs in HEB2. rewrite !map_app in HEB2.
apply garr8_app in HEB2 as [_ HEB2]. rewrite length_map, (gse_epre_len e Hp1) in HEB2.
apply garr8_app in HEB2 as [Ghp HEB2]. apply garr8_app in HEB2 as [Gnh _].
rewrite length_map, OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.length_le8 in Gnh.
change (SA + Z.of_nat 40) with (SA + 40) in Ghp, Gnh. replace (SA + 40 + Z.of_nat 8) with (SA + 48) in Gnh by lia.
assert (Mhp : val_mem SEGS (arm Wc memc) (SA + 40) 8 hp).
{ apply gse_garr8_le; [|lia].
  unfold OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.le8, word_to_le_bytes in Ghp.
  rewrite unsigned_lit_small in Ghp by lia. exact Ghp. }
assert (Mnh : val_mem SEGS (arm Wc memc) (SA + 48) 4 (re_nheld e)).
{ apply gse_garr8_le; [|unfold re_nheld in *; lia].
  unfold OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.le4 in Gnh.
  rewrite unsigned_lit_small in Gnh by (unfold re_nheld in *; lia). exact Gnh. }
assert (Mka : val_mem SEGS (arm Wc memc) (hp + 8 * Z.of_nat i) 8 ka).
{ exact (gse_key_ptr (arm Wc memc) hp (re_keys e) i ki GHP Eki ltac:(unfold ka; lia)). }
(* the two shadow ranges *)
assert (RA1 : range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF (SA + 40) 16).
{ apply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 lyc Sc Hpk Wc memc mdc TB ATABLE (SA + 40) 16 HARc HinTBc);
  change (req_size ATABLE) with 896; unfold AENT, ATABLE in *; lia. }
assert (RA2 : range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF (hp + 8 * Z.of_nat i) 8).
{ apply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 lyc Sc Hpk Wc memc mdc hp kh (hp + 8 * Z.of_nat i) 8 HARc
    HinHPc);
  [lia | rewrite HRKH; lia]. }
(* the table block and the held array are apart *)
assert (HDIS : hp + 8 * Z.of_nat i + 8 <= SA + 40 \/ SA + 52 <= hp + 8 * Z.of_nat i).
{ destruct (gll_disj_x lyc Sc Hpk Wc memc mdc TB ATABLE hp kh HARc HinTBc HinHPc
    ltac:(intros Hc; apply NI_TB; left; exact (eq_sym Hc)))
  as [Hdd | Hdd]; change (req_size ATABLE) with 896 in Hdd; rewrite ?HRKH in Hdd;
  unfold AENT, ATABLE in *; lia. }
destruct (gll_seat Wc regsc memc SA hp ka (re_nheld e) (Z.of_nat i)
  R8 R9 R18 R19 R20 R21 R22 ltac:(unfold AENT, ATABLE in *; lia) HSA8 ltac:(unfold AENT, ATABLE in *; lia)
  ltac:(unfold AENT, ATABLE in *; lia) HHP4 ltac:(pose proof (Z.div_mod hp 8 ltac:(lia)); pose proof (Z.div_mod hp 16 ltac:(lia));
    pose proof (Z.mod_pos_bound hp 8 ltac:(lia)); lia)
  ltac:(lia) ltac:(lia) HDIS HKA4 HKA16 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
  ltac:(unfold re_nheld in *; lia) Mhp Mnh Mka RA1 RA2) as [HS SHOK].
remember (Eimg (Ereg regsc (gl_extra hp (hp + 8 * Z.of_nat i) ka (re_nheld e)))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regsc (gl_extra hp (hp + 8 * Z.of_nat i) ka (re_nheld e))) E)
  by (rewrite HE; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E m = getr regsc rr).
{ intros m rr Hm. rewrite HE. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hm. }
assert (E2 : ew E 2 = getr regsc 2) by (exact (EEo 2%nat 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regsc 3) by (exact (EEo 3%nat 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regsc 4) by (exact (EEo 4%nat 4%bv eq_refl)).
assert (E8 : ew E 8 = Z_to_bv 64 (SA + 48)) by (rewrite (EEo 8%nat 8%bv eq_refl); exact R8).
assert (E9 : ew E 9 = Z_to_bv 64 (SA + 40)) by (rewrite (EEo 9%nat 9%bv eq_refl); exact R9).
assert (E19 : ew E 19 = Z_to_bv 64 SB) by (rewrite (EEo 19%nat 19%bv eq_refl); exact R19).
assert (E20 : ew E 20 = Z_to_bv 64 (8 * Z.of_nat i)) by (rewrite (EEo 20%nat 20%bv eq_refl); exact R20).
assert (E21 : ew E 21 = Z_to_bv 64 (Z.of_nat i)) by (rewrite (EEo 21%nat 21%bv eq_refl); exact R21).
assert (E33 : ew E 33 = Z_to_bv 64 (hp + 8 * Z.of_nat i))
  by (rewrite HE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsc _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 ka)
  by (rewrite HE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsc _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 (re_nheld e))
  by (rewrite HE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsc _ 3)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs - GSE_FRAME) by (rewrite E2; exact HSP).
clear HE.
(* ---- 0x825c0 -> gesture_end's entry *)
paj_run_to_tok_xR RUNTOG HS HJ SHOK Bspan AF_fr_gesture_end. { apply awr_ok_x_of0. awr_ok_tac. }
assert (KR1 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H Wc) (ms_mem ms) a = aview SEGS (w_H Wc) memc a).
{ intros a Ha. apply (aview_kept_out E _ (w_H Wc) memc (ms_mem ms) HFr a Ha). gll_outw. }
assert (PK1 : apres_kept B Wc memc Wc (ms_mem ms)).
{ apply gse_apres_grows. lazymatch goal with
  | K : mem_grows (mrestrict (w_H Wc) memc) (mrestrict (w_H Wc) (ms_mem ms)) |- _ => exact K end. }
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3.
prreg HS (4%bv : bv 5) P4. prreg HS (8%bv : bv 5) P8. prreg HS (10%bv : bv 5) P10.
pmkst HS.
(* ---- gesture_end (held[i]) *)
assert (ROOMi : ge_room MMAX (blocks_bytes Sc) (gse_c r0) mx (gse_no r0) (gse_cap r0) L /\
  gse_room MMAX (blocks_bytes Sc + tr_net (ge_tr (gse_c r0) mx (gse_no r0) (gse_cap r0) L) - (L + 1))
    (ge_ctl (gse_c r0) L) mx (ge_no (gse_c r0) (gse_no r0) L) (ge_cap (gse_c r0) mx (gse_no r0) (gse_cap r0) L)
    (skipn (S i) (gse_keys e))).
{ rewrite ESX in HROOM. cbn [gse_room] in HROOM. exact HROOM. }
destruct ROOMi as [ROOMi ROOMr].
assert (MOKi : mo_ok MT Sc (gse_cost MT (gse_c r0) mx (gse_no r0) (gse_cap r0)
  (key_text ki :: skipn (S i) (gse_keys e)))) by (rewrite <- ESX; exact HMOK).
cbn [gse_cost] in MOKi. fold L in MOKi.
destruct (gll_aout_facts lyc Sc Wc memc _ _ _ _ _ _ HOUT) as (Hmx & HnoO & Hblk).
assert (Hno0 : 0 <= gse_no r0) by lia.
assert (Hcap0 : 0 <= gse_cap r0) by (destruct Hblk; lia).
assert (HCRest : 0 <= gse_cost MT (ge_ctl (gse_c r0) L) mx (ge_no (gse_c r0) (gse_no r0) L)
  (ge_cap (gse_c r0) mx (gse_no r0) (gse_cap r0) L) (skipn (S i) (gse_keys e))).
{ apply (gll_cost_nonneg MT MTL); [lia | apply gll_ge_no_nonneg; lia | apply gll_ge_cap_nonneg; lia]. }
(* the room round: RM at the loop head carries this key's gesture_end, its free (MT_rk's mo_free is 1) and the calls
   after them; gesture_end is called with kr := 1 + krf, the free with kr := krf *)
assert (Hge_rk : 0 <= ge_cost MT_rk (gse_c r0) mx (gse_no r0) (gse_cap r0) L)
  by (apply (gll_ge_cost_nonneg MT_rk gse_rk_laws); lia).
assert (Hrest_rk : 0 <= gse_cost MT_rk (ge_ctl (gse_c r0) L) mx (ge_no (gse_c r0) (gse_no r0) L)
  (ge_cap (gse_c r0) mx (gse_no r0) (gse_cap r0) L) (skipn (S i) (gse_keys e)))
  by (apply (gll_cost_nonneg MT_rk gse_rk_laws); [lia | apply gll_ge_no_nonneg; lia | apply gll_ge_cap_nonneg; lia]).
pose (krf := (Z.to_nat (gse_cost MT_rk (ge_ctl (gse_c r0) L) mx (ge_no (gse_c r0) (gse_no r0) L)
  (ge_cap (gse_c r0) mx (gse_no r0) (gse_cap r0) L) (skipn (S i) (gse_keys e))) + kr)%nat).
assert (RMi : rp_RM RP Sc (Z.to_nat (ge_cost MT_rk (gse_c r0) mx (gse_no r0) (gse_cap r0) L) + (1 + krf))).
{ assert (EQ : (Z.to_nat (gse_cost MT_rk (gse_c r0) mx (gse_no r0) (gse_cap r0) (skipn i (gse_keys e))) + kr =
    Z.to_nat (ge_cost MT_rk (gse_c r0) mx (gse_no r0) (gse_cap r0) L) + (1 + krf))%nat).
  { rewrite ESX. cbn [gse_cost]. fold L. unfold krf. change (mo_free MT_rk) with 1. lia. }
  rewrite <- EQ. exact HRM. }
pose proof (mo_free_nonneg MT MTL) as HMF.
assert (MOKge : mo_ok MT Sc (ge_cost MT (gse_c r0) mx (gse_no r0) (gse_cap r0) L))
  by (apply (mo_ok_le MT MTL Sc _ _ MOKi); lia).
assert (HKAout : ka <> outi).
{ destruct Hblk as [(Hc0 & Ho0 & _) | (Hc0 & _ & Hin)]; [lia|].
  assert (HinOB : In (outi, gse_cap r0) OB)
    by (unfold OB, aout_blks; rewrite (proj2 (Z.eqb_neq (gse_cap r0) 0) ltac:(lia)); left; reflexivity).
  assert (Hne : (ka, L + 1) <> (outi, gse_cap r0))
    by (intros Hc; apply NI_KA; rewrite Hc; apply in_or_app; right; apply in_or_app; left; exact HinOB).
  pose proof (req_size_pos (gse_cap r0) ltac:(lia)) as [Hq1 _].
  destruct (gll_disj_x lyc Sc Hpk Wc memc mdc ka (L + 1) outi (gse_cap r0) HARc HinKAc (HinOBc _ HinOB) Hne)
    as [Hd1 | Hd1];
  rewrite ?HRKA in Hd1; lia. }
eapply (SRrG_bind SEGS R R_trans).
{ eapply (gll_ge_xR Wc (ms_regs ms) (ms_mem ms) _ GSE_STK (spZ regs) (gse_FP SA e cap out) ly S0 Hp W mem md [] lyc Sc Hpk k
    (Z_to_bv 64 (BASE + A_gse_ret1)) (gse_c r0) (gse_O r0) mx (gse_no r0) (gse_cap r0) outi
    (key_text ki) ka (L + 1) (1 + krf)%nat HJ).
  - change (spZ (ms_regs ms)) with (bv_unsigned (getr (ms_regs ms) 2)). rewrite P2, Usp. unfold GSE_FRAME. lia.
  - lia.
  - rewrite P3, E3, R3. exact Hgp.
  - rewrite P4, E4, R4. exact Htp.
  - rewrite ER1. exact P1.
  - rewrite ER1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite ER1, unsigned_lit_small by lia. lia.
  - unfold s0Z. rewrite P8, E8.
    rewrite unsigned_lit_small by (unfold AENT, ATABLE in *; lia). unfold AENT, ATABLE in *. lia.
  - rewrite P10, E34. reflexivity.
  - apply (gll_aout_kept lyc Sc Wc memc lyc Sc Wc (ms_mem ms) _ _ _ _ _ _ HOUT);
    [intros rr a Hrr Ha; apply KR1; destruct (gll_aout_rom_x lyc Sc Hpk Wc memc mdc _ _ _ _ _ _ HARc HOUT rr a Hrr Ha); lia
    | exact (gll_aout_rom_x lyc Sc Hpk Wc memc mdc _ _ _ _ _ _ HARc HOUT)
    | intros bb Hbb; exact (HinOBc bb Hbb)].
  - apply (gse_garr8_kept (w_H Wc) (w_H Wc) memc (ms_mem ms) ka _ GKEY).
    intros b Hb. unfold bzs in Hb. rewrite length_map, length_app in Hb. cbn [length] in Hb. apply KR1. lia.
  - exact KNZ.
  - exact KLEN.
  - exact HinKAc.
  - exact HKAout.
  - rewrite HRKA. lia.
  - apply (gse_garr8_kept (w_H Wc) (w_H Wc) memc (ms_mem ms) _ _ G5).
    intros b Hb. change (Z.of_nat (length (bzs END5))) with 5 in Hb.
    pose proof (pa_img_range _ (HEND5I b ltac:(lia))). apply KR1. lia.
  - intros a Hin'.
    assert (HI : 0x10000 <= a < 0x5fb000)
      by (destruct Hin' as (sg & Hsg & _ & Hr'); exact (pa_img_range a ltac:(exists sg; split; [exact Hsg | exact Hr']))).
    rewrite KR1 by lia. exact (HROM a Hin').
  - exact ROOMi.
  - exact MOKge.
  - exact RMi.
  - (* the room round: gesture_end's count premise, from the entry's (gse_cnt_at; the peaks are read off the premises) *)
    eapply (gse_cnt_at RP _ _ e (ablocks B ly S0) (ablocks B lyc Sc) TB i cap out (gse_cap r0) outi rest);
    [| exact HPERM0 | exact HPERMi | exact CNT0]; intros P; cbv [ge_pk gse_pk]; lia.
  - (* the out block's footprint is the caller's, or a block the caller never had *)
    intros a Ha. apply inFP_ablocks_fp_inv in Ha as (p & n & Hpin & Hpa).
    assert (Hpc : In (p, n) (ablocks B lyc Sc)) by (exact (HinOBc (p, n) Hpin)).
    assert (DEC : forall u v : Z * Z, {u = v} + {u <> v}) by (decide equality; apply Z.eq_dec).
    destruct (in_dec DEC (p, n) (ablocks B ly S0)) as [IN0 | NIN0].
    + left. split; [|exists p, n; split; [exact Hpc | exact Hpa]].
      apply (Permutation_in _ HPERM0) in IN0.
      destruct IN0 as [IN0 | IN0].
      * exfalso. injection IN0 as <- <-. apply NI_TB.
        right. right. apply in_or_app. right. apply in_or_app. left. exact Hpin.
      * apply in_app_or in IN0 as [IN0 | IN0].
        { unfold gse_FP. apply (proj2 (inFP_cons _ _ _ _)). right.
          replace a with (p + (a - p)) by lia.
          apply (inFP_ablocks_fp (gse_blks e ++ aout_blks cap out) p n (a - p));
          [apply in_or_app; left; exact IN0 | lia]. }
        apply in_app_or in IN0 as [IN0 | IN0].
        { unfold gse_FP. apply (proj2 (inFP_cons _ _ _ _)). right.
          replace a with (p + (a - p)) by lia.
          apply (inFP_ablocks_fp (gse_blks e ++ aout_blks cap out) p n (a - p));
          [apply in_or_app; right; exact IN0 | lia]. }
        exfalso. apply (gll_nodup_app _ (KS ++ OB) rest ltac:(rewrite <- app_assoc; exact ND3) (p, n));
        [apply in_or_app; right; exact Hpin | exact IN0].
    + right. exists p, n. split; [exact Hpc | split; [exact NIN0 | exact Hpa]]. }
cbv beta. intros W2 c2 Hwle2
  (ly2 & S2 & Hg2 & regs2 & mem2 & md2 & k1 & out2 & -> & HJ2 & HJc2 & HP2 & HAK2 & HM2 & HRM2 & (R1 & HPa & HPb) & HO2).
assert (HAR2 : ARx ly2 S2 Hg2 W2 mem2 md2) by (eapply ajournal_gx_AR_xR; exact HJ2).
fold L in HM2. fold L in HPb. fold L in HO2.
set (cap2 := ge_cap (gse_c r0) mx (gse_no r0) (gse_cap r0) L) in *.
set (OB2 := aout_blks cap2 out2) in *.
(* the blocks the call kept *)
assert (KEEPB : forall bb, In bb (ablocks B lyc Sc) -> ~ In bb OB -> In bb (ablocks B ly2 S2)).
{ intros bb Hb Hnb. assert (Hb1 : In bb (OB ++ R1)) by (eapply Permutation_in; [exact HPa | exact Hb]).
  apply in_app_or in Hb1 as [Hb1 | Hb1]; [exfalso; exact (Hnb Hb1)|].
  eapply Permutation_in; [apply Permutation_sym; exact HPb|]. apply in_or_app. right. exact Hb1. }
assert (NI_OB : forall bb, In bb OB -> ~ In bb R1).
{ intros bb Hbb. apply (gll_nodup_app _ OB R1); [|exact Hbb].
  apply (Permutation_NoDup HPa). exact (gse_nodup_x B ARx LAWS BLKN lyc Sc Hpk Wc memc mdc HARc). }
assert (NI_OB2 : forall bb, In bb OB2 -> ~ In bb R1).
{ intros bb Hbb. apply (gll_nodup_app _ OB2 R1); [|exact Hbb].
  apply (Permutation_NoDup HPb). exact (gse_nodup_x B ARx LAWS BLKN ly2 S2 Hg2 W2 mem2 md2 HAR2). }
assert (HR1 : Permutation R1 ((TB, ATABLE) :: (hp, kh) :: (ka, L + 1) :: KS ++ rest)).
{ apply (Permutation_app_inv_l OB). eapply perm_trans; [apply Permutation_sym; exact HPa|].
  eapply perm_trans; [exact HPERM|].
  change ((TB, ATABLE) :: (hp, kh) :: (ka, L + 1) :: KS ++ OB ++ rest)
    with (((TB, ATABLE) :: (hp, kh) :: (ka, L + 1) :: KS) ++ OB ++ rest).
  apply gll_swap_app. }
assert (HinTB2 : In (TB, ATABLE) (ablocks B ly2 S2))
  by (apply KEEPB; [exact HinTBc | intros Hc; apply (NI_OB _ Hc); apply (Permutation_in _ (Permutation_sym HR1)); left; reflexivity]).
assert (HinHP2 : In (hp, kh) (ablocks B ly2 S2))
  by (apply KEEPB; [exact HinHPc | intros Hc; apply (NI_OB _ Hc); apply (Permutation_in _ (Permutation_sym HR1)); right; left; reflexivity]).
assert (HinKA2 : In (ka, L + 1) (ablocks B ly2 S2))
  by (apply KEEPB; [exact HinKAc | intros Hc; apply (NI_OB _ Hc); apply (Permutation_in _ (Permutation_sym HR1)); right; right; left; reflexivity]).
assert (HinKS2 : forall bb, In bb KS -> In bb (ablocks B ly2 S2)).
{ intros bb Hbb. apply KEEPB; [exact (HinKSc bb Hbb)|]. intros Hc. apply (NI_OB _ Hc).
  apply (Permutation_in _ (Permutation_sym HR1)). right; right; right. apply in_or_app. left. exact Hbb. }
(* nothing of the caller's data is inside the out block the callee used *)
assert (NFP1 : forall p n a, In (p, n) (ablocks B lyc Sc) -> ~ In (p, n) OB -> p <= a < p + req_size n ->
  ~ inFP (ablocks_fp OB) a).
{ intros p n a Hpc Hnb Hpa Hc. apply inFP_ablocks_fp_inv in Hc as (q & m & Hqin & Hqa).
  assert (Hqc : In (q, m) (ablocks B lyc Sc)) by (exact (HinOBc (q, m) Hqin)).
  assert (Hne : (p, n) <> (q, m)) by (intros Hcc; injection Hcc as <- <-; exact (Hnb Hqin)).
  destruct (gll_disj_x lyc Sc Hpk Wc memc mdc p n q m HARc Hpc Hqc Hne); lia. }
assert (NI_TB' : ~ In (TB, ATABLE) OB)
  by (intros Hc; apply (NI_OB _ Hc); apply (Permutation_in _ (Permutation_sym HR1)); left; reflexivity).
assert (NI_HP' : ~ In (hp, kh) OB)
  by (intros Hc; apply (NI_OB _ Hc); apply (Permutation_in _ (Permutation_sym HR1)); right; left; reflexivity).
assert (NI_KA' : ~ In (ka, L + 1) OB)
  by (intros Hc; apply (NI_OB _ Hc); apply (Permutation_in _ (Permutation_sym HR1)); right; right; left; reflexivity).
(* the bytes the gesture_end call kept *)
assert (KGE : forall p n j, In (p, n) (ablocks B lyc Sc) -> In (p, n) (ablocks B ly2 S2) -> ~ In (p, n) OB ->
  0 <= j < req_size n -> aview SEGS (w_H W2) mem2 (p + j) = aview SEGS (w_H Wc) (ms_mem ms) (p + j)).
{ intros p n j Hb1 Hb2 Hb3 Hj.
  apply (gse_keep_blk_xR B PST ARx LAWS IMGC BLKN R (G_SL B RG) 0 [] GE_STK (spZ regs + -80) (ablocks_fp OB)
    lyc Sc Hpk Wc (ms_mem ms) mdc [] ly2 S2 Hg2 W2 mem2 md2 k1 p n j HG HJc2 Hb1 Hb2 Hj).
  exact (NFP1 p n (p + j) Hb1 Hb3 ltac:(lia)). }
assert (KGEa : forall p n a, In (p, n) (ablocks B lyc Sc) -> In (p, n) (ablocks B ly2 S2) -> ~ In (p, n) OB ->
  p <= a < p + req_size n -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H Wc) (ms_mem ms) a).
{ intros p n a Hb1 Hb2 Hb3 Ha. replace a with (p + (a - p)) by lia. apply (KGE p n (a - p)); [exact Hb1 | exact Hb2 | exact Hb3 | lia]. }
assert (KGEi : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) ->
  ~ (as_errno B <= a < as_errno B + 4) -> ~ Exists (in_zr a) PST -> ~ inG (G_SL B RG) a ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H Wc) (ms_mem ms) a).
{ intros a Hi Ho He Hq Hng.
  apply (gse_keep_img_xR B PST ARx R (G_SL B RG) 0 [] GE_STK (spZ regs + -80) (ablocks_fp OB) lyc Sc Hpk Wc (ms_mem ms) mdc
    [] ly2 S2 Hg2 W2 mem2 md2 k1 HJc2 a Hi Ho He Hq); [|exact Hng].
  apply gse_fp_spares. intros bb Hbb. destruct bb as [bp bn]. cbn [fst].
  destruct (alx_blocks _ _ _ LAWS lyc Sc Hpk Wc memc mdc bp bn HARc (HinOBc (bp, bn) Hbb)) as (_ & Hb4 & _). exact Hb4. }
assert (KGEh : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (spZ regs - 80 - GE_STK <= a < spZ regs - 80) ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H Wc) (ms_mem ms) a).
{ intros a Ha Hno.
  apply (gse_keep_high_xR B PST ARx R (G_SL B RG) 0 [] GE_STK (spZ regs + -80) (ablocks_fp OB) lyc Sc Hpk Wc (ms_mem ms) mdc
    [] ly2 S2 Hg2 W2 mem2 md2 k1 HG HJc2 a Ha ltac:(lia)). }
(* ---- back at 0x825e8: the two checks again, then free (held[i]) *)
jafter_call_keep_pi HS 36%nat regs2 (mrestrict (w_H W2) mem2) HP2 [0; 1; 2]%nat HS2.
match type of HS2 with ?ty -> _ => assert (HRK : ty); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| | | apply Forall_nil];
  split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; intros a Ha; try lia.
  - rewrite E9, unsigned_lit_small in Ha by lia. apply (mbyte_of_aview SEGS).
    apply (KGEa TB ATABLE a HinTBc HinTB2 NI_TB'). change (req_size ATABLE) with 896. unfold AENT, ATABLE in *. lia.
  - rewrite E8, unsigned_lit_small in Ha by lia. apply (mbyte_of_aview SEGS).
    apply (KGEa TB ATABLE a HinTBc HinTB2 NI_TB'). change (req_size ATABLE) with 896. unfold AENT, ATABLE in *. lia.
  - rewrite E33, unsigned_lit_small in Ha by lia. apply (mbyte_of_aview SEGS).
    apply (KGEa hp kh a HinHPc HinHP2 NI_HP'). rewrite HRKH. lia. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 36 (map (getr regs2) CLOB)) as Ea eqn:HEa in HS.
assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDa : forall n, (n < 36)%nat -> ew Ea n = ew E n) by (intros n Hn; rewrite HEa; apply YN3v.ew_havoc_old; exact Hn).
assert (HAEa : env_agree 32 (Ereg regsc (gl_extra hp (hp + 8 * Z.of_nat i) ka (re_nheld e))) Ea)
  by (rewrite HEa; apply env_agree_havoc_ge; [cbv; lia | exact HAE]).
clear HEa.
assert (SHOKa : sh_ok SEGS BxL gl_SH Ea (mrestrict (w_H W2) mem2)).
{ assert (HBxa : U Ea BxL = SHADOW_OFF)
    by (unfold BxL; rewrite (U_atom Ea 19 SB ltac:(rewrite OLDa by (cbv; lia); exact E19)) by (unfold SB; lia); reflexivity).
  unfold sh_ok, gl_SH. constructor; [|constructor; [|constructor; [|constructor]]].
  - apply (shent_ok_of_range SEGS (w_H W2) mem2 Ea BxL 9 (SA + 40) 16 (SA + 40) 0 8
      ltac:(apply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly2 S2 Hg2 W2 mem2 md2 TB ATABLE (SA + 40) 16 HAR2
          HinTB2);
        change (req_size ATABLE) with 896; unfold AENT, ATABLE in *; lia) HBxa);
    [rewrite (U_atom Ea 9 (SA + 40) ltac:(rewrite OLDa by (cbv; lia); exact E9)) by lia; reflexivity | lia | lia |].
    intros xx Hxx. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia.
  - apply (shent_ok_of_range SEGS (w_H W2) mem2 Ea BxL 8 (SA + 40) 16 (SA + 48) 0 8
      ltac:(apply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly2 S2 Hg2 W2 mem2 md2 TB ATABLE (SA + 40) 16 HAR2
          HinTB2);
        change (req_size ATABLE) with 896; unfold AENT, ATABLE in *; lia) HBxa);
    [rewrite (U_atom Ea 8 (SA + 48) ltac:(rewrite OLDa by (cbv; lia); exact E8)) by lia; reflexivity | lia | lia |].
    intros xx Hxx. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia.
  - apply (shent_ok_of_range SEGS (w_H W2) mem2 Ea BxL 33 (hp + 8 * Z.of_nat i) 8 (hp + 8 * Z.of_nat i) 0 8
      ltac:(apply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly2 S2 Hg2 W2 mem2 md2 hp kh (hp + 8 * Z.of_nat i) 8
          HAR2 HinHP2);
        [lia | rewrite HRKH; lia]) HBxa);
    [rewrite (U_atom Ea 33 (hp + 8 * Z.of_nat i)
       ltac:(rewrite OLDa by (cbv; lia); exact E33)) by lia; reflexivity | lia | lia |].
    intros xx Hxx. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia. }
paj_run_tok_xR RUNG HS HJ2 SHOKa Bspan. { apply awr_ok_x_of0. awr_ok_tac. }
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3.
prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8. prreg HS (10%bv : bv 5) Q10.
assert (KR2 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W2) (ms_mem ms0) a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha. apply (aview_kept_out Ea _ (w_H W2) mem2 (ms_mem ms0) HFr0 a Ha). gll_outw. }
assert (PK2 : apres_kept B W2 mem2 W2 (ms_mem ms0)).
{ apply gse_apres_grows. lazymatch goal with
  | K : mem_grows (mrestrict (w_H W2) mem2) (mrestrict (w_H W2) (ms_mem ms0)) |- _ => exact K end. }
pose proof HJ2 as HAR2b. apply ajournal_gx_AR_xR in HAR2b.
(* the block list at the free: the key first, then what survives it *)
assert (PERMX : Permutation (ablocks B ly2 S2)
  ((ka, L + 1) :: ((TB, ATABLE) :: (hp, kh) :: KS ++ OB2 ++ rest))).
{ eapply perm_trans; [exact HPb|].
  eapply perm_trans; [apply Permutation_app_head; exact HR1|].
  eapply perm_trans; [apply Permutation_app_comm|]. cbn [app].
  eapply perm_trans;
  [apply perm_skip, perm_skip, perm_skip; rewrite <- app_assoc;
   apply Permutation_app_head, Permutation_app_comm|].
  eapply perm_trans; [apply perm_skip, perm_swap|]. apply perm_swap. }
(* the same block list in the cut's form, for the free's count (gse_cnt_at) *)
assert (PERMY : Permutation (ablocks B ly2 S2)
  ((TB, ATABLE) :: gse_hpblk hp kh ++ kblks (skipn i (re_keys e)) ++ OB2 ++ rest)).
{ rewrite ESK, gll_kblks_cons. unfold gse_hpblk. rewrite (proj2 (Z.eqb_neq hp 0) Hnz). cbn [app].
  fold ka. fold L. fold KS.
  eapply perm_trans; [exact PERMX|]. eapply perm_trans; [apply perm_swap|]. apply perm_skip. apply perm_swap. }
assert (MOKfree : mo_ok MT S2 (mo_free MT)).
{ apply (mo_ok_le MT MTL S2 _ (mo_free MT + gse_cost MT (ge_ctl (gse_c r0) L) mx (ge_no (gse_c r0) (gse_no r0) L)
    cap2 (skipn (S i) (gse_keys e)))); [|lia].
  apply (mo_ok_step MT MTL Sc S2 (ge_cost MT (gse_c r0) mx (gse_no r0) (gse_cap r0) L) _);
  [apply (mo_ok_le MT MTL Sc _ _ MOKi); lia | exact HM2]. }
pmkst HS. rewrite HBfree.
eapply (SRrG_bind SEGS R R_trans).
{ eapply (gse_free_xR B PST ARx MT RP LAWS CTX_AFREE IMGC BLKN R RO RO_ARx AFREE_R AFREEN_R (G_SL B RG) W2 (ms_regs ms0) (ms_mem ms0) GSE_STK
    (spZ regs) (gse_FP SA e cap out) ly S0 Hp W mem md [] ly2 S2 Hg2 _ (k + k1) ka (L + 1)
    ((TB, ATABLE) :: (hp, kh) :: KS ++ OB2 ++ rest) (-80) (Z_to_bv 64 (BASE + A_gse_ret2)) [] krf HJ2).
  - unfold gse_hpblk. rewrite (proj2 (Z.eqb_neq ka 0) ltac:(lia)). cbn [app]. exact PERMX.
  - rewrite Q10, OLDa by (cbv; lia). exact E34.
  - change (spZ (ms_regs ms0)) with (bv_unsigned (getr (ms_regs ms0) 2)).
    rewrite Q2, OLDa by (cbv; lia). rewrite Usp. unfold GSE_FRAME. lia.
  - reflexivity.
  - lia.
  - unfold ASTACK. lia.
  - rewrite Q3, OLDa by (cbv; lia). rewrite E3, R3. exact Hgp.
  - rewrite Q4, OLDa by (cbv; lia). rewrite E4, R4. exact Htp.
  - rewrite ER2. exact Q1.
  - rewrite ER2. apply ret_ok_codeptr_v; [lia | reflexivity].
  - eapply (achain_chain_pre ly2 _ (spZ (ms_regs ms0)) (s0Z (ms_regs ms0)) []).
    + apply achain_low. unfold s0Z. rewrite Q8, OLDa by (cbv; lia). rewrite E8.
      rewrite unsigned_lit_small by lia. lia.
    + change (spZ (ms_regs ms0)) with (bv_unsigned (getr (ms_regs ms0) 2)).
      rewrite Q2, OLDa by (cbv; lia). rewrite Usp. unfold GSE_FRAME. lia.
    + reflexivity.
    + unfold raZ. rewrite Q1. rewrite unsigned_lit_small by lia. lia.
  - (* the free's caller context: the chain is [], the trace the singleton [gestures_end + 0xbc] (ra 0x82610) *)
    cbn [spine map]. replace (raZ (ms_regs ms0)) with (BASE + AF_fr_gestures_end + 0xbc); [exact HCTX_gse_loop|].
    unfold raZ. rewrite Q1, unsigned_lit_small by lia. first [lia | unfold AF_fr_gestures_end in *; lia].
  - exact HRM2.
  - (* the room round: the free's count, from the entry's *)
    unfold cnt_ok. eapply (gse_cnt_at RP _ _ e (ablocks B ly S0) (ablocks B ly2 S2) TB i cap out cap2 out2 rest);
    [| exact HPERM0 | exact PERMY | exact CNT0]; intros P; cbv [gse_pk]; lia.
  - intros _ j Hj. unfold gse_FP. apply (proj2 (inFP_cons _ _ _ _)). right.
    apply (inFP_ablocks_fp (gse_blks e ++ aout_blks cap out) ka (L + 1) j); [|exact Hj].
    apply in_or_app. left. rewrite gse_blks_split. apply in_or_app. right.
    exact (in_map (fun kk => (key_addr kk, Z.of_nat (length (key_text kk)) + 1)) (re_keys e) ki
      (nth_error_In _ _ Eki)).
  - exact MOKfree. }
cbv beta.
intros W3 c3 Hwle3 (ly3 & S3 & Hg3 & regs3 & mem3 & md3 & -> & HJ3 & HP3 & HPerm3 & HK3 & HM3 & HRM3 & HE3 & HPK3).
destruct HK3 as (HK3a & HK3b & HK3c & HK3d & HK3e & HK3f).
assert (HAR3 : ARx ly3 S3 Hg3 W3 mem3 md3) by (eapply ajournal_gx_AR_xR; exact HJ3).
assert (KFR : forall p n a, In (p, n) (ablocks B ly2 S2) -> (p, n) <> (ka, L + 1) -> p <= a < p + req_size n ->
  aview SEGS (w_H W3) mem3 a = aview SEGS (w_H W2) (ms_mem ms0) a).
{ intros p n a Hq1 Hq2 Hqa. replace a with (p + (a - p)) by lia.
  apply (HK3b p n (a - p) Hq1 ltac:(lia)). intros (Hz & Hr).
  destruct (gll_disj_x ly2 S2 Hg2 W2 (ms_mem ms0) _ p n ka (L + 1) HAR2b Hq1 HinKA2 Hq2) as [Hdd | Hdd];
  rewrite ?HRKA in Hdd; lia. }
(* the bytes of a block that both calls kept, from the loop head to after the free *)
assert (KBLK : forall p n a, In (p, n) (ablocks B lyc Sc) -> ~ In (p, n) OB -> (p, n) <> (ka, L + 1) ->
  p <= a < p + req_size n -> aview SEGS (w_H W3) mem3 a = aview SEGS (w_H Wc) memc a).
{ intros p n a Hq1 Hq2 Hq3 Hqa.
  destruct (alx_blocks _ _ _ LAWS lyc Sc Hpk Wc memc mdc p n HARc Hq1) as (_ & Hq4 & Hqc & _).
  assert (Hq2' : In (p, n) (ablocks B ly2 S2)) by (apply KEEPB; [exact Hq1 | exact Hq2]).
  rewrite (KFR p n a Hq2' Hq3 Hqa), (KR2 a ltac:(lia)), (KGEa p n a Hq1 Hq2' Hq2 Hqa).
  apply KR1. lia. }
assert (KIMG : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) ->
  ~ (as_errno B <= a < as_errno B + 4) -> ~ Exists (in_zr a) PST -> ~ inG (G_SL B RG) a ->
  aview SEGS (w_H W3) mem3 a = aview SEGS (w_H Wc) memc a).
{ intros a Hi Ho He Hq Hng. pose proof (pa_img_range a Hi).
  rewrite (HK3c a Hi Ho He), (KR2 a ltac:(lia)), (KGEi a Hi Ho He Hq Hng). apply KR1. lia. }
assert (KHI : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (spZ regs - 80 - GE_STK <= a < spZ regs - 80) ->
  aview SEGS (w_H W3) mem3 a = aview SEGS (w_H Wc) memc a).
{ intros a Ha Hno.
  rewrite (HK3a a Ha ltac:(unfold ASTACK; lia)), (KR2 a ltac:(lia)), (KGEh a Ha Hno). apply KR1. lia. }
(* ---- back at 0x82610: nheld's load4 check, i++, 8i += 8, and the branch *)
assert (HinTB3 : In (TB, ATABLE) (ablocks B ly3 S3))
  by (eapply Permutation_in; [apply Permutation_sym; exact HPerm3 | left; reflexivity]).
assert (HinHP3 : In (hp, kh) (ablocks B ly3 S3))
  by (eapply Permutation_in; [apply Permutation_sym; exact HPerm3 | right; left; reflexivity]).
assert (HinKS3 : forall bb, In bb KS -> In bb (ablocks B ly3 S3)).
{ intros bb Hbb. eapply Permutation_in; [apply Permutation_sym; exact HPerm3|].
  right; right. apply in_or_app. left. exact Hbb. }
assert (HinOB3 : forall bb, In bb OB2 -> In bb (ablocks B ly3 S3)).
{ intros bb Hbb. eapply Permutation_in; [apply Permutation_sym; exact HPerm3|].
  right; right. apply in_or_app. right. apply in_or_app. left. exact Hbb. }
jafter_call_keep_pi HS 52%nat regs3 (mrestrict (w_H W3) mem3) HP3 [0; 1; 2]%nat HS3.
match type of HS3 with ?ty -> _ => assert (HRK : ty); [|specialize (HS3 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| | | apply Forall_nil];
  split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; intros a Ha; try lia.
  - rewrite OLDa in Ha by (cbv; lia). rewrite E9, unsigned_lit_small in Ha by lia.
    apply (mbyte_of_aview SEGS).
    apply (KFR TB ATABLE a HinTB2 DTB);
    change (req_size ATABLE) with 896; lia.
  - rewrite OLDa in Ha by (cbv; lia). rewrite E8, unsigned_lit_small in Ha by lia.
    apply (mbyte_of_aview SEGS).
    apply (KFR TB ATABLE a HinTB2 DTB);
    change (req_size ATABLE) with 896; lia.
  - rewrite OLDa in Ha by (cbv; lia). rewrite E33, unsigned_lit_small in Ha by lia.
    apply (mbyte_of_aview SEGS).
    apply (KFR hp kh a HinHP2 DHP); rewrite HRKH; lia. }
clear HS. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
remember (havoc Ea 52 (map (getr regs3) CLOB)) as Eb eqn:HEb in HS.
assert (HEIb : img_env VAL A_LIM Eb) by (rewrite HEb; apply img_env_havoc; [exact HEIa | cbv; lia]).
assert (OLDb : forall n, (n < 52)%nat -> ew Eb n = ew Ea n) by (intros n Hn; rewrite HEb; apply YN3v.ew_havoc_old; exact Hn).
assert (HAEb : env_agree 32 (Ereg regsc (gl_extra hp (hp + 8 * Z.of_nat i) ka (re_nheld e))) Eb)
  by (rewrite HEb; apply env_agree_havoc_ge; [cbv; lia | exact HAEa]).
clear HEb.
assert (F8 : ew Eb 8 = Z_to_bv 64 (SA + 48)) by (rewrite OLDb, OLDa by (cbv; lia); exact E8).
assert (F9 : ew Eb 9 = Z_to_bv 64 (SA + 40)) by (rewrite OLDb, OLDa by (cbv; lia); exact E9).
assert (F19 : ew Eb 19 = Z_to_bv 64 SB) by (rewrite OLDb, OLDa by (cbv; lia); exact E19).
assert (F20 : ew Eb 20 = Z_to_bv 64 (8 * Z.of_nat i)) by (rewrite OLDb, OLDa by (cbv; lia); exact E20).
assert (F21 : ew Eb 21 = Z_to_bv 64 (Z.of_nat i)) by (rewrite OLDb, OLDa by (cbv; lia); exact E21).
assert (F33 : ew Eb 33 = Z_to_bv 64 (hp + 8 * Z.of_nat i)) by (rewrite OLDb, OLDa by (cbv; lia); exact E33).
assert (F35 : ew Eb 35 = Z_to_bv 64 (re_nheld e)) by (rewrite OLDb, OLDa by (cbv; lia); exact E35).
assert (Uspb : bv_unsigned (ew Eb 2) = spZ regs - GSE_FRAME) by (rewrite OLDb, OLDa by (cbv; lia); exact Usp).
assert (SHOKb : sh_ok SEGS BxL gl_SH Eb (mrestrict (w_H W3) mem3)).
{ assert (HBxb : U Eb BxL = SHADOW_OFF)
    by (unfold BxL; rewrite (U_atom Eb 19 SB F19) by (unfold SB; lia); reflexivity).
  unfold sh_ok, gl_SH. constructor; [|constructor; [|constructor; [|constructor]]].
  - apply (shent_ok_of_range SEGS (w_H W3) mem3 Eb BxL 9 (SA + 40) 16 (SA + 40) 0 8
      ltac:(apply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly3 S3 Hg3 W3 mem3 md3 TB ATABLE (SA + 40) 16 HAR3
          HinTB3);
        change (req_size ATABLE) with 896; lia) HBxb);
    [rewrite (U_atom Eb 9 (SA + 40) F9) by lia; reflexivity | lia | lia |].
    intros xx Hxx. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia.
  - apply (shent_ok_of_range SEGS (w_H W3) mem3 Eb BxL 8 (SA + 40) 16 (SA + 48) 0 8
      ltac:(apply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly3 S3 Hg3 W3 mem3 md3 TB ATABLE (SA + 40) 16 HAR3
          HinTB3);
        change (req_size ATABLE) with 896; lia) HBxb);
    [rewrite (U_atom Eb 8 (SA + 48) F8) by lia; reflexivity | lia | lia |].
    intros xx Hxx. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia.
  - apply (shent_ok_of_range SEGS (w_H W3) mem3 Eb BxL 33 (hp + 8 * Z.of_nat i) 8 (hp + 8 * Z.of_nat i) 0 8
      ltac:(apply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly3 S3 Hg3 W3 mem3 md3 hp kh (hp + 8 * Z.of_nat i) 8
          HAR3 HinHP3);
        [lia | rewrite HRKH; lia]) HBxb);
    [rewrite (U_atom Eb 33 (hp + 8 * Z.of_nat i) F33) by lia; reflexivity | lia | lia |].
    intros xx Hxx. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia. }
paj_run_tok_xR RUNG HS HJ3 SHOKb Bspan. { apply awr_ok_x_of0. awr_ok_tac. }
assert (KR3 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W3) (ms_mem ms1) a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha. apply (aview_kept_out Eb _ (w_H W3) mem3 (ms_mem ms1) HFr1 a Ha). gll_outw. }
assert (PK3 : apres_kept B W3 mem3 W3 (ms_mem ms1)).
{ apply gse_apres_grows. lazymatch goal with
  | K : mem_grows (mrestrict (w_H W3) mem3) (mrestrict (w_H W3) (ms_mem ms1)) |- _ => exact K end. }
(* ---- the invariant at i + 1, from any memory the last run reaches *)
assert (LEB : length (bzs (entry_bytes e)) = 56%nat).
{ unfold bzs. rewrite length_map, gse_entry_split, !length_app, (gse_epre_len e Hp1).
  rewrite OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.length_le8,
    OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.length_le4, Hp2. reflexivity. }
pose proof (blk_off_imgP_x B ARx LAWS IMGC BLKN lyc Sc Hpk Wc memc mdc TB ATABLE HARc HinTBc) as HTBoff.
change (req_size ATABLE) with 896 in HTBoff. unfold off_img in HTBoff.
assert (ERC : gse_c (gse_run c O mx no cap (firstn (S i) (gse_keys e))) = ge_ctl (gse_c r0) L)
  by (rewrite (gll_firstn_S _ (gse_keys e) i (key_text ki) Exs),
      (gse_run_app (firstn i (gse_keys e)) [key_text ki] c O mx no cap); reflexivity).
assert (ERO : gse_O (gse_run c O mx no cap (firstn (S i) (gse_keys e))) = ge_O (gse_c r0) (gse_O r0) (key_text ki))
  by (rewrite (gll_firstn_S _ (gse_keys e) i (key_text ki) Exs),
      (gse_run_app (firstn i (gse_keys e)) [key_text ki] c O mx no cap); reflexivity).
assert (ERN : gse_no (gse_run c O mx no cap (firstn (S i) (gse_keys e))) = ge_no (gse_c r0) (gse_no r0) L)
  by (rewrite (gll_firstn_S _ (gse_keys e) i (key_text ki) Exs),
      (gse_run_app (firstn i (gse_keys e)) [key_text ki] c O mx no cap); reflexivity).
assert (ERP : gse_cap (gse_run c O mx no cap (firstn (S i) (gse_keys e))) = cap2)
  by (rewrite (gll_firstn_S _ (gse_keys e) i (key_text ki) Exs),
      (gse_run_app (firstn i (gse_keys e)) [key_text ki] c O mx no cap); reflexivity).
assert (ERS : gse_spent MT c mx no cap (firstn (S i) (gse_keys e)) =
  gse_spent MT c mx no cap (firstn i (gse_keys e)) +
  (ge_cost MT (gse_c r0) mx (gse_no r0) (gse_cap r0) L + mo_free MT + 0))
  by (rewrite (gll_firstn_S _ (gse_keys e) i (key_text ki) Exs),
      (gse_spent_app MT (firstn i (gse_keys e)) [key_text ki] c O mx no cap); reflexivity).
assert (BB : blocks_bytes S3 <= blocks_bytes Sc + tr_net (ge_tr (gse_c r0) mx (gse_no r0) (gse_cap r0) L) - (L + 1)).
{ assert (HGT : tr_net (ge_tr (gse_c r0) mx (gse_no r0) (gse_cap r0) L) = cap2 - gse_cap r0)
    by (apply ge_tr_net; lia).
  rewrite (blocks_bytes_bsum B lyc Sc), (blocks_bytes_bsum B ly3 S3).
  rewrite (bsum_perm _ _ HPerm3), (bsum_perm _ _ HPa).
  rewrite ?bsum_cons, ?bsum_app.
  rewrite (bsum_perm _ _ HR1), ?bsum_cons, ?bsum_app. cbn [snd].
  assert (HOBz : bsum (aout_blks (gse_cap r0) outi) = gse_cap r0).
  { unfold aout_blks. destruct (Z.eqb_spec (gse_cap r0) 0); cbn [bsum fold_right snd]; lia. }
  assert (HOB2z : bsum OB2 <= cap2).
  { unfold OB2, aout_blks. destruct (Z.eqb_spec cap2 0); cbn [bsum fold_right snd]; lia. }
  lia. }
assert (FIN : forall (regs4 : bvmap 5 word) mem4 md4 kk,
  (forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W3) mem4 a = aview SEGS (w_H W3) (ms_mem ms1) a) ->
  apres_kept B W3 (ms_mem ms1) W3 mem4 ->
  ajournal_gx_xR SEGS B PST ARx R (G_SL B RG) 0 [] GSE_STK (spZ regs) (gse_FP SA e cap out) ly S0 Hp W mem md []
    ly3 S3 Hg3 W3 mem4 md4 kk ->
  spZ regs4 = spZ regs - GSE_FRAME ->
  getr regs4 3 = getr regs 3 -> getr regs4 4 = getr regs 4 ->
  getr regs4 8 = w64 (SA + 48) -> getr regs4 9 = w64 (SA + 40) ->
  getr regs4 18 = w64 ((SA + 48) / 8 + SB) -> getr regs4 19 = w64 SB ->
  (forall rr, 24 <= rr <= 27 -> getr regs4 (Z_to_bv 5 rr) = getr regs (Z_to_bv 5 rr)) ->
  gse_inv_xR B PST ARx MT RP MMAX RG R W ly S0 Hp regs mem md SA TB e c O mx no cap out rest (S i) W3 ly3 S3 Hg3 regs4 mem4 md4
    kk out2 kr).
{ intros regs4 mem4 md4 kk KV4 PK4 HJ4 Hsp4 H34 H44 H84 H94 H184 H194 H2427.
  assert (KALL : forall p n a, In (p, n) (ablocks B lyc Sc) -> ~ In (p, n) OB -> (p, n) <> (ka, L + 1) ->
    p <= a < p + req_size n -> aview SEGS (w_H W3) mem4 a = aview SEGS (w_H Wc) memc a).
  { intros p n a Hq1 Hq2 Hq3 Hqa.
    destruct (alx_blocks _ _ _ LAWS lyc Sc Hpk Wc memc mdc p n HARc Hq1) as (_ & Hq4 & Hqc & _).
    rewrite (KV4 a ltac:(lia)), (KR3 a ltac:(lia)). exact (KBLK p n a Hq1 Hq2 Hq3 Hqa). }
  assert (KALLi : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) ->
    ~ (as_errno B <= a < as_errno B + 4) -> ~ Exists (in_zr a) PST -> ~ inG (G_SL B RG) a ->
    aview SEGS (w_H W3) mem4 a = aview SEGS (w_H Wc) memc a).
  { intros a Hi Ho He Hq Hng. pose proof (pa_img_range a Hi).
    rewrite (KV4 a ltac:(lia)), (KR3 a ltac:(lia)). exact (KIMG a Hi Ho He Hq Hng). }
  assert (GEB4 : garr8 SEGS (arm W3 mem4) SA (bzs (entry_bytes e))).
  { apply (gse_garr8_kept (w_H Wc) (w_H W3) memc mem4 SA _ HEB). intros b Hb. rewrite LEB in Hb.
    apply (KALL TB ATABLE b HinTBc NI_TB' DTB). change (req_size ATABLE) with 896. lia. }
  assert (AWR4 : awr W3 mem4 SA AENT).
  { intros j Hj. unfold AENT in Hj.
    destruct (aview SEGS (w_H W3) mem4 (SA + j)) as [v|] eqn:Ev.
    - apply (gse_writable_view (w_H W3) mem4 (SA + j) v ltac:(lia) Ev).
      intros Hrom.
      assert (Hi : in_img SEGS (SA + j))
        by (destruct Hrom as (sg & Hsg & _ & Hr'); exists sg; split; [exact Hsg | lia]).
      pose proof (pa_img_range (SA + j) Hi). lia.
    - exfalso. apply (gse_view_garr8 (w_H W3) mem4 SA _ j GEB4 ltac:(rewrite LEB; lia)).
      exact Ev. }
  assert (GHP4 : garr8 SEGS (arm W3 mem4) hp (bzs (key_ptrs (re_keys e)))).
  { apply (gse_garr8_kept (w_H Wc) (w_H W3) memc mem4 hp _ GHP). intros b Hb.
    unfold bzs in Hb. rewrite length_map, gse_key_ptrs_len in Hb.
    apply (KALL hp kh b HinHPc NI_HP' DHP). rewrite HRKH. unfold re_nheld in Hkh. lia. }
  assert (FK4 : Forall (key_ok W3 mem4) (skipn (S i) (re_keys e))).
  { rewrite Forall_forall in FKREST |- *. intros kk' Hkk'.
    destruct (FKREST kk' Hkk') as (GK' & NZ' & LN').
    assert (Hkb : In (key_addr kk', Z.of_nat (length (key_text kk')) + 1) KS)
      by (unfold KS, kblks; exact (in_map _ _ _ Hkk')).
    split; [|split; [exact NZ' | exact LN']].
    apply (gse_garr8_kept (w_H Wc) (w_H W3) memc mem4 (key_addr kk') _ GK'). intros b Hb.
    unfold bzs in Hb. rewrite length_map, length_app in Hb. cbn [length] in Hb.
    apply (KALL (key_addr kk') (Z.of_nat (length (key_text kk')) + 1) b (HinKSc _ Hkb) (NI_KS' _ Hkb) (DKS _ Hkb)).
    assert (HR : req_size (Z.of_nat (length (key_text kk')) + 1) = Z.of_nat (length (key_text kk')) + 1)
      by (unfold req_size; destruct (Z.eqb_spec (Z.of_nat (length (key_text kk')) + 1) 0); lia).
    rewrite HR. lia. }
  assert (G54 : garr8 SEGS (arm W3 mem4) (VAL A_lit_end5) (bzs END5)).
  { apply (gse_garr8_kept (w_H Wc) (w_H W3) memc mem4 _ _ G5). intros b Hb.
    change (Z.of_nat (length (bzs END5))) with 5 in Hb.
    destruct (HEND5G b Hb) as (Hng & Hno & Hne).
    exact (KALLi b (HEND5I b Hb) Hno Hne (HEND5P b Hb) Hng). }
  assert (SLOT : forall off v, val_mem SEGS (arm Wc memc) (spZ regs - off) 8 v -> 8 <= off <= 72 ->
    val_mem SEGS (arm W3 mem4) (spZ regs - off) 8 v).
  { intros off v Hv Hoff. apply (gse_vm_kept (w_H Wc) (w_H W3) memc mem4 _ 8 v Hv).
    intros b Hb. rewrite (KV4 b ltac:(lia)), (KR3 b ltac:(lia)).
    apply KHI; [lia | unfold GE_STK, GE_FRAME, SL_STK, SL_FRAME, ASTACK, ESTACK; lia]. }
  unfold gse_inv_xR. cbv zeta. rewrite ERC, ERO, ERN, ERP, ERS.
  split; [exact HJ4|].
  split.
  { eapply gse_apres_trans; [exact HPK|]. eapply gse_apres_trans; [exact PK1|].
    eapply gse_apres_trans; [exact HAK2|]. eapply gse_apres_trans; [exact PK2|].
    eapply gse_apres_trans; [exact HPK3|]. eapply gse_apres_trans; [exact PK3 | exact PK4]. }
  split.
  { apply (mo_le_mono MT MTL S0 S3 _ _
      (mo_le_trans MT MTL S0 Sc S3 _ _ HML (mo_le_trans MT MTL Sc S2 S3 _ _ HM2 HM3))). lia. }
  split; [exact (mo_ok_step MT MTL Sc S3 _ _ MOKi (mo_le_trans MT MTL Sc S2 S3 _ _ HM2 HM3))|].
  split; [exact HRM3|].
  split; [exact (gll_room_mono _ _ (blocks_bytes Sc + tr_net (ge_tr (gse_c r0) mx (gse_no r0) (gse_cap r0) L) - (L + 1))
    _ _ _ _ BB ROOMr)|].
  split.
  { assert (EHB : gse_hpblk hp kh = [(hp, kh)])
      by (unfold gse_hpblk; rewrite (proj2 (Z.eqb_neq hp 0) Hnz); reflexivity).
    change (gse_hpblk (re_hp e) (re_kh e)) with (gse_hpblk hp kh). rewrite EHB. cbn [app]. exact HPerm3. }
  split.
  { apply (gll_aout_kept ly2 S2 W2 mem2 ly3 S3 W3 mem4 _ _ _ _ _ _ HO2).
    - intros rr a Hrr Ha.
      destruct (gll_aout_rom_x ly2 S2 Hg2 W2 mem2 md2 _ _ _ _ _ _ HAR2 HO2 rr a Hrr Ha) as [Ha64 Hrom].
      rewrite (KV4 a Ha64), (KR3 a Ha64).
      destruct (gse_aout_fp_cases B RG cap2 out2 rr Hrr) as [Hcs | (Hcs & ->)].
      + destruct (Z_le_gt_dec (as_errno B) a) as [Ee1 | Ee1];
        [destruct (Z_lt_ge_dec a (as_errno B + 4)) as [Ee2 | Ee2]|].
        * pose proof (HE3 (a - as_errno B) ltac:(lia)) as HEx.
          replace (as_errno B + (a - as_errno B)) with a in HEx by lia.
          rewrite HEx. apply KR2. exact Ha64.
        * destruct (HOUTG rr a Hcs Ha ltac:(lia)) as (Hi & _ & Ho).
          rewrite (HK3c a Hi Ho ltac:(lia)). apply KR2. exact Ha64.
        * destruct (HOUTG rr a Hcs Ha ltac:(lia)) as (Hi & _ & Ho).
          rewrite (HK3c a Hi Ho ltac:(lia)). apply KR2. exact Ha64.
      + cbn [fst snd] in Ha.
        destruct (gll_aout_facts ly2 S2 W2 mem2 _ _ _ _ _ _ HO2) as (_ & _ & [(Hz & _) | (Hz & _ & Hin2)]); [lia|].
        assert (Hne2 : (out2, cap2) <> (ka, L + 1)).
        { intros Hcc. apply (NI_OB2 (out2, cap2));
          [change OB2 with (aout_blks cap2 out2); unfold aout_blks;
           rewrite (proj2 (Z.eqb_neq cap2 0) ltac:(lia)); left; reflexivity|].
          rewrite Hcc. apply (Permutation_in _ (Permutation_sym HR1)). right; right; left; reflexivity. }
        pose proof (req_size_pos cap2 ltac:(lia)) as [Hq1 Hq2].
        rewrite (KFR out2 cap2 a Hin2 Hne2 ltac:(lia)). apply KR2. exact Ha64.
    - exact (gll_aout_rom_x ly2 S2 Hg2 W2 mem2 md2 _ _ _ _ _ _ HAR2 HO2).
    - intros bb Hbb. apply HinOB3. exact Hbb. }
  split; [exact GEB4|]. split; [exact AWR4|]. split; [exact GHP4|]. split; [exact FK4|]. split; [exact G54|].
  split.
  { eapply ajournal_gx_rom_view_xR;
    first [exact HJ4 | exact HROMO | exact PSTR | exact HROM0 | exact LAWS | exact pa_segs_low]. }
  split; [exact Hsp4|]. split; [exact H34|]. split; [exact H44|]. split; [exact H84|]. split; [exact H94|].
  split; [exact H184|]. split; [exact H194|]. split; [exact H2427|].
  split; [exact (SLOT 8 _ SL1 ltac:(lia))|].
  split; [exact (SLOT 16 _ SL8 ltac:(lia))|].
  split; [exact (SLOT 24 _ SL9 ltac:(lia))|].
  split; [exact (SLOT 32 _ SL18 ltac:(lia))|].
  split; [exact (SLOT 40 _ SL19 ltac:(lia))|].
  split; [exact (SLOT 48 _ SL20 ltac:(lia))|].
  split; [exact (SLOT 56 _ SL21 ltac:(lia))|].
  split; [exact (SLOT 64 _ SL22 ltac:(lia)) | exact (SLOT 72 _ SL23 ltac:(lia))]. }
assert (U21 : U Eb (SOff 21 1) = Z.of_nat i + 1) by (apply (U_atom_off Eb 21 (Z.of_nat i) 1 F21); lia).
assert (U35 : U Eb (SOff 35 0) = re_nheld e)
  by (apply (U_atom Eb 35 (re_nheld e) F35); unfold re_nheld in *; lia).
psrr_branch_tok RUNG BRR HS SHOKb Bspan.
- (* i + 1 < nheld: the invariant at i + 1 and back to 0x825c0 *)
  cbn [branch_taken] in Hc. rewrite bv_lts_signed in Hc.
  rewrite bv_signed_small in Hc by
    (repeat match goal with |- context [bv_unsigned (sv_denot ?EE ?zz)] =>
       change (bv_unsigned (sv_denot EE zz)) with (U EE zz) end;
     rewrite ?U21, ?U35; unfold re_nheld in *; lia).
  rewrite bv_signed_small in Hc by
    (repeat match goal with |- context [bv_unsigned (sv_denot ?EE ?zz)] =>
       change (bv_unsigned (sv_denot EE zz)) with (U EE zz) end;
     rewrite ?U21, ?U35; unfold re_nheld in *; lia).
  change (bv_unsigned (sv_denot Eb (SOff 21 1))) with (U Eb (SOff 21 1)) in Hc.
  change (bv_unsigned (sv_denot Eb (SOff 35 0))) with (U Eb (SOff 35 0)) in Hc.
  rewrite U21, U35 in Hc. apply Z.ltb_lt in Hc.
  assert (Hlt : (S i < length (re_keys e))%nat) by (unfold re_nheld in Hc; lia).
  paj_run_to_tok_xR RUNTOG HS HJ3 SHOKb Bspan A_gse_loop. { apply awr_ok_x_of0. awr_ok_tac. }
  assert (KR4 : forall a, 0 <= a < 2 ^ 64 ->
    aview SEGS (w_H W3) (ms_mem ms2) a = aview SEGS (w_H W3) (ms_mem ms1) a).
  { intros a Ha. apply (aview_kept_out Eb _ (w_H W3) (ms_mem ms1) (ms_mem ms2) HFr2 a Ha). gll_outw. }
  assert (PK4 : apres_kept B W3 (ms_mem ms1) W3 (ms_mem ms2)).
  { apply gse_apres_grows. lazymatch goal with
    | K : mem_grows (mrestrict (w_H W3) (ms_mem ms1)) (mrestrict (w_H W3) (ms_mem ms2)) |- _ => exact K end. }
  pose proof (regs_kept_of_st_ok_pi _ _ _ regsc (gl_extra hp (hp + 8 * Z.of_nat i) ka (re_nheld e))
    [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 19%bv; 23%bv; 24%bv; 25%bv; 26%bv; 27%bv] HS HAEb
    ltac:(vm_compute; reflexivity)) as HK.
  cbn [ms_regs restrict] in HK.
  prreg HS (18%bv : bv 5) N18. prreg HS (20%bv : bv 5) N20.
  prreg HS (21%bv : bv 5) N21. prreg HS (22%bv : bv 5) N22.
  pmkst HS.
  eapply (IH W ly S0 Hp regs mem md ch SA TB e c O mx no cap out rest (S i) W3 ly3 S3 Hg3
    (ms_regs ms2) (ms_mem ms2) _ _ out2 kr ltac:(lia) HPREB Hlt).
  + apply FIN.
    * intros a Ha. exact (KR4 a Ha).
    * exact PK4.
    * exact HJ3.
    * change (spZ (ms_regs ms2)) with (bv_unsigned (getr (ms_regs ms2) 2)).
      rewrite (HK 2%bv ltac:(cbv; tauto)). exact HSP.
    * rewrite (HK 3%bv ltac:(cbv; tauto)). exact R3.
    * rewrite (HK 4%bv ltac:(cbv; tauto)). exact R4.
    * rewrite (HK 8%bv ltac:(cbv; tauto)). exact R8.
    * rewrite (HK 9%bv ltac:(cbv; tauto)). exact R9.
    * rewrite N18, F8, F19. apply gse_shadow_w. lia.
    * rewrite (HK 19%bv ltac:(cbv; tauto)). exact R19.
    * intros rr Hrr. rewrite <- (R2427 rr Hrr). apply HK.
      assert (Hr4 : rr = 24 \/ rr = 25 \/ rr = 26 \/ rr = 27) by (clear - Hrr; lia).
      clear - Hr4. destruct Hr4 as [-> | [-> | [-> | ->]]]; cbn [In];
      repeat first [left; apply bv_eq; reflexivity | right].
  + rewrite N20, F20, unsigned_lit_small by lia. unfold w64. f_equal. rewrite Nat2Z.inj_succ. lia.
  + rewrite N21, F21, unsigned_lit_small by lia. unfold w64. f_equal. rewrite Nat2Z.inj_succ. lia.
  + rewrite N22, F9, F19. apply gse_shadow_w. lia.
  + rewrite (HK 23%bv ltac:(cbv; tauto)). exact R23.
- (* i + 1 = nheld: the stretch after the loop *)
  cbn [branch_taken] in Hc. rewrite bv_lts_signed in Hc.
  rewrite bv_signed_small in Hc by
    (repeat match goal with |- context [bv_unsigned (sv_denot ?EE ?zz)] =>
       change (bv_unsigned (sv_denot EE zz)) with (U EE zz) end;
     rewrite ?U21, ?U35; unfold re_nheld in *; lia).
  rewrite bv_signed_small in Hc by
    (repeat match goal with |- context [bv_unsigned (sv_denot ?EE ?zz)] =>
       change (bv_unsigned (sv_denot EE zz)) with (U EE zz) end;
     rewrite ?U21, ?U35; unfold re_nheld in *; lia).
  change (bv_unsigned (sv_denot Eb (SOff 21 1))) with (U Eb (SOff 21 1)) in Hc.
  change (bv_unsigned (sv_denot Eb (SOff 35 0))) with (U Eb (SOff 35 0)) in Hc.
  rewrite U21, U35 in Hc. apply Z.ltb_ge in Hc.
  assert (Heq : S i = length (re_keys e)) by (unfold re_nheld in Hc; lia).
  paj_run_to_tok_xR RUNTOG HS HJ3 SHOKb Bspan A_gse_tail. { apply awr_ok_x_of0. awr_ok_tac. }
  assert (KR4 : forall a, 0 <= a < 2 ^ 64 ->
    aview SEGS (w_H W3) (ms_mem ms2) a = aview SEGS (w_H W3) (ms_mem ms1) a).
  { intros a Ha. apply (aview_kept_out Eb _ (w_H W3) (ms_mem ms1) (ms_mem ms2) HFr2 a Ha). gll_outw. }
  assert (PK4 : apres_kept B W3 (ms_mem ms1) W3 (ms_mem ms2)).
  { apply gse_apres_grows. lazymatch goal with
    | K : mem_grows (mrestrict (w_H W3) (ms_mem ms1)) (mrestrict (w_H W3) (ms_mem ms2)) |- _ => exact K end. }
  pose proof (regs_kept_of_st_ok_pi _ _ _ regsc (gl_extra hp (hp + 8 * Z.of_nat i) ka (re_nheld e))
    [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 19%bv; 23%bv; 24%bv; 25%bv; 26%bv; 27%bv] HS HAEb
    ltac:(vm_compute; reflexivity)) as HK.
  cbn [ms_regs restrict] in HK.
  prreg HS (18%bv : bv 5) N18.
  pmkst HS.
  eapply (GSE_TAIL_XR W ly S0 Hp regs mem md ch SA TB e c O mx no cap out rest W3 ly3 S3 Hg3
    (ms_regs ms2) (ms_mem ms2) _ _ out2 kr HPREB).
  rewrite <- Heq. apply FIN.
  + intros a Ha. exact (KR4 a Ha).
  + exact PK4.
  + exact HJ3.
  + change (spZ (ms_regs ms2)) with (bv_unsigned (getr (ms_regs ms2) 2)).
    rewrite (HK 2%bv ltac:(cbv; tauto)). exact HSP.
  + rewrite (HK 3%bv ltac:(cbv; tauto)). exact R3.
  + rewrite (HK 4%bv ltac:(cbv; tauto)). exact R4.
  + rewrite (HK 8%bv ltac:(cbv; tauto)). exact R8.
  + rewrite (HK 9%bv ltac:(cbv; tauto)). exact R9.
  + rewrite N18, F8, F19. apply gse_shadow_w. lia.
  + rewrite (HK 19%bv ltac:(cbv; tauto)). exact R19.
  + intros rr Hrr. rewrite <- (R2427 rr Hrr). apply HK.
    assert (Hr4 : rr = 24 \/ rr = 25 \/ rr = 26 \/ rr = 27) by (clear - Hrr; lia).
    clear - Hr4. destruct Hr4 as [-> | [-> | [-> | ->]]]; cbn [In];
    repeat first [left; apply bv_eq; reflexivity | right].
Qed.
(* :1375 pb_gse_loop_x *)
Theorem pb_gse_loop_xR : gse_loop_at_xR B PST ARx MT RP MMAX RG R (BASE + A_gse_loop).
Proof.
intros W ly S Hp regs mem md ch SA TB e c O mx no cap out rest i Wc lyc Sc Hpk regsc memc mdc k outi kr
  HPREB Hilt HINV R20 R21 R22 R23.
exact (gll_loop_xR (length (re_keys e) - i) W ly S Hp regs mem md ch SA TB e c O mx no cap out rest i
  Wc lyc Sc Hpk regsc memc mdc k outi kr (Nat.le_refl _) HPREB Hilt HINV R20 R21 R22 R23).
Qed.
End wR.

End c.

(* ---- THE AR STATEMENT, re-derived (route (b), step 3, CONVERSION.md (sha256 1015972e02a9; internal record) 3.): pb_gse_loop's statement is the AR walk's,
   byte-identical, now a corollary of pb_gse_loop_x at ARx := ARi0 (cgif's AR with the head set empty), PST := [].
   Its Section takes LX0 (the laws at ARi0) in place of LAWS: the instance builds it once,
   W_journal_x.AR_laws_x_ARi0 (YCbqG.AR_laws_x_of_AR ..).  The bridges: W_gse_cut.gse_loop_at_x_AR0 (conclusion),
   gse_tail_at_x_of_AR0 (GSE_TAIL), W_contract_x.ge_spec_x_of_AR0 (GE).  The free rules stay AR rules here; their
   caller-context forms at CTX := [[gestures_end + 0xbc]; [gestures_end + 0xfc]] (the two free sites of
   gestures_end) come from W_journal.afree_cf_rule_c_weak / afree_null_cf_rule_c_weak and go to ARi0 through
   W_journal_x.afree_cf_rule_c_x_of_AR0 / afree_null_cf_rule_c_x_of_AR0.  HP0 at ARi0 is ARi0_hp0; IMGC / BLKN are
   W_kit_x.AR_imgc / AR_blkn; PSTR and HEND5P hold at PST = []. ---- *)
Section cAR.
Variable B : asyms.
Variable MT : ameter_ops.
Variable MMAX : Z.
Variable RG : rep_globals.
Hypothesis LX0 : AR_laws_x SEGS B (ARi0 SEGS B) 0.
Hypothesis TL : PALib B.
Hypothesis HG : gx_ok SEGS B (G_SL B RG).
Hypothesis MTL : ameter_laws MT.
Hypothesis GE : ge_spec B MT MMAX RG (BASE + AF_fr_gesture_end).
Hypothesis AFREE : afree_cf_rule SEGS B MT.
Hypothesis AFREEN : afree_null_cf_rule SEGS B MT.
Hypothesis HROMO : rom_out SEGS B (G_SL B RG).
Hypothesis HOUTG : forall r a, In r (aout_fp B RG 0 0) -> fst r <= a < snd r -> ~ (as_errno B <= a < as_errno B + 4) ->
  in_img SEGS a /\ ~ in_rom SEGS a /\ ~ Exists (in_zr a) (as_owned_static B).
(* " end\0" lies in the image (true at every placement: it is .rodata).  The zero-shadow claim that stood here before
   is FALSE at the instance (partial granule: shadow byte 5 at 0x7fffc1e0, W3's measurement) and was never needed. *)
Hypothesis HEND5I : forall a, VAL A_lit_end5 <= a < VAL A_lit_end5 + 5 -> in_img SEGS a.
(* HEND5G holds for EXACTLY [VAL A_lit_end5, VAL A_lit_end5 + 5) = [0x20f00, 0x20f05) on both images and MUST NOT BE
   WIDENED: its `~ owned_static` clause is TRUE (StartupTrace's tfib_lit_end5_not_owned_static, a working branch
   5fab70f4113; ZeroGlobals and W1Verify measured the same rows) only because owned_static's rows (0x20ee1, 0x1f) and
   (0x20f05, 0x1b) - the literal's two redzones - end and start exactly at its edges.  One byte more on either side,
   or rounding the range to 8 bytes or an aligned word, makes that clause FALSE. *)
Hypothesis HEND5G : forall a, VAL A_lit_end5 <= a < VAL A_lit_end5 + 5 ->
  ~ inG (G_SL B RG) a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
(* the stretch after the loop, 0x82638 onwards: lane GseTail (lib/A/W_gse_tail.v) *)
Hypothesis GSE_TAIL : gse_tail_at B MT MMAX RG (BASE + A_gse_tail).
Theorem pb_gse_loop : gse_loop_at B MT MMAX RG (BASE + A_gse_loop).
Proof.
apply gse_loop_at_x_AR0.
assert (HP0 : forall ly S Hp W mem md, ARi0 SEGS B ly S Hp W mem md -> Hp = []) by apply ARi0_hp0.
assert (IMGC : forall ly S Hp W mem md, ARi0 SEGS B ly S Hp W mem md ->
  fst (ly_img ly) <= 0x10000 /\ 0x5fb000 <= fst (ly_img ly) + snd (ly_img ly))
  by (intros ly S Hp W mem md H; destruct H as [HAR _]; exact (AR_imgc B ly S Hp W mem md HAR)).
assert (BLKN : forall ly S Hp W mem md p n, ARi0 SEGS B ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n)
  by (intros ly S Hp W mem md p n H Hin; destruct H as [HAR _]; exact (AR_blkn B ly S Hp W mem md p n HAR Hin)).
assert (PSTR : forall a, in_rom SEGS a -> ~ Exists (in_zr a) (@nil (Z * Z))) by (intros a _ H; inversion H).
assert (HEND5P : forall a, VAL A_lit_end5 <= a < VAL A_lit_end5 + 5 -> ~ Exists (in_zr a) (@nil (Z * Z)))
  by (intros a _ H; inversion H).
pose proof (ge_spec_x_of_AR0 B MT MMAX RG _ GE) as GE_X.
pose (CTXL := [[BASE + AF_fr_gestures_end + 0xbc]; [BASE + AF_fr_gestures_end + 0xfc]]).
pose proof (afree_cf_rule_c_x_of_AR0 SEGS B MT CTXL (afree_cf_rule_c_weak SEGS B MT CTXL AFREE)) as AFREE_X.
pose proof (afree_null_cf_rule_c_x_of_AR0 SEGS B MT CTXL (afree_null_cf_rule_c_weak SEGS B MT CTXL AFREEN)) as AFREEN_X.
assert (HCTX_gse_loop : In [BASE + AF_fr_gestures_end + 0xbc] CTXL) by (unfold CTXL; cbn [In]; left; reflexivity).
pose proof (gse_tail_at_x_of_AR0 B MT MMAX RG _ GSE_TAIL) as GSE_TAIL_X.
eapply (pb_gse_loop_x B [] (ARi0 SEGS B) MT RP_AR MMAX RG) with (CTX_AFREE := CTXL); eassumption.
Qed.
End cAR.
End b.
End a.

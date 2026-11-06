(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the ASan walk of fuzz_reply's gesture_model, in the form of the cgif walks of
   proofs/cgif/cgif_file_fuzzer/lib/A/AC8h.v (call sites), lib/A/AC8b.v (a loop from its head) and lib/A/ACbk.v
   (entry and return). *)
(* gesture_model(s, line, len) at 0x85b9c is the harness's reference reading of one relayed line as PHD_EVENTS
   declares param_gesture (fuzz_reply.c:377-401).  It returns at once unless len >= 14, the first 13 bytes are
   "param_gesture" (bcmp) and byte 13 is a space; it then scans back from the end for the last space (a loop with one
   ASan check per byte), and when the word after it is "begin" or "end" (bcmp) it looks the key up in s->held with
   list_find and ends in a tail call to list_push (a new begin) or list_drop (an end of a held key).
   Functional content: lib/Prog/gesture_model_c.v:26-75, `texts H' = upd (texts H) (bzs ln)` (RelayModel.upd).
   Theorem: pb_gesture_model : gm_spec B MT MMAX G (BASE + AF_fr_gesture_model) (W_contract.v Section w4, verbatim).
   Section hypotheses:
     LAWS  : AR_laws SEGS B                              (the allocator interface's laws)
     TL    : PALib B                                     (the GOT slot and the shadow cell of the image)
     HG    : gx_ok SEGS B G                              (the caller's globals are image bytes, not allocator statics)
     MTL   : ameter_laws MT                              (the allocator meter is monotone; Reusable/YC5d.v)
     ABCMP : abcmp_realizes SEGS B (SIGMA WS_bcmp)       (the bcmp interceptor; runtime lane)
     LFIND : lfind_spec B G (BASE + AF_fr_list_find)     (lane W1, W_contract.v Section w1, verbatim)
     LPUSH : lp_spec B MT G MMAX (BASE + AF_fr_list_push) (lane W2, W_contract.v Section w2, verbatim)
     LDROP : ldrop_spec B MT G (BASE + AF_fr_list_drop)  (lane W1, W_contract.v Section w1, verbatim)
     HLITG : azs B (VAL A_lit_gesture) 13                (the literals' shadow is zero: runtime lane)
     HLITB : azs B (VAL A_lit_begin) 5
     HLITE : azs B (VAL A_lit_end) 3
     HLITV : the three literals' shadow hull is visible  (runtime lane; azs alone does not give the hull)
   ARx conversion (route (b), step 3; CONVERSION.md (sha256 1015972e02a9; internal record)): Section c proves pb_gesture_model_x : gm_spec_x
   over a generic allocator relation ARx (LAWS / HP0, the callees at their _x specs, GMSCAN_X = W_gm_scan.pb_gm_scan_x's
   statement); Section r re-derives pb_gesture_model, statement unchanged, at ARx := W_journal_x.ARi0. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YI08.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require RelayModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep CheckRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_syms W_listing W_pl W_kit W_contract W_rep W_journal W_sites W_frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_shadow_pin.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG YCe5x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_journal_x W_sites_x W_contract_x W_kit_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_contract_xR_g6.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* The model's side: lib/Prog/RelayModel.v:239-277 (gesture, upd), read the way gesture_model's code reads a line. *)
Module GM.
Import RelayModel.
Lemma lsf_none : forall l i, (forall k, (k < length l)%nat -> nth k l 0 <> SPACE) -> last_space_from i l = None.
Proof.
induction l as [|b l IH]; intros i H; [reflexivity|].
cbn [last_space_from]. rewrite IH by (intros k Hk; apply (H (Datatypes.S k)); cbn; lia).
destruct (Z.eqb_spec b SPACE) as [E|E]; [exfalso; apply (H 0%nat); [cbn; lia | exact E] | reflexivity].
Qed.
Lemma lsf : forall l i j, (j < length l)%nat -> nth j l 0 = SPACE ->
(forall k, (j < k < length l)%nat -> nth k l 0 <> SPACE) -> last_space_from i l = Some (i + j)%nat.
Proof.
induction l as [|b l IH]; intros i j Hj HS HN; [cbn in Hj; lia|].
cbn [last_space_from]. destruct j as [|j].
- rewrite lsf_none by (intros k Hk; apply (HN (Datatypes.S k)); cbn; lia).
cbn in HS. rewrite HS. cbn. f_equal. lia.
- rewrite (IH (Datatypes.S i) j) by (cbn in *; first [lia | exact HS | intros k Hk; apply (HN (Datatypes.S k)); lia]).
f_equal. lia.
Qed.
Lemma eqb_true : forall a b, list_eqb a b = true <-> a = b.
Proof. intros a b. unfold list_eqb. destruct (list_eq_dec Z.eq_dec a b); split; intros H; congruence. Qed.
Lemma eqb_len : forall a b, length a <> length b -> list_eqb a b = false.
Proof. intros a b H. destruct (list_eqb a b) eqn:E; [|reflexivity]. apply eqb_true in E. subst. contradiction. Qed.
Lemma short : forall l, (length l <= 13)%nat -> gesture l = None.
Proof. intros l H. unfold gesture. rewrite (proj2 (Nat.ltb_ge 13 (length l)) H), !andb_false_r. reflexivity. Qed.
Lemma nok : forall l, firstn 13 l <> K_GESTURE -> gesture l = None.
Proof.
intros l H. unfold gesture. destruct (list_eqb (firstn 13 l) K_GESTURE) eqn:E; [|reflexivity].
exfalso. apply H. apply eqb_true. exact E.
Qed.
Lemma nosp : forall l, nth 13 l 0 <> SPACE -> gesture l = None.
Proof. intros l H. unfold gesture. rewrite (proj2 (Z.eqb_neq _ _) H), andb_false_r. cbn [andb]. reflexivity. Qed.
Lemma at_j : forall l j, (13 < length l)%nat -> firstn 13 l = K_GESTURE -> nth 13 l 0 = SPACE ->
last_space_from 0 l = Some j ->
gesture l = if Nat.ltb 13 j then
if list_eqb (skipn (Datatypes.S j) l) W_BEGIN then Some (GBegin, firstn j l)
else if list_eqb (skipn (Datatypes.S j) l) W_END then Some (GEnd, firstn j l) else None
else None.
Proof.
intros l j H1 H2 H3 H4. unfold gesture.
rewrite (proj2 (eqb_true _ _) H2), (proj2 (Z.eqb_eq _ _) H3), (proj2 (Nat.ltb_lt _ _) H1), H4.
reflexivity.
Qed.
Lemma upd_none : forall G l, gesture l = None -> upd G l = G.
Proof. intros G l H. unfold upd. rewrite H. reflexivity. Qed.
Lemma upd_begin_in : forall G l x, gesture l = Some (GBegin, x) -> In x G -> upd G l = G.
Proof.
intros G l x H I. unfold upd. rewrite H.
replace (existsb (list_eqb x) G) with true; [reflexivity|].
symmetry. apply existsb_exists. exists x. split; [exact I | apply eqb_true; reflexivity].
Qed.
Lemma filter_out : forall x G, ~ In x G -> List.filter (fun y => negb (list_eqb x y)) G = G.
Proof.
intros x G. induction G as [|y G IH]; intros N; [reflexivity|].
cbn [List.filter]. destruct (list_eqb x y) eqn:E.
- exfalso. apply eqb_true in E. subst. apply N. left. reflexivity.
- cbn [negb]. f_equal. apply IH. intros I. apply N. right. exact I.
Qed.
Lemma upd_end_out : forall G l x, gesture l = Some (GEnd, x) -> ~ In x G -> upd G l = G.
Proof. intros G l x H N. unfold upd. rewrite H. exact (filter_out x G N). Qed.
Lemma upd_begin_new : forall G l x, gesture l = Some (GBegin, x) -> ~ In x G -> upd G l = G ++ [x].
Proof.
intros G l x H N. unfold upd. rewrite H.
replace (existsb (list_eqb x) G) with false; [reflexivity|].
symmetry. apply not_true_iff_false. intros E. apply existsb_exists in E as (y & Iy & Ey).
apply eqb_true in Ey. subst. exact (N Iy).
Qed.
Lemma filter_nth : forall (G : list (list Z)) i, List.NoDup G -> (i < length G)%nat ->
List.filter (fun y => negb (list_eqb (nth i G []) y)) G = firstn i G ++ skipn (Datatypes.S i) G.
Proof.
induction G as [|y G IH]; intros i ND Hi; [cbn in Hi; lia|].
inversion ND as [|y' G' Ny NDG]; subst.
destruct i as [|i].
- cbn [nth List.filter firstn skipn app]. rewrite (proj2 (eqb_true y y) eq_refl). cbn [negb].
apply filter_out. exact Ny.
- cbn [nth List.filter firstn skipn app].
assert (Ny' : nth i G [] <> y).
{ intros E. apply Ny. rewrite <- E. apply nth_In. cbn in Hi. lia. }
destruct (list_eqb (nth i G []) y) eqn:E; [apply eqb_true in E; exfalso; exact (Ny' E)|].
cbn [negb]. f_equal. apply IH; [exact NDG | cbn in Hi; lia].
Qed.
Lemma upd_end_at : forall G l i, gesture l = Some (GEnd, nth i G []) -> List.NoDup G -> (i < length G)%nat ->
upd G l = firstn i G ++ skipn (Datatypes.S i) G.
Proof. intros G l i H ND Hi. unfold upd. rewrite H. exact (filter_nth G i ND Hi). Qed.
End GM.

(* ---- two list-length facts and one presence fact the walk needs. ---- *)
(* a record of the vector is 16 bytes (two little-endian words), so the vector holds AREC * cap bytes *)
Lemma text_rec_len : forall r, length (HarnessRep.text_rec r) = 16%nat.
Proof. intros r. unfold HarnessRep.text_rec. rewrite length_app. cbn. reflexivity. Qed.
Lemma concat_text_len : forall rs, length (concat (map HarnessRep.text_rec rs)) = (16 * length rs)%nat.
Proof.
induction rs as [|r rs IH]; [reflexivity|].
cbn [map concat length]. rewrite length_app, IH, text_rec_len. lia.
Qed.
Lemma vec_len : forall l,
Z.of_nat (length (HarnessRep.hl_junk l)) = AREC * (HarnessRep.hl_cap l - HarnessRep.hl_n l) ->
Z.of_nat (length (bzs (concat (map HarnessRep.text_rec (HarnessRep.hl_recs l)) ++ HarnessRep.hl_junk l)))
= AREC * HarnessRep.hl_cap l.
Proof.
intros l HJ. unfold bzs. rewrite length_map, length_app, concat_text_len.
unfold HarnessRep.hl_n in HJ. unfold AREC in *. lia.
Qed.
(* a run keeps every byte it does not hide: mem_grows of the restricted memories carries apresent *)
Lemma apres_of_grows : forall (Hb : word -> bool) (m m' : word -> option byte) a,
mem_grows (mrestrict Hb m) (mrestrict Hb m') -> apresent Hb m a -> apresent Hb m' a.
Proof.
intros Hb m m' a HGr [Hh [b Hb']]. split; [exact Hh|].
assert (Hm : mrestrict Hb m (Z_to_bv 64 a) <> None) by (unfold mrestrict; rewrite Hh, Hb'; discriminate).
pose proof (HGr (Z_to_bv 64 a) Hm) as Hm'. unfold mrestrict in Hm'. rewrite Hh in Hm'.
destruct (m' (Z_to_bv 64 a)) as [b'|] eqn:Em; [exists b'; reflexivity|].
cbn in Hm'. exfalso. apply Hm'. reflexivity.
Qed.
(* the bcmp result against a literal, read as a prefix equation *)
Lemma nth_of_firstn : forall n (l : list Z) i, (i < n)%nat -> nth i (firstn n l) 0 = nth i l 0.
Proof.
induction n as [|n IH]; intros l i Hi; [lia|].
destruct l as [|a l]; cbn [firstn]; [destruct i; reflexivity|].
destruct i as [|i]; cbn [nth]; [reflexivity | apply IH; lia].
Qed.
Lemma firstn_eq_of_nth : forall n (l m : list Z), length m = n -> (n <= length l)%nat ->
(forall i, (i < n)%nat -> nth i l 0 = nth i m 0) -> firstn n l = m.
Proof.
induction n as [|n IH]; intros l m Hm Hn Hi.
- destruct m; [reflexivity | cbn in Hm; lia].
- destruct l as [|a l]; [cbn in Hn; lia|]. destruct m as [|b m]; [cbn in Hm; lia|].
cbn [firstn]. f_equal; [exact (Hi 0%nat ltac:(lia))|].
apply IH; [cbn in Hm; lia | cbn in Hn; lia | intros i Hil; exact (Hi (Datatypes.S i) ltac:(lia))].
Qed.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PI).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).
Definition A_gesture_model : Z := AF_fr_gesture_model.
Definition A_gesture_modelP : Z := BASE + A_gesture_model.
(* the scan loop's head (0x85c18), the byte after the last space (0x85c58), the shared epilogue (0x85ce8) *)
Definition A_gm_loop : Z := A_gesture_model + 0x7c.
Definition A_gm_found : Z := A_gesture_model + 0xbc.
Definition A_gm_ret : Z := A_gesture_model + 0x14c.
(* ---- THE GENERIC WALK (route (b), step 3): gesture_model's entry over any allocator relation ARx with its laws.  The
   Section hypotheses beyond the AR walk's: PST / ARx / hl / LAWS (the generic relation) and HP0 (no hidden head in any
   ARx state, a Theorem Labs lane's ruling); the callees are their _x specs at the same PST / ARx, and GMSCAN_X is
   W_gm_scan.pb_gm_scan_x's statement verbatim. ---- *)
Section c.
Variable B : asyms.
Variable MT : ameter_ops.
(* the room round (W_contract_x.v Section w4): the room parameter, after MT as the kit's spec Sections take it *)
Variable RP : roomp.
Variable MMAX : Z.
Variable G : list (Z * Z).
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
Hypothesis HP0 : forall ly S Hp W mem md, ARx ly S Hp W mem md -> Hp = [].
Hypothesis TL : PALib B.
Hypothesis HG : gx_ok SEGS B G.
Hypothesis MTL : ameter_laws MT.
Hypothesis ABCMP : abcmp_realizes_x SEGS B ARx (SIGMA WS_bcmp).
Hypothesis LFIND : lfind_spec_x B PST ARx G (BASE + AF_fr_list_find).
Hypothesis LPUSH : lp_spec_x B PST ARx MT RP G MMAX (BASE + AF_fr_list_push).
Hypothesis LDROP : ldrop_spec_x B PST ARx MT RP G (BASE + AF_fr_list_drop).
(* the three literals are addressable with a visible shadow hull in every ARx state (W_shadow_pin.v ashp over ARx,
   W_contract_x.ashp_x; at the AR instance W_shadow_pin_fr.v ashp_gesture_13_fr / ashp_begin_5_fr / ashp_end_3_fr). *)
Hypothesis HLITG : ashp_x ARx (VAL A_lit_gesture) 13.
Hypothesis HLITB : ashp_x ARx (VAL A_lit_begin) 5.
Hypothesis HLITE : ashp_x ARx (VAL A_lit_end) 3.
(* an arm that makes no allocator call has room 0 (gm_cost MT_rk H ln = 0 there); gm_rm_down drops it to kr (roomp's
   rp_RMM, RMM_of) *)
Lemma gm_rm_down : forall S k kr, rp_RM RP S (k + kr) -> rp_RM RP S kr.
Proof. intros S k kr HR. exact (RMM_of RP S kr (k + kr) ltac:(lia) HR). Qed.
(* a line that names no gesture is charged nothing (W_contract.v gm_cost, the trace's charge) *)
Lemma gmm_cost_none : forall M (H : hlist) ln, RelayModel.gesture (bzs ln) = None -> gm_cost M H ln = 0.
Proof. intros M H ln Hg. unfold gm_cost. rewrite Hg. reflexivity. Qed.

Let RUN := paj_run_x_x B PST ARx LAWS G HG 0 [].
Let RUNTO := paj_run_to_x_x B PST ARx LAWS G HG 0 [].
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_fr) (PI := PI).
Local Notation AJG := (ajournal_gx_x SEGS B PST ARx G 0 []).
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.
Definition Bx : sv := SOff 32 0.
Definition gm_regions : smem := [ stack_region GM_FRAME; got_regionP; bcell_regionP 32 ].
Definition gm_facts : facts :=
mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (11%nat, mkAF 4096 140737479966720 0); (12%nat, mkAF 0 6000 0);
(32%nat, mkAF SB SB 0); (33%nat, mkAF 0 255 0) ] [] [].
Definition ss_gm : sstate := mkSS A_gesture_model sr_atoms gm_regions None gm_facts.
Definition gm_SH : list shent := [].
Definition Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition gm_extra (b13 : Z) : list word := map (Z_to_bv 64) [SB; b13].
(* The scan loop from its head (0x85c18), with its exit into the word-length dispatch: A/W_gm_scan.v pb_gm_scan_x,
   verbatim. *)
Hypothesis GMSCAN_X : forall (fuel : nat) W ly S Hp regs mem md ch HA LINE (ln : list byte) H q k (j : Z) regsc memc mdc,
afn_pre_x SEGS B ARx GM_STK ly S Hp W regs mem md ch ->
getr regs 10 = w64 HA -> getr regs 11 = w64 LINE -> getr regs 12 = w64 (Z.of_nat (length ln)) ->
alist_at B ly S W mem (HA + 80) H true -> NoDup (texts H) ->
(forall a, HA + 80 <= a < HA + 96 -> inG G a) -> azs B (HA + 80) 16 ->
(HA + 80) mod 8 = 0 ->
garr8 SEGS (arm W mem) LINE (bzs ln) -> ~ In (Z_to_bv 8 0) ln -> Z.of_nat (length ln) <= APARTIAL ->
In (q, k) (ablocks B ly S) -> ~ In (q, k) (list_blks H) -> q <= LINE ->
LINE + Z.of_nat (length ln) <= q + req_size k ->
garr8 SEGS (arm W mem) (VAL A_lit_gesture) RelayModel.K_GESTURE ->
garr8 SEGS (arm W mem) (VAL A_lit_begin) RelayModel.W_BEGIN ->
garr8 SEGS (arm W mem) (VAL A_lit_end) RelayModel.W_END ->
rom_view SEGS W mem ->
(lp_grow H = true -> lp_vbytes H < MMAX) -> AREC * hl_cap H < 2 ^ 32 ->
blocks_bytes S + (if lp_grow H then lp_vbytes H else 0) + (Z.of_nat (length ln) + 1) <= LIVE_MAX ->
mo_ok MT S (gm_cost MT H ln) ->
forall kr : nat,
rp_RM RP S (Z.to_nat (gm_cost MT_rk H ln) + kr) ->
cnt_ok_pk RP (gm_pk H) (ablocks B ly S) ->
firstn 13 (bzs ln) = RelayModel.K_GESTURE ->
nth 13 (bzs ln) 0 = RelayModel.SPACE ->
spZ regsc = spZ regs - GM_FRAME ->
getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
getr regsc 8 = w64 LINE -> getr regsc 9 = w64 HA ->
getr regsc 18 = w64 (Z.of_nat (length ln)) -> getr regsc 19 = w64 SB ->
(forall r, acallee_saved r -> 20 <= r <= 27 -> getr regsc (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
val_mem SEGS (arm W memc) (spZ regs - 8) 8 (bv_unsigned (getr regs 1)) ->
val_mem SEGS (arm W memc) (spZ regs - 16) 8 (bv_unsigned (getr regs 8)) ->
val_mem SEGS (arm W memc) (spZ regs - 24) 8 (bv_unsigned (getr regs 9)) ->
val_mem SEGS (arm W memc) (spZ regs - 32) 8 (bv_unsigned (getr regs 18)) ->
val_mem SEGS (arm W memc) (spZ regs - 40) 8 (bv_unsigned (getr regs 19)) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - GM_STK <= a < spZ regs) ->
 aview SEGS (w_H W) memc a = aview SEGS (w_H W) mem a) ->
(forall a, apresent (w_H W) mem a -> apresent (w_H W) memc a) ->
ajournal_gx_x SEGS B PST ARx G 0 [] GM_STK (spZ regs) (blk_FP (list_blks H)) ly S Hp W mem md [] ly S Hp W memc mdc 0 ->
getr regsc 10 = w64 j -> getr regsc 11 = w64 32 ->
getr regsc 12 = w64 (LINE + Z.of_nat (length ln)) ->
getr regsc 13 = w64 (LINE + Z.of_nat (length ln) - 1) ->
14 <= Z.of_nat (length ln) -> 13 < Z.of_nat (length ln) + j -> j <= 0 ->
(forall t, Z.of_nat (length ln) + j <= t < Z.of_nat (length ln) ->
 nth (Z.to_nat t) (bzs ln) 0 <> RelayModel.SPACE) ->
Z.of_nat fuel = Z.of_nat (length ln) + j - 13 ->
SRr SEGS W (mkCfg (mkst regsc (Z_to_bv 64 (BASE + A_gm_loop)) memc (seg_rom SEGS)) mdc)
(gm_post_x B PST ARx MT RP G regs ly S Hp W mem md HA H ln kr).
(* the byte line[13], read after the bcmp agrees: a read-only chunk on the line's atom *)
Definition line_region : YP09.region :=
YP09.mkRegion (Some 11%nat) 0 14 0 0 [YP09.mkChunk 13 (CVal 1 (SOff 33 0))].
(* the walk's regions write only the stack frame: every other byte is outside their writable windows *)
Ltac gm_outw Usp :=
let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
intros (r & Hin & Hr); cbn [ss_mem add_cond ss_gm gm_regions In] in Hin;
repeat (destruct Hin as [<- | Hin];
[ cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val
stack_region got_regionP bcell_regionP line_region] in Hr;
rewrite ?Usp in Hr; unfold GM_STK, GM_FRAME, LP_STK, ASTACK in *; lia | ]);
destruct Hin.
Lemma gm_entry : forall W ly S Hp regs mem md ch LINE LEN b13,
afn_pre_x SEGS B ARx GM_STK ly S Hp W regs mem md ch ->
getr regs 11 = w64 LINE -> getr regs 12 = w64 LEN -> 4096 <= LINE <= 140737479966720 -> 0 <= LEN <= 6000 ->
0 <= b13 < 256 ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (gm_extra b13))) ss_gm
(restrict (w_H W) (mkst regs (Z_to_bv 64 A_gesture_modelP) mem (seg_rom SEGS)))
/\ sh_ok SEGS Bx gm_SH (Eimg (Ereg regs (gm_extra b13))) (mrestrict (w_H W) mem).
Proof.
intros W ly S hp regs mem md ch LINE LEN b13 HPRE H11 H12 RL RN Rb.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : GM_STK = 16528) by reflexivity.
destruct (alx_const _ _ _ LAWS ly S hp W mem md HAR) as (Kcell & _ & Kgot & _).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs (gm_extra b13))). pose proof pa_B_ok as HBASE.
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E11 : ew E 11 = Z_to_bv 64 LINE) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E12 : ew E 12 = Z_to_bv 64 LEN) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact H12).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 b13) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E273 : ew E (A_OBJ 32) = Z_to_bv 64 (VAL (A_OBJ 32))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
pose proof (pa_obj_img 32 ltac:(lia)) as HcellR. pose proof (pal_got_cell B TL) as HgcD. pose proof (pa_obj_img 0 ltac:(lia)) as HgotR.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall m w, ew E m = Z_to_bv 64 w -> 0 <= w < 2 ^ 64 -> base_val E (Some m) = w).
{ intros m w Hm Hw. cbn [base_val]. rewrite Hm. apply unsigned_lit_small. exact Hw. }
split.
- unfold ss_gm, A_gesture_modelP. apply pa_entry_st_ok_full.
+ apply regs_ok_Eimg_Ereg.
+ vm_compute. reflexivity.
+ unfold gm_regions, stack_region, got_regionP, bcell_regionP;
repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
* cbn [base_val]. rewrite Usp. split; [unfold GM_FRAME; lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply Hpres. unfold GM_FRAME in *. lia.
* rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 32) 0) (VAL (A_OBJ 32)));
[cbn [sv_denot]; rewrite E273, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | pose proof (pa_val_range (A_OBJ 32)); zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
* rewrite (VB (A_OBJ 32) (VAL (A_OBJ 32)) E273) by (pose proof (pa_val_range (A_OBJ 32)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 32)) 0 8 Bx SB);
[cbn [sv_denot Bx]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
+ apply pairwise_disjoint_of_extents. unfold gm_regions, stack_region, got_regionP, bcell_regionP, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia).
rewrite (VB (A_OBJ 32) (VAL (A_OBJ 32)) E273) by (pose proof (pa_val_range (A_OBJ 32)); lia). cbn [base_val]. rewrite Usp.
unfold GM_FRAME.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
revert Hslo Hshi H47 Hceil C1 C3 WS Hstk0 HcellR HgcD HgotR. clear.
unfold zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, GM_FRAME, ESTACK. intros. repeat split; lia.
+ split; [|split; [exact I | exact I]].
cbn [gm_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Usp, E11, E12, E32, E33, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
revert Hslo Hshi H47 Hceil Hal16 C1 C3 WS Hstk0 RL RN Rb. clear.
unfold SB, zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, GM_FRAME, ESTACK. intros.
repeat match goal with |- _ /\ _ => split end; lia.
- unfold sh_ok, gm_SH. constructor.
Qed.

(* errno's four bytes are image bytes, so they lie below gesture_model's frame (the image is below kLowMemEnd, the
   frame above alloc_ceiling): every view kept outside the frame keeps errno's *)
Lemma gmm_errno_out : forall W ly S Hp regs mem md ch, afn_pre_x SEGS B ARx GM_STK ly S Hp W regs mem md ch ->
forall j, 0 <= j < 4 -> 0 <= as_errno B + j < 2 ^ 64 /\ ~ (spZ regs - GM_STK <= as_errno B + j < spZ regs).
Proof.
intros W ly S hp regs mem md ch HPRE j Hj.
pose proof HPRE as (_ & _ & _ & _ & _ & Hstk & _). pose proof Hstk as (_ & _ & Hceil & Hslo & _).
pose proof (pal_env B TL) as (_ & HeImg & _).
pose proof (pa_segs_low _ (HeImg (as_errno B + j) ltac:(lia))) as Hl.
pose proof ASAN_CEIL_range as (Hc & _). unfold ASAN_CEIL in Hc. unfold kLowMemEnd in *. split; [lia | lia].
Qed.
Theorem pb_gesture_model_x : gm_spec_x B PST ARx MT RP MMAX G A_gesture_modelP.
Proof.
intros W ly S hp regs mem md ch HA LINE ln H q k HPRE H10 H11 H12 HL ND HinG HZS HAL8 GL NZ LN Hq Hqb Hq1 Hq2 LG LB LE HROM HGROW HCAP32 HROOM MOK kr HRM HCNT.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : GM_STK = 16528) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
remember (Z.of_nat (length ln)) as LEN eqn:HLEN.
set (b13 := nth 13 (bzs ln) 0).
destruct (alx_blocks _ _ _ LAWS ly S hp W mem md q k HAR Hq) as (Hq16 & Hq4096 & Hqceil & Hqh_ia & Hqpres & _).
assert (Hrq2 : k <= req_size k)
by (unfold req_size; destruct (k =? 0) eqn:Ek; [apply Z.eqb_eq in Ek | apply Z.eqb_neq in Ek]; lia).
assert (RL : 4096 <= LINE <= 140737479966720) by (unfold ASAN_CEIL in *; lia).
assert (RN : 0 <= LEN <= 6000) by (unfold APARTIAL in LN; lia).
assert (Rb : 0 <= b13 < 256).
{ unfold b13. destruct (nth_in_or_default 13 (bzs ln) 0) as [Hin | ->]; [|lia].
unfold bzs in Hin |- *. apply in_map_iff in Hin as (b & <- & _). unfold bz.
pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R. lia. }
destruct (gm_entry W ly S hp regs mem md ch LINE LEN b13 HPRE H11 ltac:(rewrite H12, HLEN; reflexivity) RL RN Rb) as [HS SHOK].
assert (HJ : AJG GM_STK (spZ regs) (blk_FP (list_blks H)) ly S hp W mem md [] ly S hp W mem md 0).
{ apply (ajournal_gx_init_x SEGS B PST ARx G 0 [] GM_STK _ ly S hp W regs mem md ch HPRE); [lia | reflexivity | lia | intros a Ha; lia]. }
remember (Eimg (Ereg regs (gm_extra b13))) as E eqn:HE. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (E1 : ew E 1 = getr regs 1) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E8 : ew E 8 = getr regs 8) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 8 8%bv eq_refl)).
assert (E9 : ew E 9 = getr regs 9) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 9 9%bv eq_refl)).
assert (E18 : ew E 18 = getr regs 18) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 18 18%bv eq_refl)).
assert (E19 : ew E 19 = getr regs 19) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 19 19%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 HA) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 LINE) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E12 : ew E 12 = Z_to_bv 64 LEN) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); rewrite H12, HLEN; reflexivity).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 b13) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E262 : ew E 262%nat = Z_to_bv 64 (VAL (A_OBJ 21))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E264 : ew E 264%nat = Z_to_bv 64 (VAL (A_OBJ 23))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E265 : ew E 265%nat = Z_to_bv 64 (VAL (A_OBJ 24))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HAE : env_agree 32 (Ereg regs (gm_extra b13)) E) by (rewrite HE; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
clear HE.
(* ---- bounds every arm needs: the list's bytes and the image are below this frame. ---- *)
assert (HLO : alloc_ceiling <= spZ regs - GM_STK) by (unfold GM_STK, GM_FRAME, LP_STK, ASTACK in *; lia).
assert (BLK : forall p n a, In (p, n) (ablocks B ly S) -> p <= a < p + req_size n ->
0 <= a /\ a < spZ regs - GM_STK).
{ intros p n a Hin Hr. destruct (alx_blocks _ _ _ LAWS ly S hp W mem md p n HAR Hin) as (_ & Hp4 & Hpc & _).
unfold GM_STK, GM_FRAME, LP_STK, ASTACK in *. split; [lia | lia]. }
assert (IMG : forall a, in_img SEGS a -> 0 <= a /\ a < spZ regs - GM_STK).
{ intros a Hin. pose proof (pa_segs_low a Hin) as Hl.
unfold kLowMemEnd, GM_STK, GM_FRAME, LP_STK, ASTACK in *. split; [lia | lia]. }
assert (FPLO : forall r, In r (alist_fp (HA + 80) H) -> forall a, fst r <= a < snd r ->
0 <= a /\ a < spZ regs - GM_STK).
{ intros r Hr a Ha. pose proof HL as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9).
unfold alist_fp in Hr. destruct Hr as [<- | Hr].
- cbn [fst snd] in Ha. apply IMG. apply (proj1 (HG a (HinG a ltac:(lia)))).
- apply in_app_or in Hr as [Hr | Hr].
+ destruct (hl_cap H =? 0) eqn:Ec; cbn [In] in Hr; [destruct Hr|].
destruct Hr as [<- | []]. apply Z.eqb_neq in Ec.
destruct V6 as [(Hc0 & _) | (Hc0 & Hinv & Hj & _)]; [lia|].
pose proof (vec_len H Hj) as Hlen. unfold gfp in Ha. cbn [fst snd] in Ha. rewrite Hlen in Ha.
pose proof (req_size_pos (AREC * hl_cap H) ltac:(unfold AREC; lia)) as [_ Hrs].
apply (BLK (hl_v H) (AREC * hl_cap H) a Hinv). lia.
+ apply in_map_iff in Hr as (rec & <- & Hrec). unfold gfp in Ha. cbn [fst snd] in Ha.
rewrite Forall_forall in V9. destruct (V9 rec Hrec) as (Rin & _).
pose proof (req_size_pos (Z.of_nat (length (snd rec)) + 1) ltac:(lia)) as [_ Hrs].
apply (BLK (fst rec) (Z.of_nat (length (snd rec)) + 1) a Rin).
unfold bzs in Ha. rewrite length_map, length_app in Ha. cbn [length] in Ha. lia. }
assert (ABL : forall b, In b (alist_blks H) -> In b (ablocks B ly S)).
{ intros b Hb. pose proof HL as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9).
unfold alist_blks in Hb. apply in_app_or in Hb as [Hb | Hb].
- destruct (hl_cap H =? 0) eqn:Ec; cbn [In] in Hb; [destruct Hb|].
destruct Hb as [<- | []]. apply Z.eqb_neq in Ec.
destruct V6 as [(Hc0 & _) | (_ & Hinv & _)]; [lia | exact Hinv].
- apply in_map_iff in Hb as (rec & <- & Hrec). rewrite Forall_forall in V9.
exact (proj1 (V9 rec Hrec)). }
unfold cfg_at. change (w64 A_gesture_modelP) with (Z_to_bv 64 A_gesture_modelP).
unfold A_gesture_modelP, A_gesture_model.
paj_run_tok_x RUN HS HJ SHOK Bspan. { apply awr_ok_x_of0. awr_ok_tac. exact Usp. }
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* len < 14: GM.short, the line is not a gesture *)
rewrite branch_ltu_U, (U_atom E 12 LEN E12) in Hc by lia. rewrite U_lit in Hc by lia.
assert (Hlt : LEN < 14) by (destruct (Z.ltb_spec LEN 14); [lia | discriminate]).
assert (GNONE : RelayModel.gesture (bzs ln) = None)
by (apply GM.short; unfold bzs; rewrite length_map; lia).
paj_run_tok_x RUN HS HJ SHOK Bspan. { apply awr_ok_x_of0. awr_ok_tac. exact Usp. }
assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - GM_STK <= a < spZ regs) ->
aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) mem a).
{ intros a Ha Hno.
rewrite (aview_kept_out E _ (w_H W) (ms_mem ms) (ms_mem ms0) HFr0 a Ha) by gm_outw Usp.
apply (aview_kept_out E _ (w_H W) mem (ms_mem ms) HFr a Ha). gm_outw Usp. }
assert (PRES : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms0) a).
{ intros a Hp.
lazymatch goal with
| K1 : mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) (ms_mem ms)),
  K2 : mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms0)) |- _ =>
  exact (apres_of_grows _ _ _ a K2 (apres_of_grows _ _ _ a K1 Hp)) end. }
prreg HS (1%bv : bv 5) R1.
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. unfold gm_post_x.
lazymatch goal with |- exists _ _ _ _ _ _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ =>
exists ly, S, hp, r, m, d, 0, H end.
split; [cbn [ms_regs]; rewrite R1, E1, Hra; reflexivity|].
split; [cbn [ms_mem]; apply (ajournal_gx_materialize_x SEGS B PST ARx LAWS Hsegs G 0 []); exact HJ|].
split; [eapply (aregs_preserved_of_st_ok SEGS _ E _ _ regs (gm_extra b13) HS); [exact HAE | vm_compute; reflexivity]|].
split; [intros a _ _ _ Hp; apply PRES; exact Hp|].
split; [intros ie Hie; destruct (gmm_errno_out W ly S hp regs mem md ch HPRE ie Hie) as [Hr Hn]; cbn [ms_mem]; exact (KEEP _ Hr Hn)|].
split.
{ cbn [ms_mem]. apply (alist_at_kept B ly S W mem ly S W (ms_mem ms0) (HA + 80) H true HL).
- intros r Hr a Ha. destruct (FPLO r Hr a Ha) as [Ha0 Hahi]. split.
  + apply KEEP; unfold GM_STK, GM_FRAME, LP_STK, ASTACK in *; lia.
  + intros Hw. apply (writable_kept (w_H W) mem (ms_mem ms0) a); [intros Hp; apply PRES; exact Hp | exact Hw].
- exact ABL. }
split; [exact ND|].
split; [symmetry; apply GM.upd_none; exact GNONE|].
split; [destruct (Z.ltb_spec (hl_n H) (hl_n H)); [lia | reflexivity]|].
split; [intros rest Hperm; exact Hperm|].
split; [reflexivity|].
split; [rewrite (gmm_cost_none MT H ln GNONE); apply (mo_le_refl MT MTL)|].
exact (gm_rm_down S _ kr HRM).
- (* 14 <= len: the line may be a gesture; compare the first 13 bytes with "param_gesture" *)
rewrite branch_ltu_U, (U_atom E 12 LEN E12) in Hc by lia. rewrite U_lit in Hc by lia.
assert (Hge : 14 <= LEN) by (destruct (Z.ltb_spec LEN 14); [discriminate | lia]).
paj_run_tok_x RUN HS HJ SHOK Bspan. { apply awr_ok_x_of0. awr_ok_tac. exact Usp. }
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3.
prreg HS (4%bv : bv 5) Q4. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
prreg HS (12%bv : bv 5) Q12.
assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - GM_STK <= a < spZ regs) ->
aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) mem a).
{ intros a Ha Hno.
rewrite (aview_kept_out E _ (w_H W) (ms_mem ms) (ms_mem ms0) HFr0 a Ha) by gm_outw Usp.
apply (aview_kept_out E _ (w_H W) mem (ms_mem ms) HFr a Ha). gm_outw Usp. }
assert (PRES1 : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms0) a).
{ intros a Hp. lazymatch goal with
| K1 : mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) (ms_mem ms)),
  K2 : mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms0)) |- _ =>
  exact (apres_of_grows _ _ _ a K2 (apres_of_grows _ _ _ a K1 Hp)) end. }
assert (Usp2 : spZ (ms_regs ms0) = spZ regs - 48).
{ unfold spZ. rewrite Q2, Usp. rewrite unsigned_lit_small by (unfold spZ in *; lia). reflexivity. }
pose proof HJ as HARc. apply ajournal_gx_AR_x in HARc.
pose proof (pa_obj_img 21 ltac:(lia)) as HL21. pose proof (pa_val_range (A_OBJ 21)) as HV21.
assert (GA : forall j, (j < length ln)%nat ->
aview SEGS (w_H W) (ms_mem ms0) (LINE + Z.of_nat j) = Some (nth j (bzs ln) 0)).
{ intros j Hj.
assert (Hb : 0 <= LINE + Z.of_nat j /\ LINE + Z.of_nat j < spZ regs - GM_STK)
by (apply (BLK q k (LINE + Z.of_nat j) Hq); lia).
destruct Hb as [Hb0 Hb1]. rewrite (KEEP1 (LINE + Z.of_nat j) ltac:(lia) ltac:(lia)).
destruct (GL j ltac:(unfold bzs; rewrite length_map; exact Hj)) as [Hv Hr].
exact (aview_of_val_mem1 SEGS (w_H W) mem _ _ Hv Hr). }
assert (LITLO : forall (oi : nat) (n : Z), (oi < 33)%nat -> 0 <= n <= 16 ->
0 <= VAL (A_OBJ oi) + n /\ VAL (A_OBJ oi) + n < spZ regs - GM_STK).
{ intros oi n Hi Hn. pose proof (pa_obj_img oi Hi) as Hobj.
unfold GM_STK, GM_FRAME, LP_STK, ASTACK in *. split; lia. }
assert (LITA : forall j, (j < 13)%nat ->
aview SEGS (w_H W) (ms_mem ms0) (VAL (A_OBJ 21) + Z.of_nat j) = Some (nth j RelayModel.K_GESTURE 0)).
{ intros j Hj. destruct (LITLO 21%nat (Z.of_nat j) ltac:(lia) ltac:(lia)) as [Ha0 Hahi].
rewrite (KEEP1 (VAL (A_OBJ 21) + Z.of_nat j) ltac:(lia) ltac:(lia)).
destruct (LG j ltac:(vm_compute; lia)) as [Hv Hr].
change (VAL A_lit_gesture) with (VAL (A_OBJ 21)) in Hv.
exact (aview_of_val_mem1 SEGS (w_H W) mem _ _ Hv Hr). }
pose proof (pa_obj_img 21%nat ltac:(lia)) as HO21.
eapply SRr_bind.
{ eapply (aj_bcmp_gx_at_x B PST ARx LAWS (SIGMA WS_bcmp) ABCMP G 0 ([] : list (Z * Z)) W (ms_regs ms0) (ms_mem ms0)
GM_STK (spZ regs) (blk_FP (list_blks H)) ly S hp W mem md ([] : list (Z * Z)) ly S hp _ 0
LINE (VAL (A_OBJ 21)) 13 (-48) (Z_to_bv 64 (BASE + 14588)) HG eq_refl HJ).
- rewrite Q10, E11. reflexivity.
- rewrite Q11, E262. reflexivity.
- exact Q12.
- lia.
- lia.
- lia.
- lia.
- lia.
- rewrite Usp2. lia.
- reflexivity.
- lia.
- rewrite WS. unfold ESTACK. lia.
- rewrite Q3, E3. exact Hgp.
- rewrite Q4, E4. exact Htp.
- exact Q1.
- apply ret_ok_codeptr_v; [lia | reflexivity].
- intros a Ha. destruct (BLK q k a Hq ltac:(lia)) as [Ha0 Hahi]. split.
  + replace a with (LINE + Z.of_nat (Z.to_nat (a - LINE))) by lia. rewrite GA by lia. discriminate.
  + rewrite Usp2. unfold ESTACK, GM_STK, GM_FRAME, LP_STK, ASTACK in *. lia.
- intros a Ha. destruct (LITLO 21%nat (a - VAL (A_OBJ 21)) ltac:(lia) ltac:(lia)) as [Ha0 Hahi]. split.
  + replace a with (VAL (A_OBJ 21) + Z.of_nat (Z.to_nat (a - VAL (A_OBJ 21)))) by lia.
    rewrite LITA by lia. discriminate.
  + rewrite Usp2. unfold ESTACK, GM_STK, GM_FRAME, LP_STK, ASTACK in *. lia.
- intros a Ha. destruct (BLK q k a Hq ltac:(lia)) as [Ha0 Hahi].
  unfold ESTACK, GM_STK, GM_FRAME, LP_STK, ASTACK in *. lia.
- intros a Ha. destruct (LITLO 21%nat (a - VAL (A_OBJ 21)) ltac:(lia) ltac:(lia)) as [Ha0 Hahi].
  unfold ESTACK, GM_STK, GM_FRAME, LP_STK, ASTACK in *. lia.
- apply (amem_range_of_block_x SEGS B ARx LAWS ly S hp W (ms_mem ms0) _ q k LINE 13 HARc Hq); lia.
- apply amem_range_high; [lia | left; lia | unfold ASAN_CEIL in *; lia].
- apply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly S hp W (ms_mem ms0) _ q k LINE 13 HARc Hq); lia.
- intros _. apply (shadow_hull_vis_of_block_hp0_x SEGS B ARx LAWS HP0 ly S hp W (ms_mem ms0) _ q k LINE 13 HARc Hq); lia.
- exact (proj1 (HLITG ly S hp W (ms_mem ms0) _ HARc)).
- intros Hn0. exact (proj2 (HLITG ly S hp W (ms_mem ms0) _ HARc) Hn0). }
cbv beta. intros W2 c2 Hwle2 (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP2 & Hres & Hcmp & Hfr2 & Hpres2).
jafter_call_keep_pi HS 34%nat regs2 (mrestrict (w_H W) mem2) HP2 [0]%nat HS2.
match type of HS2 with ?ty -> _ => assert (HRK : ty); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| apply Forall_nil].
unfold stack_region, GM_FRAME.
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Usp.
- intros a Ha. apply (mbyte_of_aview SEGS). apply Hfr2; unfold ESTACK in *; lia.
- intros a Ha _. apply (apresent_writable SEGS).
pose proof HJ2 as HJI. apply ajournal_gx_inner_x in HJI. destruct HJI as (memS & HJi & _).
rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPR2 & _).
apply HPR2. unfold GM_STK, GM_FRAME, LP_STK, ASTACK in *. lia. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 34 (map (getr regs2) CLOB)) as Eb eqn:HEb in HS.
assert (HEIb : img_env VAL A_LIM Eb) by (rewrite HEb; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDb : forall m, (m < 34)%nat -> ew Eb m = ew E m) by (intros m Hm; rewrite HEb; apply YN3v.ew_havoc_old; exact Hm).
assert (HAEb : env_agree 32 (Ereg regs (gm_extra b13)) Eb)
by (rewrite HEb; apply env_agree_havoc_ge; [cbv; lia | exact HAE]).
clear HEb.
assert (SHOKb : sh_ok SEGS Bx gm_SH Eb (mrestrict (w_H W) mem2)) by (unfold sh_ok, gm_SH; constructor).
assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - GM_STK <= a < spZ regs) ->
aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) mem a).
{ intros a Ha Hno.
rewrite (Hfr2 a Ha ltac:(unfold ESTACK, GM_STK, GM_FRAME, LP_STK, ASTACK in *; lia)).
apply KEEP1; [exact Ha | exact Hno]. }
assert (PRES2 : forall a, apresent (w_H W) mem a -> apresent (w_H W) mem2 a)
by (intros a Hp; apply Hpres2; apply PRES1; exact Hp).
assert (Uspb : bv_unsigned (ew Eb 2) = spZ regs) by (rewrite OLDb by lia; rewrite E2; reflexivity).
assert (Hvr : 0 <= bv_unsigned v < 2 ^ 64)
by (pose proof (bv_unsigned_in_range 64 v) as Hr0; change (bv_modulus 64) with (2 ^ 64) in Hr0; lia).
(* the model side of the comparison *)
assert (CMPM : v = w64 0 <-> firstn 13 (bzs ln) = RelayModel.K_GESTURE).
{ rewrite Hcmp. split.
- intros Hall. apply (firstn_eq_of_nth 13); [vm_compute; reflexivity | unfold bzs; rewrite length_map; lia|].
  intros i Hi. specialize (Hall (Z.of_nat i) ltac:(lia)).
  rewrite GA in Hall by lia.
  rewrite LITA in Hall by lia. injection Hall as Hall. exact Hall.
- intros Hfk i Hi. replace i with (Z.of_nat (Z.to_nat i)) by lia.
  rewrite GA by lia. rewrite LITA by lia.
  f_equal. rewrite <- Hfk. symmetry. apply nth_of_firstn. lia. }
prreg HS (10%bv : bv 5) R10.
assert (F38 : ew Eb 38 = Z_to_bv 64 (bv_unsigned v))
by (rewrite Z_to_bv_bv_unsigned, <- R10; exact Hres).
psrr_branch_tok RUN BR HS SHOKb Bspan.
+ (* bcmp <> 0: the first 13 bytes are not "param_gesture" *)
rewrite branch_ne_U, (U_atom Eb 38 (bv_unsigned v) F38 Hvr), U_lit in Hc0 by lia.
assert (Hvn : bv_unsigned v <> 0)
by (destruct (Z.eqb_spec (bv_unsigned v) 0); [cbn in Hc0; discriminate | lia]).
assert (GNONE : RelayModel.gesture (bzs ln) = None).
{ apply GM.nok. intros Hfk. apply Hvn. rewrite ((proj2 CMPM) Hfk). reflexivity. }
paj_run_tok_x RUN HS HJ2 SHOKb Bspan. { apply awr_ok_x_of0. awr_ok_tac. exact Uspb. }
assert (KEEPA : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - GM_STK <= a < spZ regs) ->
aview SEGS (w_H W) (ms_mem ms1) a = aview SEGS (w_H W) mem a).
{ intros a Ha Hno.
rewrite (aview_kept_out Eb _ (w_H W) mem2 (ms_mem ms1) HFr1 a Ha) by gm_outw Uspb.
apply KEEP2; [exact Ha | exact Hno]. }
assert (PRESA : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms1) a).
{ intros a Hp. lazymatch goal with
| K3 : mem_grows (mrestrict (w_H W) mem2) (mrestrict (w_H W) (ms_mem ms1)) |- _ =>
  exact (apres_of_grows _ _ _ a K3 (PRES2 a Hp)) end. }
prreg HS (1%bv : bv 5) RA1.
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. unfold gm_post_x.
lazymatch goal with |- exists _ _ _ _ _ _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ =>
exists ly, S, hp, r, m, d, 0, H end.
split; [cbn [ms_regs]; rewrite RA1, OLDb by lia; rewrite E1, Hra; reflexivity|].
split; [cbn [ms_mem]; apply (ajournal_gx_materialize_x SEGS B PST ARx LAWS Hsegs G 0 []); exact HJ2|].
split; [eapply (aregs_preserved_of_st_ok SEGS _ Eb _ _ regs (gm_extra b13) HS); [exact HAEb | vm_compute; reflexivity]|].
split; [intros a _ _ _ Hp; apply PRESA; exact Hp|].
split; [intros ie Hie; destruct (gmm_errno_out W ly S hp regs mem md ch HPRE ie Hie) as [Hr Hn]; cbn [ms_mem]; exact (KEEPA _ Hr Hn)|].
split.
{ cbn [ms_mem]. apply (alist_at_kept B ly S W mem ly S W (ms_mem ms1) (HA + 80) H true HL).
- intros r Hr a Ha. destruct (FPLO r Hr a Ha) as [Ha0 Hahi]. split.
  + apply KEEPA; unfold GM_STK, GM_FRAME, LP_STK, ASTACK in *; lia.
  + intros Hw. apply (writable_kept (w_H W) mem (ms_mem ms1) a); [intros Hp; apply PRESA; exact Hp | exact Hw].
- exact ABL. }
split; [exact ND|].
split; [symmetry; apply GM.upd_none; exact GNONE|].
split; [destruct (Z.ltb_spec (hl_n H) (hl_n H)); [lia | reflexivity]|].
split; [intros rest Hperm; exact Hperm|].
split; [reflexivity|].
split; [rewrite (gmm_cost_none MT H ln GNONE); apply (mo_le_refl MT MTL)|].
exact (gm_rm_down S _ kr HRM).
+ (* bcmp = 0: the line starts with "param_gesture" *)
rewrite branch_ne_U, (U_atom Eb 38 (bv_unsigned v) F38 Hvr), U_lit in Hc0 by lia.
assert (HFK : firstn 13 (bzs ln) = RelayModel.K_GESTURE).
{ apply (proj1 CMPM). apply bv_eq.
  destruct (Z.eqb_spec (bv_unsigned v) 0); [rewrite e; reflexivity | cbn in Hc0; discriminate]. }
assert (E11b : ew Eb 11 = Z_to_bv 64 LINE) by (rewrite OLDb by lia; exact E11).
assert (E33b : ew Eb 33 = Z_to_bv 64 b13) by (rewrite OLDb by lia; exact E33).
assert (VM13 : val_mem SEGS (mrestrict (w_H W) mem2) (LINE + 13) 1 b13).
{ apply (val_mem_kept SEGS (w_H W) (w_H W) mem mem2 (LINE + 13) 1%nat b13).
- intros kk Hkk. cbn in Hkk. replace kk with 0 by lia. rewrite Z.add_0_r.
  apply KEEP2; [lia | destruct (BLK q k (LINE + 13) Hq ltac:(lia)) as [Hd0 Hd1];
  unfold GM_STK, GM_FRAME, LP_STK, ASTACK in *; lia].
- destruct (GL 13%nat ltac:(unfold bzs; rewrite length_map; lia)) as [Hv _].
  change (Z.of_nat 13) with 13 in Hv. exact Hv. }
pose proof (st_ok_pi_add_region Eb _ _ line_region HS) as HSr.
lazymatch type of HSr with ?a -> ?b -> ?c -> _ =>
assert (Hwf : a); [vm_compute; reflexivity|];
assert (Hrok : b); [|assert (Hdis : c); [|specialize (HSr Hwf Hrok Hdis)]] end.
{ unfold line_region, region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks ms_mem restrict mkst].
cbn [base_val]. rewrite E11b, unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS Eb _ LINE (13%Z) (1%N) (SOff 33 0) b13);
[cbn [sv_denot]; rewrite E33b, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | zside |].
exact VM13. }
{ apply all_disjoint_of_extents. unfold line_region, stack_region, extent_of_region.
cbn [ss_mem add_cond map YP09.r_base YP09.r_lo YP09.r_hi].
cbn [base_val]. rewrite E11b, Uspb, unsigned_lit_small by lia.
cbn [zall_disjoint]. unfold zdisj. cbn [fst snd].
destruct (BLK q k LINE Hq ltac:(lia)) as [Hd0 Hd1].
unfold GM_STK, GM_FRAME, LP_STK, ASTACK in *. repeat split; lia. }
clear HS. rename HSr into HS.
pose proof HJ2 as HARc2. apply ajournal_gx_AR_x in HARc2.
assert (HBxv : U Eb Bx = SHADOW_OFF).
{ unfold Bx. rewrite (U_atom Eb 32 SB ltac:(rewrite OLDb by lia; exact E32) ltac:(unfold SB; lia)).
reflexivity. }
paj_run_tok_x RUN HS HJ2 SHOKb Bspan.
{ rewrite <- (aview_rd_of SEGS), HBxv,
(U_atom_off Eb 11 LINE 13 E11b ltac:(lia) ltac:(lia)).
apply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly S hp W mem2 _ q k (LINE + 13) 1 HARc2 Hq); lia. }
{ apply awr_ok_x_of0. awr_ok_tac. exact Uspb. }
psrr_branch_tok RUN BR HS SHOKb Bspan.
* (* line[13] <> ' ': not a gesture line *)
assert (Uspc : bv_unsigned (ew (ewset (ewset Eb 512 w) 513 w0) 2) = spZ regs)
by (rewrite !ew_ewset_other by lia; exact Uspb).
assert (HAEc : env_agree 32 (Ereg regs (gm_extra b13)) (ewset (ewset Eb 512 w) 513 w0)).
{ split; [intros mm Hmm; rewrite !ew_ewset_other by lia; exact (proj1 HAEb mm Hmm)
| cbn [ewset ed]; exact (proj2 HAEb)]. }
assert (E33c : ew (ewset (ewset Eb 512 w) 513 w0) 33 = Z_to_bv 64 b13)
by (rewrite !ew_ewset_other by lia; exact E33b).
rewrite branch_ne_U, (U_atom _ 33 b13 E33c ltac:(lia)), U_lit in Hc1 by lia.
assert (GNONE : RelayModel.gesture (bzs ln) = None).
{ apply GM.nosp. unfold RelayModel.SPACE. fold b13.
destruct (Z.eqb_spec b13 32); [cbn in Hc1; discriminate | exact n]. }
paj_run_tok_x RUN HS HJ2 SHOKb Bspan. { apply awr_ok_x_of0. awr_ok_tac. exact Uspc. }
assert (KEEPB : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - GM_STK <= a < spZ regs) ->
aview SEGS (w_H W) (ms_mem ms2) a = aview SEGS (w_H W) mem a).
{ intros a Ha Hno.
rewrite (aview_kept_out _ _ (w_H W) (ms_mem ms1) (ms_mem ms2) HFr2 a Ha) by gm_outw Uspc.
rewrite (aview_kept_out Eb _ (w_H W) mem2 (ms_mem ms1) HFr1 a Ha) by gm_outw Uspb.
apply KEEP2; [exact Ha | exact Hno]. }
assert (PRESB : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms2) a).
{ intros a Hp. lazymatch goal with
| K3 : mem_grows (mrestrict (w_H W) mem2) (mrestrict (w_H W) (ms_mem ms1)),
  K4 : mem_grows (mrestrict (w_H W) (ms_mem ms1)) (mrestrict (w_H W) (ms_mem ms2)) |- _ =>
  exact (apres_of_grows _ _ _ a K4 (apres_of_grows _ _ _ a K3 (PRES2 a Hp))) end. }
prreg HS (1%bv : bv 5) RB1.
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. unfold gm_post_x.
lazymatch goal with |- exists _ _ _ _ _ _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ =>
exists ly, S, hp, r, m, d, 0, H end.
split; [cbn [ms_regs]; rewrite RB1; rewrite ?ew_ewset_other by lia; rewrite OLDb by lia;
rewrite E1, Hra; reflexivity|].
split; [cbn [ms_mem]; apply (ajournal_gx_materialize_x SEGS B PST ARx LAWS Hsegs G 0 []); exact HJ2|].
split; [lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
eapply (aregs_preserved_of_st_ok SEGS _ Ev _ _ regs (gm_extra b13) HS) end;
[first [exact HAEb | exact HAEc] | vm_compute; reflexivity]|].
split; [intros a _ _ _ Hp; apply PRESB; exact Hp|].
split; [intros ie Hie; destruct (gmm_errno_out W ly S hp regs mem md ch HPRE ie Hie) as [Hr Hn]; cbn [ms_mem]; exact (KEEPB _ Hr Hn)|].
split.
{ cbn [ms_mem]. apply (alist_at_kept B ly S W mem ly S W (ms_mem ms2) (HA + 80) H true HL).
- intros r Hr a Ha. destruct (FPLO r Hr a Ha) as [Ha0 Hahi]. split.
  + apply KEEPB; unfold GM_STK, GM_FRAME, LP_STK, ASTACK in *; lia.
  + intros Hw. apply (writable_kept (w_H W) mem (ms_mem ms2) a); [intros Hp; apply PRESB; exact Hp | exact Hw].
- exact ABL. }
split; [exact ND|].
split; [symmetry; apply GM.upd_none; exact GNONE|].
split; [destruct (Z.ltb_spec (hl_n H) (hl_n H)); [lia | reflexivity]|].
split; [intros rest Hperm; exact Hperm|].
split; [reflexivity|].
split; [rewrite (gmm_cost_none MT H ln GNONE); apply (mo_le_refl MT MTL)|].
exact (gm_rm_down S _ kr HRM).
* (* line[13] = ' ': the scan loop *)
assert (Uspc : bv_unsigned (ew (ewset (ewset Eb 512 w) 513 w0) 2) = spZ regs)
by (rewrite !ew_ewset_other by lia; exact Uspb).
assert (HAEc : env_agree 32 (Ereg regs (gm_extra b13)) (ewset (ewset Eb 512 w) 513 w0)).
{ split; [intros mm Hmm; rewrite !ew_ewset_other by lia; exact (proj1 HAEb mm Hmm)
| cbn [ewset ed]; exact (proj2 HAEb)]. }
assert (E33c : ew (ewset (ewset Eb 512 w) 513 w0) 33 = Z_to_bv 64 b13)
by (rewrite !ew_ewset_other by lia; exact E33b).
rewrite branch_ne_U, (U_atom _ 33 b13 E33c ltac:(lia)), U_lit in Hc1 by lia.
assert (HSP : nth 13 (bzs ln) 0 = RelayModel.SPACE).
{ unfold RelayModel.SPACE. fold b13.
destruct (Z.eqb_spec b13 32); [exact e | cbn in Hc1; discriminate]. }
paj_run_to_tok_x RUNTO HS HJ2 SHOKb Bspan A_gm_loop. { apply awr_ok_x_of0. awr_ok_tac. exact Uspc. }
prreg HS (10%bv : bv 5) L10. prreg HS (11%bv : bv 5) L11.
prreg HS (12%bv : bv 5) L12. prreg HS (13%bv : bv 5) L13.
(* the registers the loop head carries, and the saved words in the frame *)
pose proof (regs_kept_of_st_ok_pi _ _ _ regs (gm_extra b13)
[3%bv; 4%bv; 20%bv; 21%bv; 22%bv; 23%bv; 24%bv; 25%bv; 26%bv; 27%bv] HS HAEc
ltac:(vm_compute; reflexivity)) as HK.
cbn [ms_regs restrict] in HK.
prreg HS (8%bv : bv 5) L8. prreg HS (9%bv : bv 5) L9.
prreg HS (18%bv : bv 5) L18. prreg HS (19%bv : bv 5) L19.
pose proof (st_ok_pi_region_nth _ _ _ 1%nat _ HS eq_refl) as HRG.
cbn [ms_mem restrict] in HRG.
assert (SLOT : forall (od : Z) (n : nat) (r : bv 5),
In (YP09.mkChunk od (CVal 8 (SOff n 0)))
[YP09.mkChunk (-40) (CVal 8 (SOff 19 0)); YP09.mkChunk (-32) (CVal 8 (SOff 18 0));
 YP09.mkChunk (-24) (CVal 8 (SOff 9 0)); YP09.mkChunk (-16) (CVal 8 (SOff 8 0));
 YP09.mkChunk (-8) (CVal 8 (SOff 1 0))] ->
ew (ewset (ewset Eb 512 w) 513 w0) n = getr regs r ->
val_mem SEGS (arm W (ms_mem ms2)) (spZ regs + od) 8 (bv_unsigned (getr regs r))).
{ intros od n r Hin Hew.
apply (slot_of_region _ _ (spZ regs) _ _ _ _ _ od (SOff n 0)
(bv_unsigned (getr regs r)) HRG Uspc Hin);
[cbn [sv_denot]; rewrite Hew, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
| pose proof (bv_unsigned_in_range 64 (getr regs r)) as Hrr;
  change (bv_modulus 64) with (2 ^ 64) in Hrr; lia]. }
assert (KEEPL : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - GM_STK <= a < spZ regs) ->
aview SEGS (w_H W) (ms_mem ms2) a = aview SEGS (w_H W) mem a).
{ intros a Ha Hno.
rewrite (aview_kept_out _ _ (w_H W) (ms_mem ms1) (ms_mem ms2) HFr2 a Ha) by gm_outw Uspc.
rewrite (aview_kept_out Eb _ (w_H W) mem2 (ms_mem ms1) HFr1 a Ha) by gm_outw Uspb.
apply KEEP2; [exact Ha | exact Hno]. }
assert (PRESL : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms2) a).
{ intros a Hp. lazymatch goal with
| K3 : mem_grows (mrestrict (w_H W) mem2) (mrestrict (w_H W) (ms_mem ms1)),
  K4 : mem_grows (mrestrict (w_H W) (ms_mem ms1)) (mrestrict (w_H W) (ms_mem ms2)) |- _ =>
  exact (apres_of_grows _ _ _ a K4 (apres_of_grows _ _ _ a K3 (PRES2 a Hp))) end. }
prreg HS (2%bv : bv 5) L2.
assert (EWv : forall (n : nat), (n < 512)%nat -> ew (ewset (ewset Eb 512 w) 513 w0) n = ew Eb n)
by (intros n Hn; rewrite !ew_ewset_other by lia; reflexivity).
subst LEN.
pmkst HS.
eapply (GMSCAN_X (Z.to_nat (Z.of_nat (length ln) - 13)) W ly S hp regs mem md ch HA LINE ln H q k 0
(ms_regs ms2) (ms_mem ms2) _ HPRE H10 H11 H12 HL ND HinG HZS HAL8 GL NZ LN Hq Hqb Hq1 Hq2 LG LB LE HROM
HGROW HCAP32 HROOM MOK kr HRM HCNT HFK HSP).
-- unfold spZ. rewrite L2, ?Uspc, ?Uspb, unsigned_lit_small by (unfold spZ in *; lia).
   unfold spZ, GM_FRAME. lia.
-- rewrite (HK 3%bv (or_introl eq_refl)). exact Hgp.
-- rewrite (HK 4%bv (or_intror (or_introl eq_refl))). exact Htp.
-- rewrite L8. rewrite OLDb by lia. exact E11.
-- rewrite L9. rewrite OLDb by lia. exact E10.
-- rewrite L18. rewrite OLDb by lia. exact E12.
-- rewrite L19. rewrite OLDb by lia. exact E32.
-- intros r Hcs Hr. apply HK.
   assert (Hr8 : r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27)
   by (clear - Hr; lia).
   clear - Hr8.
   destruct Hr8 as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]; cbn [In];
   repeat first [left; apply bv_eq; vm_compute; reflexivity | right].
-- replace (spZ regs - 8) with (spZ regs + -8) by lia.
   apply (SLOT (-8) 1%nat 1%bv (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl)))))).
   rewrite EWv by lia. rewrite OLDb by lia. exact E1.
-- replace (spZ regs - 16) with (spZ regs + -16) by lia.
   apply (SLOT (-16) 8%nat 8%bv (or_intror (or_intror (or_intror (or_introl eq_refl))))).
   rewrite EWv by lia. rewrite OLDb by lia. exact E8.
-- replace (spZ regs - 24) with (spZ regs + -24) by lia.
   apply (SLOT (-24) 9%nat 9%bv (or_intror (or_intror (or_introl eq_refl)))).
   rewrite EWv by lia. rewrite OLDb by lia. exact E9.
-- replace (spZ regs - 32) with (spZ regs + -32) by lia.
   apply (SLOT (-32) 18%nat 18%bv (or_intror (or_introl eq_refl))).
   rewrite EWv by lia. rewrite OLDb by lia. exact E18.
-- replace (spZ regs - 40) with (spZ regs + -40) by lia.
   apply (SLOT (-40) 19%nat 19%bv (or_introl eq_refl)).
   rewrite EWv by lia. rewrite OLDb by lia. exact E19.
-- exact KEEPL.
-- exact PRESL.
-- rewrite wvb_collapse in HJ2. exact HJ2.
-- exact L10.
-- exact L11.
-- rewrite L12. rewrite !OLDb by lia. rewrite E11, E12.
   unfold w64. rewrite YI08.alu64_add_lit. reflexivity.
-- rewrite L13. rewrite !OLDb by lia. rewrite E11, E12.
   rewrite unsigned_lit_small by lia. unfold w64. rewrite YI08.alu64_add_lit. f_equal. lia.
-- lia.
-- lia.
-- lia.
-- intros t Ht. exfalso. lia.
-- lia.
Qed.
(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0): the entry walk at a world relation R.  ajournal_gx_x -> ajournal_gx_xR R, SRr SEGS ->
   SRrG SEGS R, the kit's journal lemmas -> their _xR twins, the runs and the branch -> their SRrG forms (W_journal_x.v
   paj_run_x_xG / paj_run_to_x_xG, W_kit.v paj_branch_xR), the returns -> the strict step lifted by SRr_SRrG (WLE_R),
   bcmp's call -> W_sites_x.v aj_bcmp_gx_at_xR (a Theorem Labs lane's engine twin), gm_post_x / gm_spec_x
   -> W_contract_xR_g6.v gm_post_xR / gm_spec_xR (a Theorem Labs lane's).  GMSCAN_XR is GMSCAN_X at R (W_gm_scan.pb_gm_scan_xR's
   statement).  The strict pb_gesture_model_x above keeps its proof. ---- *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
(* :256 GMSCAN_X at R *)
Hypothesis GMSCAN_XR : forall (fuel : nat) W ly S Hp regs mem md ch HA LINE (ln : list byte) H q k (j : Z) regsc memc mdc,
afn_pre_x SEGS B ARx GM_STK ly S Hp W regs mem md ch ->
getr regs 10 = w64 HA -> getr regs 11 = w64 LINE -> getr regs 12 = w64 (Z.of_nat (length ln)) ->
alist_at B ly S W mem (HA + 80) H true -> NoDup (texts H) ->
(forall a, HA + 80 <= a < HA + 96 -> inG G a) -> azs B (HA + 80) 16 ->
(HA + 80) mod 8 = 0 ->
garr8 SEGS (arm W mem) LINE (bzs ln) -> ~ In (Z_to_bv 8 0) ln -> Z.of_nat (length ln) <= APARTIAL ->
In (q, k) (ablocks B ly S) -> ~ In (q, k) (list_blks H) -> q <= LINE ->
LINE + Z.of_nat (length ln) <= q + req_size k ->
garr8 SEGS (arm W mem) (VAL A_lit_gesture) RelayModel.K_GESTURE ->
garr8 SEGS (arm W mem) (VAL A_lit_begin) RelayModel.W_BEGIN ->
garr8 SEGS (arm W mem) (VAL A_lit_end) RelayModel.W_END ->
rom_view SEGS W mem ->
(lp_grow H = true -> lp_vbytes H < MMAX) -> AREC * hl_cap H < 2 ^ 32 ->
blocks_bytes S + (if lp_grow H then lp_vbytes H else 0) + (Z.of_nat (length ln) + 1) <= LIVE_MAX ->
mo_ok MT S (gm_cost MT H ln) ->
forall kr : nat,
rp_RM RP S (Z.to_nat (gm_cost MT_rk H ln) + kr) ->
cnt_ok_pk RP (gm_pk H) (ablocks B ly S) ->
firstn 13 (bzs ln) = RelayModel.K_GESTURE ->
nth 13 (bzs ln) 0 = RelayModel.SPACE ->
spZ regsc = spZ regs - GM_FRAME ->
getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
getr regsc 8 = w64 LINE -> getr regsc 9 = w64 HA ->
getr regsc 18 = w64 (Z.of_nat (length ln)) -> getr regsc 19 = w64 SB ->
(forall r, acallee_saved r -> 20 <= r <= 27 -> getr regsc (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
val_mem SEGS (arm W memc) (spZ regs - 8) 8 (bv_unsigned (getr regs 1)) ->
val_mem SEGS (arm W memc) (spZ regs - 16) 8 (bv_unsigned (getr regs 8)) ->
val_mem SEGS (arm W memc) (spZ regs - 24) 8 (bv_unsigned (getr regs 9)) ->
val_mem SEGS (arm W memc) (spZ regs - 32) 8 (bv_unsigned (getr regs 18)) ->
val_mem SEGS (arm W memc) (spZ regs - 40) 8 (bv_unsigned (getr regs 19)) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - GM_STK <= a < spZ regs) ->
 aview SEGS (w_H W) memc a = aview SEGS (w_H W) mem a) ->
(forall a, apresent (w_H W) mem a -> apresent (w_H W) memc a) ->
ajournal_gx_xR SEGS B PST ARx R G 0 [] GM_STK (spZ regs) (blk_FP (list_blks H)) ly S Hp W mem md [] ly S Hp W memc mdc 0 ->
getr regsc 10 = w64 j -> getr regsc 11 = w64 32 ->
getr regsc 12 = w64 (LINE + Z.of_nat (length ln)) ->
getr regsc 13 = w64 (LINE + Z.of_nat (length ln) - 1) ->
14 <= Z.of_nat (length ln) -> 13 < Z.of_nat (length ln) + j -> j <= 0 ->
(forall t, Z.of_nat (length ln) + j <= t < Z.of_nat (length ln) ->
 nth (Z.to_nat t) (bzs ln) 0 <> RelayModel.SPACE) ->
Z.of_nat fuel = Z.of_nat (length ln) + j - 13 ->
SRrG SEGS R W (mkCfg (mkst regsc (Z_to_bv 64 (BASE + A_gm_loop)) memc (seg_rom SEGS)) mdc)
(gm_post_xR B PST ARx R MT RP G regs ly S Hp W mem md HA H ln kr).
Let RUNG := paj_run_x_xG B PST ARx LAWS R G HG 0 [].
Let RUNTOG := paj_run_to_x_xG B PST ARx LAWS R G HG 0 [].
Let BRR := paj_branch_xR (PI := PI) (R := R).
(* :388 pb_gesture_model_x *)
Theorem pb_gesture_model_xR : gm_spec_xR B PST ARx R MT RP MMAX G A_gesture_modelP.
Proof.
intros W ly S hp regs mem md ch HA LINE ln H q k HPRE H10 H11 H12 HL ND HinG HZS HAL8 GL NZ LN Hq Hqb Hq1 Hq2 LG LB LE HROM HGROW HCAP32 HROOM MOK kr HRM HCNT.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : GM_STK = 16528) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
remember (Z.of_nat (length ln)) as LEN eqn:HLEN.
set (b13 := nth 13 (bzs ln) 0).
destruct (alx_blocks _ _ _ LAWS ly S hp W mem md q k HAR Hq) as (Hq16 & Hq4096 & Hqceil & Hqh_ia & Hqpres & _).
assert (Hrq2 : k <= req_size k)
by (unfold req_size; destruct (k =? 0) eqn:Ek; [apply Z.eqb_eq in Ek | apply Z.eqb_neq in Ek]; lia).
assert (RL : 4096 <= LINE <= 140737479966720) by (unfold ASAN_CEIL in *; lia).
assert (RN : 0 <= LEN <= 6000) by (unfold APARTIAL in LN; lia).
assert (Rb : 0 <= b13 < 256).
{ unfold b13. destruct (nth_in_or_default 13 (bzs ln) 0) as [Hin | ->]; [|lia].
unfold bzs in Hin |- *. apply in_map_iff in Hin as (b & <- & _). unfold bz.
pose proof (bv_unsigned_in_range 8 b) as Rr. change (bv_modulus 8) with 256 in Rr. lia. }
destruct (gm_entry W ly S hp regs mem md ch LINE LEN b13 HPRE H11 ltac:(rewrite H12, HLEN; reflexivity) RL RN Rb) as [HS SHOK].
assert (HJ : (ajournal_gx_xR SEGS B PST ARx R G 0 []) GM_STK (spZ regs) (blk_FP (list_blks H)) ly S hp W mem md [] ly S hp W mem md 0).
{ apply (ajournal_gx_init_xR SEGS B PST ARx R_refl G 0 [] GM_STK _ ly S hp W regs mem md ch HPRE); [lia | reflexivity | lia | intros a Ha; lia]. }
remember (Eimg (Ereg regs (gm_extra b13))) as E eqn:HE. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (E1 : ew E 1 = getr regs 1) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E8 : ew E 8 = getr regs 8) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 8 8%bv eq_refl)).
assert (E9 : ew E 9 = getr regs 9) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 9 9%bv eq_refl)).
assert (E18 : ew E 18 = getr regs 18) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 18 18%bv eq_refl)).
assert (E19 : ew E 19 = getr regs 19) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 19 19%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 HA) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 LINE) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E12 : ew E 12 = Z_to_bv 64 LEN) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); rewrite H12, HLEN; reflexivity).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 b13) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E262 : ew E 262%nat = Z_to_bv 64 (VAL (A_OBJ 21))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E264 : ew E 264%nat = Z_to_bv 64 (VAL (A_OBJ 23))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E265 : ew E 265%nat = Z_to_bv 64 (VAL (A_OBJ 24))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HAE : env_agree 32 (Ereg regs (gm_extra b13)) E) by (rewrite HE; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
clear HE.
(* ---- bounds every arm needs: the list's bytes and the image are below this frame. ---- *)
assert (HLO : alloc_ceiling <= spZ regs - GM_STK) by (unfold GM_STK, GM_FRAME, LP_STK, ASTACK in *; lia).
assert (BLK : forall p n a, In (p, n) (ablocks B ly S) -> p <= a < p + req_size n ->
0 <= a /\ a < spZ regs - GM_STK).
{ intros p n a Hin Hr. destruct (alx_blocks _ _ _ LAWS ly S hp W mem md p n HAR Hin) as (_ & Hp4 & Hpc & _).
unfold GM_STK, GM_FRAME, LP_STK, ASTACK in *. split; [lia | lia]. }
assert (IMG : forall a, in_img SEGS a -> 0 <= a /\ a < spZ regs - GM_STK).
{ intros a Hin. pose proof (pa_segs_low a Hin) as Hl.
unfold kLowMemEnd, GM_STK, GM_FRAME, LP_STK, ASTACK in *. split; [lia | lia]. }
assert (FPLO : forall r, In r (alist_fp (HA + 80) H) -> forall a, fst r <= a < snd r ->
0 <= a /\ a < spZ regs - GM_STK).
{ intros r Hr a Ha. pose proof HL as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9).
unfold alist_fp in Hr. destruct Hr as [<- | Hr].
- cbn [fst snd] in Ha. apply IMG. apply (proj1 (HG a (HinG a ltac:(lia)))).
- apply in_app_or in Hr as [Hr | Hr].
+ destruct (hl_cap H =? 0) eqn:Ec; cbn [In] in Hr; [destruct Hr|].
destruct Hr as [<- | []]. apply Z.eqb_neq in Ec.
destruct V6 as [(Hc0 & _) | (Hc0 & Hinv & Hj & _)]; [lia|].
pose proof (vec_len H Hj) as Hlen. unfold gfp in Ha. cbn [fst snd] in Ha. rewrite Hlen in Ha.
pose proof (req_size_pos (AREC * hl_cap H) ltac:(unfold AREC; lia)) as [_ Hrs].
apply (BLK (hl_v H) (AREC * hl_cap H) a Hinv). lia.
+ apply in_map_iff in Hr as (rec & <- & Hrec). unfold gfp in Ha. cbn [fst snd] in Ha.
rewrite Forall_forall in V9. destruct (V9 rec Hrec) as (Rin & _).
pose proof (req_size_pos (Z.of_nat (length (snd rec)) + 1) ltac:(lia)) as [_ Hrs].
apply (BLK (fst rec) (Z.of_nat (length (snd rec)) + 1) a Rin).
unfold bzs in Ha. rewrite length_map, length_app in Ha. cbn [length] in Ha. lia. }
assert (ABL : forall b, In b (alist_blks H) -> In b (ablocks B ly S)).
{ intros b Hb. pose proof HL as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9).
unfold alist_blks in Hb. apply in_app_or in Hb as [Hb | Hb].
- destruct (hl_cap H =? 0) eqn:Ec; cbn [In] in Hb; [destruct Hb|].
destruct Hb as [<- | []]. apply Z.eqb_neq in Ec.
destruct V6 as [(Hc0 & _) | (_ & Hinv & _)]; [lia | exact Hinv].
- apply in_map_iff in Hb as (rec & <- & Hrec). rewrite Forall_forall in V9.
exact (proj1 (V9 rec Hrec)). }
unfold cfg_at. change (w64 A_gesture_modelP) with (Z_to_bv 64 A_gesture_modelP).
unfold A_gesture_modelP, A_gesture_model.
paj_run_tok_xR RUNG HS HJ SHOK Bspan. { apply awr_ok_x_of0. awr_ok_tac. exact Usp. }
psrr_branch_tok RUNG BRR HS SHOK Bspan.
- (* len < 14: GM.short, the line is not a gesture *)
rewrite branch_ltu_U, (U_atom E 12 LEN E12) in Hc by lia. rewrite U_lit in Hc by lia.
assert (Hlt : LEN < 14) by (destruct (Z.ltb_spec LEN 14); [lia | discriminate]).
assert (GNONE : RelayModel.gesture (bzs ln) = None)
by (apply GM.short; unfold bzs; rewrite length_map; lia).
paj_run_tok_xR RUNG HS HJ SHOK Bspan. { apply awr_ok_x_of0. awr_ok_tac. exact Usp. }
assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - GM_STK <= a < spZ regs) ->
aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) mem a).
{ intros a Ha Hno.
rewrite (aview_kept_out E _ (w_H W) (ms_mem ms) (ms_mem ms0) HFr0 a Ha) by gm_outw Usp.
apply (aview_kept_out E _ (w_H W) mem (ms_mem ms) HFr a Ha). gm_outw Usp. }
assert (PRES : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms0) a).
{ intros a Hp.
lazymatch goal with
| K1 : mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) (ms_mem ms)),
  K2 : mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms0)) |- _ =>
  exact (apres_of_grows _ _ _ a K2 (apres_of_grows _ _ _ a K1 Hp)) end. }
prreg HS (1%bv : bv 5) R1.
(* the return moves no world: the strict step, lifted by SRr_SRrG (WLE_R) *)
apply (SRr_SRrG SEGS R WLE_R).
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. unfold gm_post_xR.
lazymatch goal with |- exists _ _ _ _ _ _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ =>
exists ly, S, hp, r, m, d, 0, H end.
split; [cbn [ms_regs]; rewrite R1, E1, Hra; reflexivity|].
split; [cbn [ms_mem]; apply (ajournal_gx_materialize_xR SEGS B PST ARx LAWS Hsegs G 0 []); exact HJ|].
split; [eapply (aregs_preserved_of_st_ok SEGS _ E _ _ regs (gm_extra b13) HS); [exact HAE | vm_compute; reflexivity]|].
split; [intros a _ _ _ Hp; apply PRES; exact Hp|].
split; [intros ie Hie; destruct (gmm_errno_out W ly S hp regs mem md ch HPRE ie Hie) as [Hr Hn]; cbn [ms_mem]; exact (KEEP _ Hr Hn)|].
split.
{ cbn [ms_mem]. apply (alist_at_kept B ly S W mem ly S W (ms_mem ms0) (HA + 80) H true HL).
- intros r Hr a Ha. destruct (FPLO r Hr a Ha) as [Ha0 Hahi]. split.
  + apply KEEP; unfold GM_STK, GM_FRAME, LP_STK, ASTACK in *; lia.
  + intros Hw. apply (writable_kept (w_H W) mem (ms_mem ms0) a); [intros Hp; apply PRES; exact Hp | exact Hw].
- exact ABL. }
split; [exact ND|].
split; [symmetry; apply GM.upd_none; exact GNONE|].
split; [destruct (Z.ltb_spec (hl_n H) (hl_n H)); [lia | reflexivity]|].
split; [intros rest Hperm; exact Hperm|].
split; [reflexivity|].
split; [rewrite (gmm_cost_none MT H ln GNONE); apply (mo_le_refl MT MTL)|].
exact (gm_rm_down S _ kr HRM).
- (* 14 <= len: the line may be a gesture; compare the first 13 bytes with "param_gesture" *)
rewrite branch_ltu_U, (U_atom E 12 LEN E12) in Hc by lia. rewrite U_lit in Hc by lia.
assert (Hge : 14 <= LEN) by (destruct (Z.ltb_spec LEN 14); [discriminate | lia]).
paj_run_tok_xR RUNG HS HJ SHOK Bspan. { apply awr_ok_x_of0. awr_ok_tac. exact Usp. }
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3.
prreg HS (4%bv : bv 5) Q4. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
prreg HS (12%bv : bv 5) Q12.
assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - GM_STK <= a < spZ regs) ->
aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) mem a).
{ intros a Ha Hno.
rewrite (aview_kept_out E _ (w_H W) (ms_mem ms) (ms_mem ms0) HFr0 a Ha) by gm_outw Usp.
apply (aview_kept_out E _ (w_H W) mem (ms_mem ms) HFr a Ha). gm_outw Usp. }
assert (PRES1 : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms0) a).
{ intros a Hp. lazymatch goal with
| K1 : mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) (ms_mem ms)),
  K2 : mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms0)) |- _ =>
  exact (apres_of_grows _ _ _ a K2 (apres_of_grows _ _ _ a K1 Hp)) end. }
assert (Usp2 : spZ (ms_regs ms0) = spZ regs - 48).
{ unfold spZ. rewrite Q2, Usp. rewrite unsigned_lit_small by (unfold spZ in *; lia). reflexivity. }
pose proof HJ as HARc. apply ajournal_gx_AR_xR in HARc.
pose proof (pa_obj_img 21 ltac:(lia)) as HL21. pose proof (pa_val_range (A_OBJ 21)) as HV21.
assert (GA : forall j, (j < length ln)%nat ->
aview SEGS (w_H W) (ms_mem ms0) (LINE + Z.of_nat j) = Some (nth j (bzs ln) 0)).
{ intros j Hj.
assert (Hb : 0 <= LINE + Z.of_nat j /\ LINE + Z.of_nat j < spZ regs - GM_STK)
by (apply (BLK q k (LINE + Z.of_nat j) Hq); lia).
destruct Hb as [Hb0 Hb1]. rewrite (KEEP1 (LINE + Z.of_nat j) ltac:(lia) ltac:(lia)).
destruct (GL j ltac:(unfold bzs; rewrite length_map; exact Hj)) as [Hv Hr].
exact (aview_of_val_mem1 SEGS (w_H W) mem _ _ Hv Hr). }
assert (LITLO : forall (oi : nat) (n : Z), (oi < 33)%nat -> 0 <= n <= 16 ->
0 <= VAL (A_OBJ oi) + n /\ VAL (A_OBJ oi) + n < spZ regs - GM_STK).
{ intros oi n Hi Hn. pose proof (pa_obj_img oi Hi) as Hobj.
unfold GM_STK, GM_FRAME, LP_STK, ASTACK in *. split; lia. }
assert (LITA : forall j, (j < 13)%nat ->
aview SEGS (w_H W) (ms_mem ms0) (VAL (A_OBJ 21) + Z.of_nat j) = Some (nth j RelayModel.K_GESTURE 0)).
{ intros j Hj. destruct (LITLO 21%nat (Z.of_nat j) ltac:(lia) ltac:(lia)) as [Ha0 Hahi].
rewrite (KEEP1 (VAL (A_OBJ 21) + Z.of_nat j) ltac:(lia) ltac:(lia)).
destruct (LG j ltac:(vm_compute; lia)) as [Hv Hr].
change (VAL A_lit_gesture) with (VAL (A_OBJ 21)) in Hv.
exact (aview_of_val_mem1 SEGS (w_H W) mem _ _ Hv Hr). }
pose proof (pa_obj_img 21%nat ltac:(lia)) as HO21.
eapply (SRrG_bind SEGS R R_trans).
{ eapply (aj_bcmp_gx_at_xR B PST ARx LAWS R_trans WLE_R (SIGMA WS_bcmp) ABCMP G 0 ([] : list (Z * Z)) W (ms_regs ms0) (ms_mem ms0)
GM_STK (spZ regs) (blk_FP (list_blks H)) ly S hp W mem md ([] : list (Z * Z)) ly S hp _ 0
LINE (VAL (A_OBJ 21)) 13 (-48) (Z_to_bv 64 (BASE + 14588)) HG eq_refl HJ).
- rewrite Q10, E11. reflexivity.
- rewrite Q11, E262. reflexivity.
- exact Q12.
- lia.
- lia.
- lia.
- lia.
- lia.
- rewrite Usp2. lia.
- reflexivity.
- lia.
- rewrite WS. unfold ESTACK. lia.
- rewrite Q3, E3. exact Hgp.
- rewrite Q4, E4. exact Htp.
- exact Q1.
- apply ret_ok_codeptr_v; [lia | reflexivity].
- intros a Ha. destruct (BLK q k a Hq ltac:(lia)) as [Ha0 Hahi]. split.
  + replace a with (LINE + Z.of_nat (Z.to_nat (a - LINE))) by lia. rewrite GA by lia. discriminate.
  + rewrite Usp2. unfold ESTACK, GM_STK, GM_FRAME, LP_STK, ASTACK in *. lia.
- intros a Ha. destruct (LITLO 21%nat (a - VAL (A_OBJ 21)) ltac:(lia) ltac:(lia)) as [Ha0 Hahi]. split.
  + replace a with (VAL (A_OBJ 21) + Z.of_nat (Z.to_nat (a - VAL (A_OBJ 21)))) by lia.
    rewrite LITA by lia. discriminate.
  + rewrite Usp2. unfold ESTACK, GM_STK, GM_FRAME, LP_STK, ASTACK in *. lia.
- intros a Ha. destruct (BLK q k a Hq ltac:(lia)) as [Ha0 Hahi].
  unfold ESTACK, GM_STK, GM_FRAME, LP_STK, ASTACK in *. lia.
- intros a Ha. destruct (LITLO 21%nat (a - VAL (A_OBJ 21)) ltac:(lia) ltac:(lia)) as [Ha0 Hahi].
  unfold ESTACK, GM_STK, GM_FRAME, LP_STK, ASTACK in *. lia.
- apply (amem_range_of_block_x SEGS B ARx LAWS ly S hp W (ms_mem ms0) _ q k LINE 13 HARc Hq); lia.
- apply amem_range_high; [lia | left; lia | unfold ASAN_CEIL in *; lia].
- apply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly S hp W (ms_mem ms0) _ q k LINE 13 HARc Hq); lia.
- intros _. apply (shadow_hull_vis_of_block_hp0_x SEGS B ARx LAWS HP0 ly S hp W (ms_mem ms0) _ q k LINE 13 HARc Hq); lia.
- exact (proj1 (HLITG ly S hp W (ms_mem ms0) _ HARc)).
- intros Hn0. exact (proj2 (HLITG ly S hp W (ms_mem ms0) _ HARc) Hn0). }
cbv beta. intros W2 c2 Hwle2 (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP2 & Hres & Hcmp & Hfr2 & Hpres2).
jafter_call_keep_pi HS 34%nat regs2 (mrestrict (w_H W) mem2) HP2 [0]%nat HS2.
match type of HS2 with ?ty -> _ => assert (HRK : ty); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| apply Forall_nil].
unfold stack_region, GM_FRAME.
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Usp.
- intros a Ha. apply (mbyte_of_aview SEGS). apply Hfr2; unfold ESTACK in *; lia.
- intros a Ha _. apply (apresent_writable SEGS).
pose proof HJ2 as HJI. apply ajournal_gx_inner_xR in HJI. destruct HJI as (memS & HJi & _).
rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPR2 & _).
apply HPR2. unfold GM_STK, GM_FRAME, LP_STK, ASTACK in *. lia. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 34 (map (getr regs2) CLOB)) as Eb eqn:HEb in HS.
assert (HEIb : img_env VAL A_LIM Eb) by (rewrite HEb; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDb : forall m, (m < 34)%nat -> ew Eb m = ew E m) by (intros m Hm; rewrite HEb; apply YN3v.ew_havoc_old; exact Hm).
assert (HAEb : env_agree 32 (Ereg regs (gm_extra b13)) Eb)
by (rewrite HEb; apply env_agree_havoc_ge; [cbv; lia | exact HAE]).
clear HEb.
assert (SHOKb : sh_ok SEGS Bx gm_SH Eb (mrestrict (w_H W) mem2)) by (unfold sh_ok, gm_SH; constructor).
assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - GM_STK <= a < spZ regs) ->
aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) mem a).
{ intros a Ha Hno.
rewrite (Hfr2 a Ha ltac:(unfold ESTACK, GM_STK, GM_FRAME, LP_STK, ASTACK in *; lia)).
apply KEEP1; [exact Ha | exact Hno]. }
assert (PRES2 : forall a, apresent (w_H W) mem a -> apresent (w_H W) mem2 a)
by (intros a Hp; apply Hpres2; apply PRES1; exact Hp).
assert (Uspb : bv_unsigned (ew Eb 2) = spZ regs) by (rewrite OLDb by lia; rewrite E2; reflexivity).
assert (Hvr : 0 <= bv_unsigned v < 2 ^ 64)
by (pose proof (bv_unsigned_in_range 64 v) as Hr0; change (bv_modulus 64) with (2 ^ 64) in Hr0; lia).
(* the model side of the comparison *)
assert (CMPM : v = w64 0 <-> firstn 13 (bzs ln) = RelayModel.K_GESTURE).
{ rewrite Hcmp. split.
- intros Hall. apply (firstn_eq_of_nth 13); [vm_compute; reflexivity | unfold bzs; rewrite length_map; lia|].
  intros i Hi. specialize (Hall (Z.of_nat i) ltac:(lia)).
  rewrite GA in Hall by lia.
  rewrite LITA in Hall by lia. injection Hall as Hall. exact Hall.
- intros Hfk i Hi. replace i with (Z.of_nat (Z.to_nat i)) by lia.
  rewrite GA by lia. rewrite LITA by lia.
  f_equal. rewrite <- Hfk. symmetry. apply nth_of_firstn. lia. }
prreg HS (10%bv : bv 5) R10.
assert (F38 : ew Eb 38 = Z_to_bv 64 (bv_unsigned v))
by (rewrite Z_to_bv_bv_unsigned, <- R10; exact Hres).
psrr_branch_tok RUNG BRR HS SHOKb Bspan.
+ (* bcmp <> 0: the first 13 bytes are not "param_gesture" *)
rewrite branch_ne_U, (U_atom Eb 38 (bv_unsigned v) F38 Hvr), U_lit in Hc0 by lia.
assert (Hvn : bv_unsigned v <> 0)
by (destruct (Z.eqb_spec (bv_unsigned v) 0); [cbn in Hc0; discriminate | lia]).
assert (GNONE : RelayModel.gesture (bzs ln) = None).
{ apply GM.nok. intros Hfk. apply Hvn. rewrite ((proj2 CMPM) Hfk). reflexivity. }
paj_run_tok_xR RUNG HS HJ2 SHOKb Bspan. { apply awr_ok_x_of0. awr_ok_tac. exact Uspb. }
assert (KEEPA : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - GM_STK <= a < spZ regs) ->
aview SEGS (w_H W) (ms_mem ms1) a = aview SEGS (w_H W) mem a).
{ intros a Ha Hno.
rewrite (aview_kept_out Eb _ (w_H W) mem2 (ms_mem ms1) HFr1 a Ha) by gm_outw Uspb.
apply KEEP2; [exact Ha | exact Hno]. }
assert (PRESA : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms1) a).
{ intros a Hp. lazymatch goal with
| K3 : mem_grows (mrestrict (w_H W) mem2) (mrestrict (w_H W) (ms_mem ms1)) |- _ =>
  exact (apres_of_grows _ _ _ a K3 (PRES2 a Hp)) end. }
prreg HS (1%bv : bv 5) RA1.
(* the return moves no world: the strict step, lifted by SRr_SRrG (WLE_R) *)
apply (SRr_SRrG SEGS R WLE_R).
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. unfold gm_post_xR.
lazymatch goal with |- exists _ _ _ _ _ _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ =>
exists ly, S, hp, r, m, d, 0, H end.
split; [cbn [ms_regs]; rewrite RA1, OLDb by lia; rewrite E1, Hra; reflexivity|].
split; [cbn [ms_mem]; apply (ajournal_gx_materialize_xR SEGS B PST ARx LAWS Hsegs G 0 []); exact HJ2|].
split; [eapply (aregs_preserved_of_st_ok SEGS _ Eb _ _ regs (gm_extra b13) HS); [exact HAEb | vm_compute; reflexivity]|].
split; [intros a _ _ _ Hp; apply PRESA; exact Hp|].
split; [intros ie Hie; destruct (gmm_errno_out W ly S hp regs mem md ch HPRE ie Hie) as [Hr Hn]; cbn [ms_mem]; exact (KEEPA _ Hr Hn)|].
split.
{ cbn [ms_mem]. apply (alist_at_kept B ly S W mem ly S W (ms_mem ms1) (HA + 80) H true HL).
- intros r Hr a Ha. destruct (FPLO r Hr a Ha) as [Ha0 Hahi]. split.
  + apply KEEPA; unfold GM_STK, GM_FRAME, LP_STK, ASTACK in *; lia.
  + intros Hw. apply (writable_kept (w_H W) mem (ms_mem ms1) a); [intros Hp; apply PRESA; exact Hp | exact Hw].
- exact ABL. }
split; [exact ND|].
split; [symmetry; apply GM.upd_none; exact GNONE|].
split; [destruct (Z.ltb_spec (hl_n H) (hl_n H)); [lia | reflexivity]|].
split; [intros rest Hperm; exact Hperm|].
split; [reflexivity|].
split; [rewrite (gmm_cost_none MT H ln GNONE); apply (mo_le_refl MT MTL)|].
exact (gm_rm_down S _ kr HRM).
+ (* bcmp = 0: the line starts with "param_gesture" *)
rewrite branch_ne_U, (U_atom Eb 38 (bv_unsigned v) F38 Hvr), U_lit in Hc0 by lia.
assert (HFK : firstn 13 (bzs ln) = RelayModel.K_GESTURE).
{ apply (proj1 CMPM). apply bv_eq.
  destruct (Z.eqb_spec (bv_unsigned v) 0); [rewrite e; reflexivity | cbn in Hc0; discriminate]. }
assert (E11b : ew Eb 11 = Z_to_bv 64 LINE) by (rewrite OLDb by lia; exact E11).
assert (E33b : ew Eb 33 = Z_to_bv 64 b13) by (rewrite OLDb by lia; exact E33).
assert (VM13 : val_mem SEGS (mrestrict (w_H W) mem2) (LINE + 13) 1 b13).
{ apply (val_mem_kept SEGS (w_H W) (w_H W) mem mem2 (LINE + 13) 1%nat b13).
- intros kk Hkk. cbn in Hkk. replace kk with 0 by lia. rewrite Z.add_0_r.
  apply KEEP2; [lia | destruct (BLK q k (LINE + 13) Hq ltac:(lia)) as [Hd0 Hd1];
  unfold GM_STK, GM_FRAME, LP_STK, ASTACK in *; lia].
- destruct (GL 13%nat ltac:(unfold bzs; rewrite length_map; lia)) as [Hv _].
  change (Z.of_nat 13) with 13 in Hv. exact Hv. }
pose proof (st_ok_pi_add_region Eb _ _ line_region HS) as HSr.
lazymatch type of HSr with ?a -> ?b -> ?c -> _ =>
assert (Hwf : a); [vm_compute; reflexivity|];
assert (Hrok : b); [|assert (Hdis : c); [|specialize (HSr Hwf Hrok Hdis)]] end.
{ unfold line_region, region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks ms_mem restrict mkst].
cbn [base_val]. rewrite E11b, unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS Eb _ LINE (13%Z) (1%N) (SOff 33 0) b13);
[cbn [sv_denot]; rewrite E33b, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | zside |].
exact VM13. }
{ apply all_disjoint_of_extents. unfold line_region, stack_region, extent_of_region.
cbn [ss_mem add_cond map YP09.r_base YP09.r_lo YP09.r_hi].
cbn [base_val]. rewrite E11b, Uspb, unsigned_lit_small by lia.
cbn [zall_disjoint]. unfold zdisj. cbn [fst snd].
destruct (BLK q k LINE Hq ltac:(lia)) as [Hd0 Hd1].
unfold GM_STK, GM_FRAME, LP_STK, ASTACK in *. repeat split; lia. }
clear HS. rename HSr into HS.
pose proof HJ2 as HARc2. apply ajournal_gx_AR_xR in HARc2.
assert (HBxv : U Eb Bx = SHADOW_OFF).
{ unfold Bx. rewrite (U_atom Eb 32 SB ltac:(rewrite OLDb by lia; exact E32) ltac:(unfold SB; lia)).
reflexivity. }
paj_run_tok_xR RUNG HS HJ2 SHOKb Bspan.
{ rewrite <- (aview_rd_of SEGS), HBxv,
(U_atom_off Eb 11 LINE 13 E11b ltac:(lia) ltac:(lia)).
apply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly S hp W mem2 _ q k (LINE + 13) 1 HARc2 Hq); lia. }
{ apply awr_ok_x_of0. awr_ok_tac. exact Uspb. }
psrr_branch_tok RUNG BRR HS SHOKb Bspan.
* (* line[13] <> ' ': not a gesture line *)
assert (Uspc : bv_unsigned (ew (ewset (ewset Eb 512 w) 513 w0) 2) = spZ regs)
by (rewrite !ew_ewset_other by lia; exact Uspb).
assert (HAEc : env_agree 32 (Ereg regs (gm_extra b13)) (ewset (ewset Eb 512 w) 513 w0)).
{ split; [intros mm Hmm; rewrite !ew_ewset_other by lia; exact (proj1 HAEb mm Hmm)
| cbn [ewset ed]; exact (proj2 HAEb)]. }
assert (E33c : ew (ewset (ewset Eb 512 w) 513 w0) 33 = Z_to_bv 64 b13)
by (rewrite !ew_ewset_other by lia; exact E33b).
rewrite branch_ne_U, (U_atom _ 33 b13 E33c ltac:(lia)), U_lit in Hc1 by lia.
assert (GNONE : RelayModel.gesture (bzs ln) = None).
{ apply GM.nosp. unfold RelayModel.SPACE. fold b13.
destruct (Z.eqb_spec b13 32); [cbn in Hc1; discriminate | exact n]. }
paj_run_tok_xR RUNG HS HJ2 SHOKb Bspan. { apply awr_ok_x_of0. awr_ok_tac. exact Uspc. }
assert (KEEPB : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - GM_STK <= a < spZ regs) ->
aview SEGS (w_H W) (ms_mem ms2) a = aview SEGS (w_H W) mem a).
{ intros a Ha Hno.
rewrite (aview_kept_out _ _ (w_H W) (ms_mem ms1) (ms_mem ms2) HFr2 a Ha) by gm_outw Uspc.
rewrite (aview_kept_out Eb _ (w_H W) mem2 (ms_mem ms1) HFr1 a Ha) by gm_outw Uspb.
apply KEEP2; [exact Ha | exact Hno]. }
assert (PRESB : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms2) a).
{ intros a Hp. lazymatch goal with
| K3 : mem_grows (mrestrict (w_H W) mem2) (mrestrict (w_H W) (ms_mem ms1)),
  K4 : mem_grows (mrestrict (w_H W) (ms_mem ms1)) (mrestrict (w_H W) (ms_mem ms2)) |- _ =>
  exact (apres_of_grows _ _ _ a K4 (apres_of_grows _ _ _ a K3 (PRES2 a Hp))) end. }
prreg HS (1%bv : bv 5) RB1.
(* the return moves no world: the strict step, lifted by SRr_SRrG (WLE_R) *)
apply (SRr_SRrG SEGS R WLE_R).
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. unfold gm_post_xR.
lazymatch goal with |- exists _ _ _ _ _ _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ =>
exists ly, S, hp, r, m, d, 0, H end.
split; [cbn [ms_regs]; rewrite RB1; rewrite ?ew_ewset_other by lia; rewrite OLDb by lia;
rewrite E1, Hra; reflexivity|].
split; [cbn [ms_mem]; apply (ajournal_gx_materialize_xR SEGS B PST ARx LAWS Hsegs G 0 []); exact HJ2|].
split; [lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
eapply (aregs_preserved_of_st_ok SEGS _ Ev _ _ regs (gm_extra b13) HS) end;
[first [exact HAEb | exact HAEc] | vm_compute; reflexivity]|].
split; [intros a _ _ _ Hp; apply PRESB; exact Hp|].
split; [intros ie Hie; destruct (gmm_errno_out W ly S hp regs mem md ch HPRE ie Hie) as [Hr Hn]; cbn [ms_mem]; exact (KEEPB _ Hr Hn)|].
split.
{ cbn [ms_mem]. apply (alist_at_kept B ly S W mem ly S W (ms_mem ms2) (HA + 80) H true HL).
- intros r Hr a Ha. destruct (FPLO r Hr a Ha) as [Ha0 Hahi]. split.
  + apply KEEPB; unfold GM_STK, GM_FRAME, LP_STK, ASTACK in *; lia.
  + intros Hw. apply (writable_kept (w_H W) mem (ms_mem ms2) a); [intros Hp; apply PRESB; exact Hp | exact Hw].
- exact ABL. }
split; [exact ND|].
split; [symmetry; apply GM.upd_none; exact GNONE|].
split; [destruct (Z.ltb_spec (hl_n H) (hl_n H)); [lia | reflexivity]|].
split; [intros rest Hperm; exact Hperm|].
split; [reflexivity|].
split; [rewrite (gmm_cost_none MT H ln GNONE); apply (mo_le_refl MT MTL)|].
exact (gm_rm_down S _ kr HRM).
* (* line[13] = ' ': the scan loop *)
assert (Uspc : bv_unsigned (ew (ewset (ewset Eb 512 w) 513 w0) 2) = spZ regs)
by (rewrite !ew_ewset_other by lia; exact Uspb).
assert (HAEc : env_agree 32 (Ereg regs (gm_extra b13)) (ewset (ewset Eb 512 w) 513 w0)).
{ split; [intros mm Hmm; rewrite !ew_ewset_other by lia; exact (proj1 HAEb mm Hmm)
| cbn [ewset ed]; exact (proj2 HAEb)]. }
assert (E33c : ew (ewset (ewset Eb 512 w) 513 w0) 33 = Z_to_bv 64 b13)
by (rewrite !ew_ewset_other by lia; exact E33b).
rewrite branch_ne_U, (U_atom _ 33 b13 E33c ltac:(lia)), U_lit in Hc1 by lia.
assert (HSP : nth 13 (bzs ln) 0 = RelayModel.SPACE).
{ unfold RelayModel.SPACE. fold b13.
destruct (Z.eqb_spec b13 32); [exact e | cbn in Hc1; discriminate]. }
paj_run_to_tok_xR RUNTOG HS HJ2 SHOKb Bspan A_gm_loop. { apply awr_ok_x_of0. awr_ok_tac. exact Uspc. }
prreg HS (10%bv : bv 5) L10. prreg HS (11%bv : bv 5) L11.
prreg HS (12%bv : bv 5) L12. prreg HS (13%bv : bv 5) L13.
(* the registers the loop head carries, and the saved words in the frame *)
pose proof (regs_kept_of_st_ok_pi _ _ _ regs (gm_extra b13)
[3%bv; 4%bv; 20%bv; 21%bv; 22%bv; 23%bv; 24%bv; 25%bv; 26%bv; 27%bv] HS HAEc
ltac:(vm_compute; reflexivity)) as HK.
cbn [ms_regs restrict] in HK.
prreg HS (8%bv : bv 5) L8. prreg HS (9%bv : bv 5) L9.
prreg HS (18%bv : bv 5) L18. prreg HS (19%bv : bv 5) L19.
pose proof (st_ok_pi_region_nth _ _ _ 1%nat _ HS eq_refl) as HRG.
cbn [ms_mem restrict] in HRG.
assert (SLOT : forall (od : Z) (n : nat) (r : bv 5),
In (YP09.mkChunk od (CVal 8 (SOff n 0)))
[YP09.mkChunk (-40) (CVal 8 (SOff 19 0)); YP09.mkChunk (-32) (CVal 8 (SOff 18 0));
 YP09.mkChunk (-24) (CVal 8 (SOff 9 0)); YP09.mkChunk (-16) (CVal 8 (SOff 8 0));
 YP09.mkChunk (-8) (CVal 8 (SOff 1 0))] ->
ew (ewset (ewset Eb 512 w) 513 w0) n = getr regs r ->
val_mem SEGS (arm W (ms_mem ms2)) (spZ regs + od) 8 (bv_unsigned (getr regs r))).
{ intros od n r Hin Hew.
apply (slot_of_region _ _ (spZ regs) _ _ _ _ _ od (SOff n 0)
(bv_unsigned (getr regs r)) HRG Uspc Hin);
[cbn [sv_denot]; rewrite Hew, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
| pose proof (bv_unsigned_in_range 64 (getr regs r)) as Hrr;
  change (bv_modulus 64) with (2 ^ 64) in Hrr; lia]. }
assert (KEEPL : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - GM_STK <= a < spZ regs) ->
aview SEGS (w_H W) (ms_mem ms2) a = aview SEGS (w_H W) mem a).
{ intros a Ha Hno.
rewrite (aview_kept_out _ _ (w_H W) (ms_mem ms1) (ms_mem ms2) HFr2 a Ha) by gm_outw Uspc.
rewrite (aview_kept_out Eb _ (w_H W) mem2 (ms_mem ms1) HFr1 a Ha) by gm_outw Uspb.
apply KEEP2; [exact Ha | exact Hno]. }
assert (PRESL : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms2) a).
{ intros a Hp. lazymatch goal with
| K3 : mem_grows (mrestrict (w_H W) mem2) (mrestrict (w_H W) (ms_mem ms1)),
  K4 : mem_grows (mrestrict (w_H W) (ms_mem ms1)) (mrestrict (w_H W) (ms_mem ms2)) |- _ =>
  exact (apres_of_grows _ _ _ a K4 (apres_of_grows _ _ _ a K3 (PRES2 a Hp))) end. }
prreg HS (2%bv : bv 5) L2.
assert (EWv : forall (n : nat), (n < 512)%nat -> ew (ewset (ewset Eb 512 w) 513 w0) n = ew Eb n)
by (intros n Hn; rewrite !ew_ewset_other by lia; reflexivity).
subst LEN.
pmkst HS.
eapply (GMSCAN_XR (Z.to_nat (Z.of_nat (length ln) - 13)) W ly S hp regs mem md ch HA LINE ln H q k 0
(ms_regs ms2) (ms_mem ms2) _ HPRE H10 H11 H12 HL ND HinG HZS HAL8 GL NZ LN Hq Hqb Hq1 Hq2 LG LB LE HROM
HGROW HCAP32 HROOM MOK kr HRM HCNT HFK HSP).
-- unfold spZ. rewrite L2, ?Uspc, ?Uspb, unsigned_lit_small by (unfold spZ in *; lia).
   unfold spZ, GM_FRAME. lia.
-- rewrite (HK 3%bv (or_introl eq_refl)). exact Hgp.
-- rewrite (HK 4%bv (or_intror (or_introl eq_refl))). exact Htp.
-- rewrite L8. rewrite OLDb by lia. exact E11.
-- rewrite L9. rewrite OLDb by lia. exact E10.
-- rewrite L18. rewrite OLDb by lia. exact E12.
-- rewrite L19. rewrite OLDb by lia. exact E32.
-- intros r Hcs Hr. apply HK.
   assert (Hr8 : r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27)
   by (clear - Hr; lia).
   clear - Hr8.
   destruct Hr8 as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]; cbn [In];
   repeat first [left; apply bv_eq; vm_compute; reflexivity | right].
-- replace (spZ regs - 8) with (spZ regs + -8) by lia.
   apply (SLOT (-8) 1%nat 1%bv (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl)))))).
   rewrite EWv by lia. rewrite OLDb by lia. exact E1.
-- replace (spZ regs - 16) with (spZ regs + -16) by lia.
   apply (SLOT (-16) 8%nat 8%bv (or_intror (or_intror (or_intror (or_introl eq_refl))))).
   rewrite EWv by lia. rewrite OLDb by lia. exact E8.
-- replace (spZ regs - 24) with (spZ regs + -24) by lia.
   apply (SLOT (-24) 9%nat 9%bv (or_intror (or_intror (or_introl eq_refl)))).
   rewrite EWv by lia. rewrite OLDb by lia. exact E9.
-- replace (spZ regs - 32) with (spZ regs + -32) by lia.
   apply (SLOT (-32) 18%nat 18%bv (or_intror (or_introl eq_refl))).
   rewrite EWv by lia. rewrite OLDb by lia. exact E18.
-- replace (spZ regs - 40) with (spZ regs + -40) by lia.
   apply (SLOT (-40) 19%nat 19%bv (or_introl eq_refl)).
   rewrite EWv by lia. rewrite OLDb by lia. exact E19.
-- exact KEEPL.
-- exact PRESL.
-- rewrite wvb_collapse in HJ2. exact HJ2.
-- exact L10.
-- exact L11.
-- rewrite L12. rewrite !OLDb by lia. rewrite E11, E12.
   unfold w64. rewrite YI08.alu64_add_lit. reflexivity.
-- rewrite L13. rewrite !OLDb by lia. rewrite E11, E12.
   rewrite unsigned_lit_small by lia. unfold w64. rewrite YI08.alu64_add_lit. f_equal. lia.
-- lia.
-- lia.
-- lia.
-- intros t Ht. exfalso. lia.
-- lia.
Qed.
End wR.
End c.

(* ---- THE AR STATEMENT, re-derived (route (b), step 3; CONVERSION.md (sha256 1015972e02a9; internal record) 3.-4.): pb_gesture_model's statement is the AR
   walk's, unchanged, now a corollary of pb_gesture_model_x at ARx := ARi0, PST := [] through W_contract_x
   gm_spec_x_AR0.  LX0 replaces LAWS; HP0 at ARi0 is ARi0_hp0; ABCMP / HLITG become their ARi0 forms by the kit's
   W_sites_x abcmp_realizes_x_of_AR0 / W_contract_x ashp_x_ARi0_of; the old GMSCAN gives GMSCAN_X at ARi0 (its pre and
   journal at ARi0 are the AR ones by W_journal_x afn_pre_x_ARi0_to_AR / ajournal_gx_x_ARi0_AR, its post the generic
   one by W_contract_x gm_post_x_of_AR0). ---- *)
Section r.
Variable B : asyms.
Variable MT : ameter_ops.
Variable MMAX : Z.
Variable G : list (Z * Z).
Hypothesis LX0 : AR_laws_x SEGS B (ARi0 SEGS B) 0.
Hypothesis TL : PALib B.
Hypothesis HG : gx_ok SEGS B G.
Hypothesis MTL : ameter_laws MT.
Hypothesis ABCMP : abcmp_realizes SEGS B (SIGMA WS_bcmp).
Hypothesis LFIND : lfind_spec B G (BASE + AF_fr_list_find).
Hypothesis LPUSH : lp_spec B MT G MMAX (BASE + AF_fr_list_push).
Hypothesis LDROP : ldrop_spec B MT G (BASE + AF_fr_list_drop).
Hypothesis HLITG : ashp B (VAL A_lit_gesture) 13.
Hypothesis HLITB : ashp B (VAL A_lit_begin) 5.
Hypothesis HLITE : ashp B (VAL A_lit_end) 3.
Hypothesis GMSCAN : forall (fuel : nat) W ly S regs mem md ch HA LINE (ln : list byte) H q k (j : Z)
regsc memc mdc,
afn_pre SEGS B GM_STK ly S W regs mem md ch ->
getr regs 10 = w64 HA -> getr regs 11 = w64 LINE -> getr regs 12 = w64 (Z.of_nat (length ln)) ->
alist_at B ly S W mem (HA + 80) H true -> NoDup (texts H) ->
(forall a, HA + 80 <= a < HA + 96 -> inG G a) -> azs B (HA + 80) 16 ->
(HA + 80) mod 8 = 0 ->
garr8 SEGS (arm W mem) LINE (bzs ln) -> ~ In (Z_to_bv 8 0) ln -> Z.of_nat (length ln) <= APARTIAL ->
In (q, k) (ablocks B ly S) -> ~ In (q, k) (list_blks H) -> q <= LINE ->
LINE + Z.of_nat (length ln) <= q + req_size k ->
garr8 SEGS (arm W mem) (VAL A_lit_gesture) RelayModel.K_GESTURE ->
garr8 SEGS (arm W mem) (VAL A_lit_begin) RelayModel.W_BEGIN ->
garr8 SEGS (arm W mem) (VAL A_lit_end) RelayModel.W_END ->
rom_view SEGS W mem ->
(lp_grow H = true -> lp_vbytes H < MMAX) -> AREC * hl_cap H < 2 ^ 32 ->
blocks_bytes S + (if lp_grow H then lp_vbytes H else 0) + (Z.of_nat (length ln) + 1) <= LIVE_MAX ->
mo_ok MT S (gm_cost MT H ln) ->
firstn 13 (bzs ln) = RelayModel.K_GESTURE ->
nth 13 (bzs ln) 0 = RelayModel.SPACE ->
spZ regsc = spZ regs - GM_FRAME ->
getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
getr regsc 8 = w64 LINE -> getr regsc 9 = w64 HA ->
getr regsc 18 = w64 (Z.of_nat (length ln)) -> getr regsc 19 = w64 SB ->
(forall r, acallee_saved r -> 20 <= r <= 27 -> getr regsc (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
val_mem SEGS (arm W memc) (spZ regs - 8) 8 (bv_unsigned (getr regs 1)) ->
val_mem SEGS (arm W memc) (spZ regs - 16) 8 (bv_unsigned (getr regs 8)) ->
val_mem SEGS (arm W memc) (spZ regs - 24) 8 (bv_unsigned (getr regs 9)) ->
val_mem SEGS (arm W memc) (spZ regs - 32) 8 (bv_unsigned (getr regs 18)) ->
val_mem SEGS (arm W memc) (spZ regs - 40) 8 (bv_unsigned (getr regs 19)) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - GM_STK <= a < spZ regs) ->
 aview SEGS (w_H W) memc a = aview SEGS (w_H W) mem a) ->
(forall a, apresent (w_H W) mem a -> apresent (w_H W) memc a) ->
@ajournal_gx _ SK SEGS B G 0 [] GM_STK (spZ regs) (blk_FP (list_blks H))
 ly S W mem md [] ly S W memc mdc 0 ->
getr regsc 10 = w64 j -> getr regsc 11 = w64 32 ->
getr regsc 12 = w64 (LINE + Z.of_nat (length ln)) ->
getr regsc 13 = w64 (LINE + Z.of_nat (length ln) - 1) ->
14 <= Z.of_nat (length ln) -> 13 < Z.of_nat (length ln) + j -> j <= 0 ->
(forall t, Z.of_nat (length ln) + j <= t < Z.of_nat (length ln) ->
 nth (Z.to_nat t) (bzs ln) 0 <> RelayModel.SPACE) ->
Z.of_nat fuel = Z.of_nat (length ln) + j - 13 ->
SRr SEGS W (mkCfg (mkst regsc (Z_to_bv 64 (BASE + A_gm_loop)) memc (seg_rom SEGS)) mdc)
(gm_post B MT G regs ly S W mem md HA H ln).
(* a premise at ARi0 turned into its AR form (the pre gives Hp = []), then fed to the AR hypothesis; the room round's
   kr, rp_RM and cnt_ok_pk premises have no AR counterpart and are skipped *)
Local Ltac go1 H :=
  lazymatch goal with
  | |- forall _, _ =>
    let x := fresh "x" in intro x;
    lazymatch type of x with
    | nat => idtac
    | context [rp_RM] => idtac
    | context [cnt_ok_pk] => idtac
    | _ =>
      lazymatch type of x with
      | context [@afn_pre_x] =>
        let E := fresh "E" in pose proof (proj2 (proj1 x)) as E; apply afn_pre_x_ARi0_to_AR in x;
        lazymatch type of E with ?v = _ => subst v end
      | context [@ajournal_gx_x] => apply ajournal_gx_x_ARi0_AR in x
      | _ => idtac
      end;
      specialize (H x)
    end; go1 H
  | |- _ => idtac
  end.
Theorem pb_gesture_model : gm_spec B MT MMAX G A_gesture_modelP.
Proof.
apply gm_spec_x_AR0.
pose proof (ARi0_hp0 SEGS B) as HP0.
pose proof (abcmp_realizes_x_of_AR0 SEGS B _ ABCMP) as ABCMPx.
pose proof (ashp_x_ARi0_of B _ _ HLITG) as HLITGx.
eapply (pb_gesture_model_x B MT RP_AR MMAX G [] (ARi0 SEGS B)); try eassumption.
intros fuel W1 ly1 S1 Hp1. specialize (GMSCAN fuel W1 ly1 S1). go1 GMSCAN.
eapply SRr_mono; [exact GMSCAN | cbv beta; intros W2 c2 _ HQ; apply gm_post_x_of_AR0; exact HQ].
Qed.
End r.
End b.
End a.

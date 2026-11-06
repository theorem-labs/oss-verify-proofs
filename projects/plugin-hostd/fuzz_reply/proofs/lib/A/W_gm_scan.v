(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: one cut lemma of fuzz_reply's gesture_model ASan walk (lane W4, sub-lane
   W4Gesture.WalkGestureModel): the backward scan 0x85c18 .. 0x85c54 for the last space of the line, in the donor's
   loop form (proofs/cgif/cgif_file_fuzzer/lib/A/AC8b.v:50-255: a loop lemma stated from the loop head with concrete
   register facts, proved by induction on a nat fuel; each iteration builds a fresh symbolic state with
   pa_entry_st_ok_full and runs back to the head).
   Section hypotheses: the header of A/W_gesture_model.v verbatim, plus GMFOUND (lane W4Gesture's other hand,
   A/W_gm_found.v: the walk from 0x85c58 to the end).
   ARx conversion (route (b), step 3; CONVERSION.md (sha256 1015972e02a9; internal record)): Section c proves pb_gm_scan_x over a generic
   allocator relation ARx (LAWS / HP0, GMFOUND_X = W_gm_found.pb_gm_found_x's statement); Section r re-derives
   gm_scan, statement unchanged, at ARx := W_journal_x.ARi0. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require RelayModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep CheckRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_syms W_listing W_pl W_kit W_contract W_rep W_journal W_sites W_frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_shadow_pin.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG YCe5x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_journal_x W_sites_x W_contract_x W_kit_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_contract_xR W_contract_xR_g3 W_contract_xR_g6.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* The model's side: lib/Prog/RelayModel.v:239-277 (gesture, upd), read the way gesture_model's code reads a line.
   Copied verbatim from A/W_gesture_model.v (self-contained). *)
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

(* The loop's three address sums, as the alias list states them: register n plus a0 (the scan's index, a
   non-positive Z held as a 64-bit wrap) is atom t at offset c.  The executor's s_alu2 (Reusable/YP0e.v:1523)
   rewrites each sum to that atom offset, which is what the shadow pattern and the region lookup need. *)
Lemma u_alias_add : forall E (n t : nat) (v jj c : Z),
ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> ew E 10 = w64 jj ->
ew E t = Z_to_bv 64 (v + jj - c) -> 0 <= v + jj - c < 2 ^ 64 -> 0 <= v + jj < 2 ^ 64 ->
sv_denot E (SAlu ALU_ADD (SOff n 0) (SOff 10 0)) = sv_denot E (SOff t c).
Proof.
intros E n t v jj c Hn Hv H10 Ht Hr Hs.
apply U_inj. rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_atom E n v Hn Hv), (U_atom_off E t (v + jj - c) c Ht ltac:(lia) ltac:(lia)).
rewrite U_SOff, H10. unfold w64. rewrite Z_to_bv_unsigned, Z.add_0_r.
unfold zcanon, M64, bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite Zmod_mod, Zplus_mod_idemp_r, Z.mod_small by lia. lia.
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
(* ---- THE GENERIC WALK (route (b), step 3): the scan loop over any allocator relation ARx with its laws.  The Section
   hypotheses beyond the AR walk's: PST / ARx / hl / LAWS (the generic relation) and HP0 (no hidden head in any ARx
   state, a Theorem Labs lane's ruling); the callees are their _x specs at the same PST / ARx, and GMFOUND_X is
   W_gm_found.pb_gm_found_x's statement verbatim. ---- *)
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

(* The walk from 0x85c58 (A_gm_found): A/W_gm_found.v pb_gm_found_x, verbatim. *)
Hypothesis GMFOUND_X : forall W ly S Hp regs mem md ch HA LINE (ln : list byte) H q k (js : Z) regsc memc mdc,
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
RelayModel.last_space_from 0 (bzs ln) = Some (Z.to_nat js) ->
13 <= js < Z.of_nat (length ln) ->
getr regsc 10 = w64 (js + 1 - Z.of_nat (length ln)) ->
SRr SEGS W (mkCfg (mkst regsc (Z_to_bv 64 (BASE + A_gm_found)) memc (seg_rom SEGS)) mdc)
(gm_post_x B PST ARx MT RP G regs ly S Hp W mem md HA H ln kr).

Let RUN := paj_run_x_x B PST ARx LAWS G HG 0 [].
Let RUNTO := paj_run_to_x_x B PST ARx LAWS G HG 0 [].
Let BR := paj_branch (PI := PI).
(* s3 (x19) holds the shadow base at the loop head: the shadow pattern's Bx is that register's atom. *)
Definition Bx : sv := SOff 19 0.
Definition Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
(* atom 32 = P, the scanned byte's address; 33 = its value; 34 = len + j, the loop counter's sum *)
Definition gs_extra (P Bv Q : Z) : list word := map (Z_to_bv 64) [P; Bv; Q].
Definition line_region : YP09.region :=
YP09.mkRegion (Some 32%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 33 0))].
Definition gs_regions : smem := [ line_region ].
(* a3 + a0 and a2 + a0 are the byte's address and the one after it; s2 + a0 is len + j.  The executor's s_alu2
   (Reusable/YP0e.v:1523) rewrites each sum through these to a plain atom offset, which is what the ASan shadow
   pattern (Reusable/YCbn.v:61-85 match_x) and the region lookup need. *)
(* The sstate is vm_compute'd by the run tactics, so every numeral in it is CLOSED: the atoms' facts bound the
   scanned address, the byte and the counter by the contract's own constants, and the iteration's actual values
   live only in the environment (ew E n).  Atom 34's range INCLUDES 0 on purpose: that leaves the back edge's
   `bnez a4` undecidable, so the executor stops there instead of unrolling the loop for the whole fuel. *)
Definition gs_facts : facts :=
mkFacts [ (19%nat, mkAF SB SB 0); (32%nat, mkAF 4096 140737479966720 0); (33%nat, mkAF 0 255 0);
(34%nat, mkAF 0 6000 0) ] []
[ (SAlu ALU_ADD (SOff 13 0) (SOff 10 0), SOff 32 0);
  (SAlu ALU_ADD (SOff 12 0) (SOff 10 0), SOff 32 1);
  (SAlu ALU_ADD (SOff 18 0) (SOff 10 0), SOff 34 0) ].
Definition ss_gs : sstate := mkSS A_gm_loop sr_atoms gs_regions None gs_facts.
Definition gs_SH : list shent := [].

Lemma gs_entry : forall (W : world SEGS) (regsc : bvmap 5 word) (memc : word -> option byte) (A2 A3 j LEN P Bv Q : Z),
getr regsc 10 = w64 j -> getr regsc 12 = w64 A2 -> getr regsc 13 = w64 A3 ->
getr regsc 18 = w64 LEN -> getr regsc 19 = w64 SB ->
A3 = A2 - 1 -> P = A3 + j -> Q = LEN + j ->
0 <= A2 < 2 ^ 64 -> 0 <= A3 < 2 ^ 64 -> 0 <= LEN < 2 ^ 64 ->
4096 <= P <= 140737479966720 -> 0 <= Q <= 6000 -> 0 <= Bv < 256 ->
val_mem SEGS (mrestrict (w_H W) memc) P 1 Bv ->
st_ok_pi SEGS VAL (Eimg (Ereg regsc (gs_extra P Bv Q))) ss_gs
(restrict (w_H W) (mkst regsc (Z_to_bv 64 (BASE + A_gm_loop)) memc (seg_rom SEGS)))
/\ sh_ok SEGS Bx gs_SH (Eimg (Ereg regsc (gs_extra P Bv Q))) (mrestrict (w_H W) memc).
Proof.
intros W regsc memc A2 A3 j LEN P Bv Q H10 H12 H13 H18 H19 EA3 EP EQ RA2 RA3 RLEN RPa RQ RB VM.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regsc (gs_extra P Bv Q))).
assert (E10 : ew E 10 = getr regsc 10) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsc _ 10 10%bv eq_refl)).
assert (E12 : ew E 12 = getr regsc 12) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsc _ 12 12%bv eq_refl)).
assert (E13 : ew E 13 = getr regsc 13) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsc _ 13 13%bv eq_refl)).
assert (E18 : ew E 18 = getr regsc 18) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsc _ 18 18%bv eq_refl)).
assert (E19 : ew E 19 = getr regsc 19) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsc _ 19 19%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 P) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsc _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 Bv) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsc _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 Q) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsc _ 2)).
assert (UJ : bv_unsigned (w64 j) = j mod 2 ^ 64).
{ unfold w64. rewrite Z_to_bv_unsigned. reflexivity. }
split.
- unfold ss_gs. apply pa_entry_st_ok_full.
+ apply regs_ok_Eimg_Ereg.
+ vm_compute. reflexivity.
+ unfold gs_regions, line_region; repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
cbn [base_val]. rewrite E32, unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ P 0 1 (SOff 33 0) Bv);
[cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | zside |].
rewrite Z.add_0_r. exact VM.
+ apply pairwise_disjoint_of_extents. unfold gs_regions, line_region, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. cbn [zpairwise_disjoint zall_disjoint]. repeat split.
+ split; [|split; [exact I|]].
* cbn [gs_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E19, E32, E33, E34, H19, !unsigned_lit_small by (unfold SB; lia).
rewrite !Z.pow_0_r, !Z.mod_1_r.
repeat match goal with |- _ /\ _ => split end; unfold SB; lia.
* cbn [gs_facts f_alias alias_ok]. split; [|split; [|split; [|exact I]]].
-- apply (u_alias_add E 13 32 A3 j 0);
[rewrite E13, H13; reflexivity | lia | rewrite E10, H10; reflexivity
| rewrite E32; f_equal; lia | lia | lia].
-- apply (u_alias_add E 12 32 A2 j 1);
[rewrite E12, H12; reflexivity | lia | rewrite E10, H10; reflexivity
| rewrite E32; f_equal; lia | lia | lia].
-- apply (u_alias_add E 18 34 LEN j 0);
[rewrite E18, H18; reflexivity | lia | rewrite E10, H10; reflexivity
| rewrite E34; f_equal; lia | lia | lia].
- unfold sh_ok, gs_SH. constructor.
Qed.

(* the loop's regions write nothing: every byte is outside their writable windows *)
Ltac gs_outw :=
let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
intros (r & Hin & Hr); cbn [ss_mem add_cond ss_gs gs_regions In] in Hin;
repeat (destruct Hin as [<- | Hin];
[ cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi line_region] in Hr; lia | ]);
destruct Hin.
(* the view after the runs is the view at the loop head: chain the runs' frames back to memc *)
Ltac gs_meq :=
let a := fresh "a" in let Ha := fresh "Ha" in
intros a Ha;
repeat match goal with
| HFx : frame_of _ _ (mrestrict _ ?m0) (mrestrict _ ?m1) |- aview _ _ ?m1 _ = _ =>
  rewrite (aview_kept_out _ _ _ m0 m1 HFx a Ha) by gs_outw
end; reflexivity.
Ltac gs_in := cbn [In]; repeat first [left; reflexivity | right].
(* x20 .. x27 are in a kept-register list *)
Ltac gs_cs r Hr :=
let Hr8 := fresh "Hr8" in
assert (Hr8 : r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by (clear - Hr; lia);
clear - Hr8;
destruct Hr8 as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]; cbn [In];
repeat first [left; apply bv_eq; vm_compute; reflexivity | right].
Ltac gs_spr := unfold GM_STK, GM_FRAME, LP_STK, ASTACK, ASAN_CEIL in *; lia.
Lemma gs_vm : forall (W : world SEGS) (m m' : word -> option byte) a n v,
(forall b, 0 <= b < 2 ^ 64 -> aview SEGS (w_H W) m' b = aview SEGS (w_H W) m b) ->
0 <= a -> a + Z.of_nat n <= 2 ^ 64 -> val_mem SEGS (arm W m) a n v -> val_mem SEGS (arm W m') a n v.
Proof.
intros W m m' a n v Hk H0 H1 Hv. unfold arm in *.
apply (val_mem_kept SEGS (w_H W) (w_H W) m m' a n v); [intros kk Hkk; apply Hk; lia | exact Hv].
Qed.

(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0): the scan loop at a world relation R, R a Section variable with its laws R_refl /
   R_trans / WLE_R.  Against the strict texts: ajournal_gx_x SEGS B PST ARx -> ajournal_gx_xR SEGS B PST ARx R, SRr SEGS
   -> SRrG SEGS R, gm_post_x B PST ARx -> gm_post_xR B PST ARx R; GMFOUND_XR is GMFOUND_X under these substitutions,
   the text of W_gm_found.v pb_gm_found_xR, so a composer discharges it with that lemma; the runs and the branch are
   their SRrG forms (W_journal_x.v paj_run_x_xG / paj_run_to_x_xG, W_kit.v paj_branch_xR).  The loop calls no allocator
   function, so the list_push / list_drop contracts are not premises here.  pb_gm_scan_x below is pb_gm_scan_xR at
   R := wle (GMFOUND_X is GMFOUND_XR at wle, by conversion). ---- *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
(* :190 GMFOUND_X at R *)
Hypothesis GMFOUND_XR : forall W ly S Hp regs mem md ch HA LINE (ln : list byte) H q k (js : Z) regsc memc mdc,
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
RelayModel.last_space_from 0 (bzs ln) = Some (Z.to_nat js) ->
13 <= js < Z.of_nat (length ln) ->
getr regsc 10 = w64 (js + 1 - Z.of_nat (length ln)) ->
SRrG SEGS R W (mkCfg (mkst regsc (Z_to_bv 64 (BASE + A_gm_found)) memc (seg_rom SEGS)) mdc)
(gm_post_xR B PST ARx R MT RP G regs ly S Hp W mem md HA H ln kr).
Let RUNG := paj_run_x_xG B PST ARx LAWS R G HG 0 [].
Let RUNTOG := paj_run_to_x_xG B PST ARx LAWS R G HG 0 [].
Let BRR := paj_branch_xR (PI := PI) (R := R).
(* :346 pb_gm_scan_x *)
Lemma pb_gm_scan_xR : forall (fuel : nat) W ly S Hp regs mem md ch HA LINE (ln : list byte) H q k (j : Z) regsc memc mdc,
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
Proof.
induction fuel as [|fuel IH]; intros W ly S hp regs mem md ch HA LINE ln H q k j regsc memc mdc
HPRE Hr10 Hr11 Hr12 HL ND HinG HZS HA8 GL NZ LN Hq Hqb Hq1 Hq2 LG LB LE HROM HGROW HAREC HROOM MOK kr HRM HCNT
HFK HSP Uspc Cgp Ctp Cs0 Cs1 Cs2 Cs3 CKEPT VRA VS0 VS1 VS2 VS3 KEEPc PRESc HJ
C10 C11 C12 C13 HLEN14 HJ13 HJ0 HINV HFUEL; [lia|].
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp0 & Htp0 & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : GM_STK = 16528) by reflexivity.
remember (Z.of_nat (length ln)) as LEN eqn:HLEN.
destruct (alx_blocks _ _ _ LAWS ly S hp W mem md q k HAR0 Hq) as (Hq16 & Hq4096 & Hqceil & Hqh_ia & Hqpres & _).
assert (Hrq1 : 1 <= req_size k) by lia.
assert (Hrq2 : k <= req_size k)
by (unfold req_size; destruct (k =? 0) eqn:Ek; [apply Z.eqb_eq in Ek | apply Z.eqb_neq in Ek]; lia).
assert (HLO : alloc_ceiling <= spZ regs - GM_STK) by (unfold GM_STK, GM_FRAME, LP_STK, ASTACK in *; lia).
assert (BLK : forall a, q <= a < q + req_size k -> 0 <= a /\ a < spZ regs - GM_STK)
by (intros a Ha; unfold ASAN_CEIL in *; split; lia).
set (idx := LEN + j - 1).
set (Bv := nth (Z.to_nat idx) (bzs ln) 0).
assert (Hidx : 13 <= idx < LEN) by (unfold idx; lia).
assert (Hlnl : Z.of_nat (length (bzs ln)) = LEN) by (unfold bzs; rewrite length_map; lia).
destruct (GL (Z.to_nat idx) ltac:(lia)) as [Hvb Hrb].
assert (HPlo : q <= LINE + idx < q + req_size k) by lia.
destruct (BLK (LINE + idx) HPlo) as [HPl0 HPl1].
assert (VMP : val_mem SEGS (mrestrict (w_H W) memc) (LINE + idx) 1 Bv).
{ apply (val_mem_kept SEGS (w_H W) (w_H W) mem memc (LINE + idx) 1%nat Bv).
- intros kk Hkk. cbn in Hkk. replace kk with 0 by lia. rewrite Z.add_0_r.
  apply KEEPc; unfold GM_STK, GM_FRAME, LP_STK, ASTACK in *; lia.
- unfold Bv. replace (LINE + idx) with (LINE + Z.of_nat (Z.to_nat idx)) by lia. exact Hvb. }
destruct (gs_entry W regsc memc (LINE + LEN) (LINE + LEN - 1) j LEN (LINE + idx) Bv (LEN + j)
C10 C12 C13 Cs2 Cs3 ltac:(lia) ltac:(unfold idx; lia) ltac:(lia)
ltac:(unfold ASAN_CEIL in *; lia) ltac:(unfold ASAN_CEIL in *; lia) ltac:(lia)
ltac:(unfold ASAN_CEIL in *; lia) ltac:(unfold APARTIAL in *; lia) Hrb VMP) as [HS SHOK].
remember (Eimg (Ereg regsc (gs_extra (LINE + idx) Bv (LEN + j)))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (E2 : ew E 2 = getr regsc 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsc _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regsc 3) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsc _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regsc 4) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsc _ 4 4%bv eq_refl)).
assert (E10 : ew E 10 = w64 j) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsc _ 10 10%bv eq_refl); exact C10).
assert (E11 : ew E 11 = w64 32) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsc _ 11 11%bv eq_refl); exact C11).
assert (E12 : ew E 12 = w64 (LINE + LEN)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsc _ 12 12%bv eq_refl); exact C12).
assert (E13 : ew E 13 = w64 (LINE + LEN - 1)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsc _ 13 13%bv eq_refl); exact C13).
assert (E18 : ew E 18 = w64 LEN) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsc _ 18 18%bv eq_refl); exact Cs2).
assert (E19 : ew E 19 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsc _ 19 19%bv eq_refl); exact Cs3).
assert (E32 : ew E 32 = Z_to_bv 64 (LINE + idx)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsc _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 Bv) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsc _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (LEN + j)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsc _ 2)).
assert (HAE : env_agree 32 (Ereg regsc (gs_extra (LINE + idx) Bv (LEN + j))) E)
by (rewrite HE; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
clear HE.
assert (Usp : bv_unsigned (ew E 2) = spZ regsc) by (rewrite E2; reflexivity).
assert (HBxv : U E Bx = SHADOW_OFF)
by (unfold Bx; rewrite (U_atom E 19 SB E19 ltac:(unfold SB; lia)); reflexivity).
pose proof HJ as HARc. apply ajournal_gx_AR_xR in HARc.
paj_run_tok_xR RUNG HS HJ SHOK Bspan.
{ rewrite <- (aview_rd_of SEGS), HBxv, (U_atom E 32 (LINE + idx) E32 ltac:(lia)).
apply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly S hp W memc _ q k (LINE + idx) 1 HARc Hq); lia. }
{ apply awr_ok_x_of0. awr_ok_tac. }
(* stopped at 0x85c34 (beq a4, a1): the scanned byte is atom 33, a1 is still the 32 the caller loaded *)
assert (F33 : ew (ewset (ewset E 512 w) 513 w0) 33 = Z_to_bv 64 Bv) by (rewrite !ew_ewset_other by lia; exact E33).
assert (F11 : ew (ewset (ewset E 512 w) 513 w0) 11 = Z_to_bv 64 32) by (rewrite !ew_ewset_other by lia; exact E11).
assert (F34 : ew (ewset (ewset E 512 w) 513 w0) 34 = Z_to_bv 64 (LEN + j)) by (rewrite !ew_ewset_other by lia; exact E34).
assert (F10 : ew (ewset (ewset E 512 w) 513 w0) 10 = w64 j) by (rewrite !ew_ewset_other by lia; exact E10).
assert (HAE1 : env_agree 32 (Ereg regsc (gs_extra (LINE + idx) Bv (LEN + j))) (ewset (ewset E 512 w) 513 w0)).
{ split; [intros mm Hmm; rewrite !ew_ewset_other by lia; exact (proj1 HAE mm Hmm) | cbn [ewset ed]; exact (proj2 HAE)]. }
assert (Hidx_def : idx = LEN + j - 1) by reflexivity.
assert (HBv : nth (Z.to_nat idx) (bzs ln) 0 = Bv) by reflexivity.
clearbody idx Bv.
psrr_branch_tok RUNG BRR HS SHOK Bspan.
- (* line[len + j - 1] = ' ': on to the found point 0x85c58 *)
  rewrite branch_eq_U, (U_atom _ 33 Bv F33 ltac:(lia)), (U_atom _ 11 32 F11 ltac:(lia)) in Hc.
  apply Z.eqb_eq in Hc.
  paj_run_to_tok_xR RUNTOG HS HJ SHOK Bspan A_gm_found. { apply awr_ok_x_of0. awr_ok_tac. }
  assert (MEQ0 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) memc a)
  by gs_meq.
  assert (PRES0 : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms0) a).
  { intros a Hp. lazymatch goal with
    | K1 : mem_grows (mrestrict (w_H W) memc) (mrestrict (w_H W) (ms_mem ms)),
      K2 : mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms0)) |- _ =>
      exact (apresent_grows _ _ _ a K2 (apresent_grows _ _ _ a K1 (PRESc a Hp))) end. }
  pose proof (regs_kept_of_st_ok_pi _ _ _ regsc _
    [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 10%bv; 18%bv; 19%bv; 20%bv; 21%bv; 22%bv; 23%bv; 24%bv; 25%bv; 26%bv; 27%bv]
    HS HAE1 ltac:(vm_compute; reflexivity)) as HK.
  cbn [ms_regs restrict] in HK.
  subst LEN.
  pmkst HS.
  apply (GMFOUND_XR W ly S hp regs mem md ch HA LINE ln H q k idx (ms_regs ms0) (ms_mem ms0) _ HPRE Hr10 Hr11 Hr12 HL ND
    HinG HZS HA8 GL NZ LN Hq Hqb Hq1 Hq2 LG LB LE HROM HGROW HAREC HROOM MOK kr HRM HCNT HFK HSP).
  + unfold spZ. rewrite (HK 2%bv ltac:(gs_in)). exact Uspc.
  + rewrite (HK 3%bv ltac:(gs_in)). exact Cgp.
  + rewrite (HK 4%bv ltac:(gs_in)). exact Ctp.
  + rewrite (HK 8%bv ltac:(gs_in)). exact Cs0.
  + rewrite (HK 9%bv ltac:(gs_in)). exact Cs1.
  + rewrite (HK 18%bv ltac:(gs_in)). exact Cs2.
  + rewrite (HK 19%bv ltac:(gs_in)). exact Cs3.
  + intros r Hcs Hr. rewrite <- (CKEPT r Hcs Hr). apply HK. gs_cs r Hr.
  + apply (gs_vm W memc _ _ _ _ MEQ0); [gs_spr | gs_spr | exact VRA].
  + apply (gs_vm W memc _ _ _ _ MEQ0); [gs_spr | gs_spr | exact VS0].
  + apply (gs_vm W memc _ _ _ _ MEQ0); [gs_spr | gs_spr | exact VS1].
  + apply (gs_vm W memc _ _ _ _ MEQ0); [gs_spr | gs_spr | exact VS2].
  + apply (gs_vm W memc _ _ _ _ MEQ0); [gs_spr | gs_spr | exact VS3].
  + intros a Ha Hno. rewrite (MEQ0 a Ha). exact (KEEPc a Ha Hno).
  + exact PRES0.
  + exact HJ.
  + apply (GM.lsf (bzs ln) 0 (Z.to_nat idx)).
    * lia.
    * rewrite HBv, Hc. reflexivity.
    * intros kk Hkk. replace kk with (Z.to_nat (Z.of_nat kk)) by lia. apply HINV. lia.
  + lia.
  + rewrite (HK 10%bv ltac:(gs_in)), C10. unfold w64. f_equal. lia.
- (* not a space: one step back *)
  rewrite branch_eq_U, (U_atom _ 33 Bv F33 ltac:(lia)), (U_atom _ 11 32 F11 ltac:(lia)) in Hc.
  apply Z.eqb_neq in Hc.
  (* line[13] is the space, so a byte that is not one sits above it *)
  assert (Hidx14 : 14 <= idx).
  { destruct (Z.eq_dec idx 13) as [I13 | I13]; [|lia]. exfalso. apply Hc. rewrite <- HBv, I13. exact HSP. }
  paj_run_tok_xR RUNG HS HJ SHOK Bspan. { apply awr_ok_x_of0. awr_ok_tac. }
  psrr_branch_tok RUNG BRR HS SHOK Bspan.
  + (* len + j - 1 <> 0: back to the loop head 0x85c18 *)
    paj_run_to_tok_xR RUNTOG HS HJ SHOK Bspan A_gm_loop. { apply awr_ok_x_of0. awr_ok_tac. }
    assert (MEQ1 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W) (ms_mem ms1) a = aview SEGS (w_H W) memc a)
    by gs_meq.
    assert (PRES1 : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms1) a).
    { intros a Hp. lazymatch goal with
      | K1 : mem_grows (mrestrict (w_H W) memc) (mrestrict (w_H W) (ms_mem ms)),
        K2 : mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms0)),
        K3 : mem_grows (mrestrict (w_H W) (ms_mem ms0)) (mrestrict (w_H W) (ms_mem ms1)) |- _ =>
        exact (apresent_grows _ _ _ a K3 (apresent_grows _ _ _ a K2 (apresent_grows _ _ _ a K1 (PRESc a Hp)))) end. }
    pose proof (regs_kept_of_st_ok_pi _ _ _ regsc _
      [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 11%bv; 12%bv; 13%bv; 18%bv; 19%bv; 20%bv; 21%bv; 22%bv; 23%bv; 24%bv; 25%bv;
       26%bv; 27%bv] HS HAE1 ltac:(vm_compute; reflexivity)) as HK.
    cbn [ms_regs restrict] in HK.
    prreg HS (10%bv : bv 5) L10.
    subst LEN.
    pmkst HS.
    apply (IH W ly S hp regs mem md ch HA LINE ln H q k (j - 1) (ms_regs ms1) (ms_mem ms1) _ HPRE Hr10 Hr11 Hr12 HL ND
      HinG HZS HA8 GL NZ LN Hq Hqb Hq1 Hq2 LG LB LE HROM HGROW HAREC HROOM MOK kr HRM HCNT HFK HSP).
    * unfold spZ. rewrite (HK 2%bv ltac:(gs_in)). exact Uspc.
    * rewrite (HK 3%bv ltac:(gs_in)). exact Cgp.
    * rewrite (HK 4%bv ltac:(gs_in)). exact Ctp.
    * rewrite (HK 8%bv ltac:(gs_in)). exact Cs0.
    * rewrite (HK 9%bv ltac:(gs_in)). exact Cs1.
    * rewrite (HK 18%bv ltac:(gs_in)). exact Cs2.
    * rewrite (HK 19%bv ltac:(gs_in)). exact Cs3.
    * intros r Hcs Hr. rewrite <- (CKEPT r Hcs Hr). apply HK. gs_cs r Hr.
    * apply (gs_vm W memc _ _ _ _ MEQ1); [gs_spr | gs_spr | exact VRA].
    * apply (gs_vm W memc _ _ _ _ MEQ1); [gs_spr | gs_spr | exact VS0].
    * apply (gs_vm W memc _ _ _ _ MEQ1); [gs_spr | gs_spr | exact VS1].
    * apply (gs_vm W memc _ _ _ _ MEQ1); [gs_spr | gs_spr | exact VS2].
    * apply (gs_vm W memc _ _ _ _ MEQ1); [gs_spr | gs_spr | exact VS3].
    * intros a Ha Hno. rewrite (MEQ1 a Ha). exact (KEEPc a Ha Hno).
    * exact PRES1.
    * exact HJ.
    * rewrite L10, E10. unfold w64. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
      rewrite Zplus_mod_idemp_l. f_equal; lia.
    * rewrite (HK 11%bv ltac:(gs_in)). exact C11.
    * rewrite (HK 12%bv ltac:(gs_in)). exact C12.
    * rewrite (HK 13%bv ltac:(gs_in)). exact C13.
    * exact HLEN14.
    * lia.
    * lia.
    * intros t Ht. destruct (Z.eq_dec t idx) as [-> | Hne].
      -- rewrite HBv. unfold RelayModel.SPACE. exact Hc.
      -- apply HINV. lia.
    * lia.
  + (* len + j - 1 = 0 would put the scan below line[13]: not reached *)
    exfalso.
    rewrite branch_ne_U, (U_atom_off _ 34 (LEN + j) (-1) F34 ltac:(lia) ltac:(lia)), U_lit in Hc0 by lia.
    apply (proj1 (Bool.negb_false_iff _)) in Hc0. apply Z.eqb_eq in Hc0. lia.
Qed.
End wR.
(* the strict text is the R section's at R := wle: GMFOUND_XR at wle is GMFOUND_X *)
#[local] Ltac wle_inst := first [ eassumption | intros ? ? H; exact H | intros ?; apply wle_refl
  | intros ? ? ? H1 H2; eapply wle_trans; [exact H1 | exact H2] ].

Lemma pb_gm_scan_x : forall (fuel : nat) W ly S Hp regs mem md ch HA LINE (ln : list byte) H q k (j : Z) regsc memc mdc,
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
Proof. eapply (pb_gm_scan_xR (@wle SEGS)); wle_inst. Qed.

End c.

(* ---- THE AR STATEMENT, re-derived (route (b), step 3; CONVERSION.md (sha256 1015972e02a9; internal record) 3.-4.): gm_scan's statement is the AR walk's,
   unchanged, now a corollary of pb_gm_scan_x at ARx := ARi0, PST := [].  LX0 replaces LAWS; HP0 at ARi0 is
   ARi0_hp0; the old GMFOUND gives GMFOUND_X at ARi0 (its pre and journal at ARi0 are the AR ones by
   W_journal_x afn_pre_x_ARi0_to_AR / ajournal_gx_x_ARi0_AR, its post the generic one by W_contract_x
   gm_post_x_of_AR0); the entry, the journal and the post through afn_pre_x_ARi0_of_AR / ajournal_gx_AR_x_ARi0 /
   gm_post_x_AR0. ---- *)
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
Hypothesis GMFOUND : forall W ly S regs mem md ch HA LINE (ln : list byte) H q k (js : Z) regsc memc mdc,
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
ajournal_gx SEGS B G 0 [] GM_STK (spZ regs) (blk_FP (list_blks H)) ly S W mem md [] ly S W memc mdc 0 ->
RelayModel.last_space_from 0 (bzs ln) = Some (Z.to_nat js) ->
13 <= js < Z.of_nat (length ln) ->
getr regsc 10 = w64 (js + 1 - Z.of_nat (length ln)) ->
SRr SEGS W (mkCfg (mkst regsc (Z_to_bv 64 (BASE + A_gm_found)) memc (seg_rom SEGS)) mdc)
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
Lemma gm_scan : forall (fuel : nat) W ly S regs mem md ch HA LINE (ln : list byte) H q k (j : Z) regsc memc mdc,
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
ajournal_gx SEGS B G 0 [] GM_STK (spZ regs) (blk_FP (list_blks H)) ly S W mem md [] ly S W memc mdc 0 ->
getr regsc 10 = w64 j -> getr regsc 11 = w64 32 ->
getr regsc 12 = w64 (LINE + Z.of_nat (length ln)) ->
getr regsc 13 = w64 (LINE + Z.of_nat (length ln) - 1) ->
14 <= Z.of_nat (length ln) -> 13 < Z.of_nat (length ln) + j -> j <= 0 ->
(forall t, Z.of_nat (length ln) + j <= t < Z.of_nat (length ln) ->
 nth (Z.to_nat t) (bzs ln) 0 <> RelayModel.SPACE) ->
Z.of_nat fuel = Z.of_nat (length ln) + j - 13 ->
SRr SEGS W (mkCfg (mkst regsc (Z_to_bv 64 (BASE + A_gm_loop)) memc (seg_rom SEGS)) mdc)
(gm_post B MT G regs ly S W mem md HA H ln).
Proof.
intros fuel W ly S regs mem md ch HA LINE ln H q k j regsc memc mdc HPRE. intros.
pose proof (ARi0_hp0 SEGS B) as HP0.
pose proof (afn_pre_x_ARi0_of_AR SEGS B _ _ _ _ _ _ _ _ HPRE) as HPREx.
lazymatch goal with HJ : context [@W_journal.ajournal_gx] |- _ =>
  pose proof HJ as HJx; apply ajournal_gx_AR_x_ARi0 with (Hp := []) in HJx end.
eapply SRr_mono.
{ eapply (pb_gm_scan_x B MT RP_AR MMAX G [] (ARi0 SEGS B)) with (kr := 0%nat); try eassumption.
  all: first
    [ exact (rp_RM_AR _ _)
    | apply cnt_ok_pk_AR; unfold gm_pk; cbn; lia
    | intros W1 ly1 S1 Hp1; specialize (GMFOUND W1 ly1 S1); go1 GMFOUND;
      eapply SRr_mono; [exact GMFOUND | cbv beta; intros W2 c2 _ HQ; apply gm_post_x_of_AR0; exact HQ] ]. }
cbv beta. intros W2 c2 _ HQ. exact (gm_post_x_AR0 B MT G regs ly S [] W mem md HA H ln _ W2 c2 HQ).
Qed.
End r.
End b.
End a.

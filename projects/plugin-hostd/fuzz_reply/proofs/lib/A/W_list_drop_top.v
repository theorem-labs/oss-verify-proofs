(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the outer walk of fuzz_reply's list_drop on the ASan image (a Theorem Labs lane W1,
   step 4), in the form of lib/A/W_list_find.v pb_list_find (entry, cut, splice, epilogue, return).  The walk is
   ARx-generic at the caller-context free rule (pb_list_drop_cx_x, route (b), step 3; the template is
   lib/A/W_check_bounded.v); the strong-rule forms pb_list_drop_x / pb_list_drop_ro_x and the context-rule
   G-generic form pb_list_drop_ro_cx_x are corollaries of it, and the AR theorems pb_list_drop and pb_list_drop_ro
   are re-derived from them at ARx := ARi0, PST := []. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YI08 YO0c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YI00 YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require HarnessRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Mem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YN2e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_syms W_listing W_pl W_kit W_journal W_rep W_contract W_sites W_frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_kit_x W_journal_x W_contract_x W_sites_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_list_drop.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_contract_xR_g3.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PI).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).

(* record i's text pointer, an 8-byte cell of the vector (lib/A/W_list_find.v alist_rec_fields, its first half) *)
Lemma ld_rec_ptr : forall B ly S W mem LA l lines j,
alist_at B ly S W mem LA l lines -> (j < length (HarnessRep.hl_recs l))%nat ->
val_mem SEGS (arm W mem) (HarnessRep.hl_v l + 16 * Z.of_nat j) 8
  (fst (nth j (HarnessRep.hl_recs l) (0, [])) mod 2 ^ 64).
Proof.
intros B ly S W mem LA l lines j HA Hj.
destruct HA as (_ & _ & _ & _ & Hcap & Hv & _).
destruct Hv as [(Hc0 & _) | (_ & _ & _ & Hg)].
{ unfold HarnessRep.hl_n in Hcap. lia. }
destruct (nth_split (HarnessRep.hl_recs l) (0, []) Hj) as (l1 & l2 & Hsp & Hl1).
set (r := nth j (HarnessRep.hl_recs l) (0, [])) in *.
rewrite Hsp in Hg. rewrite map_app, concat_app in Hg. cbn [map concat] in Hg.
unfold HarnessRep.bzs in Hg. rewrite !map_app in Hg. rewrite <- !app_assoc in Hg.
apply garr8_app in Hg as [_ Hg]. rewrite length_map, text_recs_length, Hl1 in Hg.
unfold HarnessRep.text_rec, OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.le8 in Hg.
rewrite !map_app, <- !app_assoc in Hg.
apply garr8_app in Hg as [H1 _].
apply garr8_val_mem8 in H1.
rewrite Z_to_bv_unsigned in H1. unfold bv_wrap in H1. change (bv_modulus 64) with (2 ^ 64) in H1.
replace (HarnessRep.hl_v l + Z.of_nat (16 * j)) with (HarnessRep.hl_v l + 16 * Z.of_nat j) in H1 by lia.
exact H1.
Qed.
(* the shadow address of an 8-aligned object, as the machine computes it (W_list_find.v lf_srl3) *)
Lemma ld_srl3 : forall X, 0 <= X < 2 ^ 63 ->
alu64 ALU_SRL (Z_to_bv 64 X) (Z_to_bv 64 3) = Z_to_bv 64 (X / 8).
Proof.
intros X HX.
assert (HD : 0 <= X / 8 < 2 ^ 63) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
apply bv_eq. rewrite alu64_unsigned. cbn [zalu_raw].
rewrite (unsigned_lit_small X) by lia. rewrite (unsigned_lit_small 3) by lia.
rewrite (unsigned_lit_small (X / 8)) by lia.
change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
first [ unfold bv_wrap; change (bv_modulus 64) with (2 ^ 64) | unfold zcanon, M64 ].
apply Z.mod_small. lia.
Qed.
(* the records list_drop leaves: each one of the list before, none of them record i *)
Lemma ld_recs_drop : forall (recs : list (Z * list byte)) i r, (i < length recs)%nat -> List.NoDup (map fst recs) ->
In r (firstn i recs ++ skipn (S i) recs) -> In r recs /\ fst r <> fst (nth i recs (0, [])).
Proof.
intros recs i r Hi ND Hr.
destruct (nth_split recs (0, []) Hi) as (A & Bs & Hsp & HlA).
set (ri := nth i recs (0, [])) in *. clearbody ri. subst recs i.
rewrite drop_split in Hr. rewrite map_app in ND. cbn [map] in ND.
split.
- apply in_app_or in Hr as [Hx|Hx]; apply in_or_app; [left; exact Hx | right; right; exact Hx].
- intros E. apply (NoDup_remove_2 _ _ _ ND). rewrite <- E, <- map_app. apply in_map. exact Hr.
Qed.
(* two values that agree byte for byte at a read the same through the ASan view *)
Lemma ld_aview_agree : forall (W W' : world SEGS) m m' a (n : nat) x k,
val_mem SEGS (arm W m) a n x -> val_mem SEGS (arm W' m') a n x -> 0 <= k < Z.of_nat n ->
aview SEGS (w_H W') m' (a + k) = aview SEGS (w_H W) m (a + k).
Proof.
intros W W' m m' a n x k H1 H2 Hk. unfold aview. cbv beta. f_equal.
exact (val_mem_agree SEGS _ _ a n x H1 H2 k Hk).
Qed.

(* ---- THE GENERIC WALK (route (b), step 3): W_list_drop.v Section d's hypotheses, over any allocator relation ARx
   with its laws and HP0, the callee contracts' generic twins at the same PST / ARx, the journal ajournal_gx_x at
   the walk's own G, XO = 0, OUT = [].  The free rule is the CALLER-CONTEXT form (afree_cf_rule_c_x at a table CTX
   holding list_drop's free context [BASE + AF_fr_list_drop + 0x60], 0x85874), so an instance that has only the
   context form (top_x's AFREE_x at K0's CTX_AFREE) takes this walk; Section d below derives the strong-rule form.
   ---- *)
Section dc.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
Hypothesis HP0 : forall ly S Hp W mem md, ARx ly S Hp W mem md -> Hp = [].
Variable MT : ameter_ops.
(* the room round (ROOM-TEXTS.md v3 sha256 767baa12f13c; internal record): ldrop_spec_x's room record; list_drop only frees, so its peak is 0 *)
Variable RP : roomp.
Variable CTX : list (list Z).
Hypothesis HCTX : In [BASE + AF_fr_list_drop + 0x60] CTX.
Variable G : list (Z * Z).
Hypothesis HG : gx_ok SEGS B G.
Hypothesis GRT : gx_rt B G.
Hypothesis TL : PALib B.
Hypothesis AFREE : afree_cf_rule_c_x SEGS B PST ARx MT RP CTX.
Hypothesis AMOVE : amemmove_realizes_x B ARx (SIGMA WS_asan_memmove).
(* rom_view has to cross the free call (W_list_drop.v's ROMS, the same text: acall_kept keeps an image byte outside
   the allocator's statics and errno, and the statics' read-only bytes are the relation's pinned const cells). *)
Hypothesis ROMS : forall a, in_rom SEGS a ->
(Exists (in_zr a) (as_owned_static B) -> rom_pinned SEGS B a) /\ ~ (as_errno B <= a < as_errno B + 4) /\ ~ inG G a.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.
Let RUN := paj_run_x_x B PST ARx LAWS G HG 0 [].
Let RUNTO := paj_run_to_x_x B PST ARx LAWS G HG 0 [].
Let RET := paj_ret_at (PL := PL_fr) (PI := PI).
(* W_list_drop's lemmas are taken after its Section d closed: give each the Section's own variables and
   hypotheses, whichever of them its closed form takes.  PST and G have one type: PST is the list binder that the
   relation's binder follows (W_list_drop.v declares ARx right after PST, and G after both); hl is the Z binder that
   the laws' binder follows. *)
Ltac ld_inst H := repeat match type of H with
| forall _ : asyms, _ => specialize (H B)
| forall (_ : list (Z * Z)) (_ : alayout -> astate -> list Z -> world _ -> (word -> option byte) -> Model -> Prop), _ =>
  specialize (H PST)
| forall _ : alayout -> astate -> list Z -> world _ -> (word -> option byte) -> Model -> Prop, _ => specialize (H ARx)
| forall (_ : Z) (_ : AR_laws_x _ _ _ _), _ => specialize (H hl)
| forall _ : ameter_ops, _ => specialize (H MT)
| forall _ : roomp, _ => specialize (H RP)
| forall _ : list (list Z), _ => specialize (H CTX)
| forall _ : list (Z * Z), _ => specialize (H G)
| In (_ :: nil) _ -> _ => specialize (H HCTX)
| AR_laws_x _ _ _ _ -> _ => specialize (H LAWS)
| (forall _ : alayout, _) -> _ => specialize (H HP0)
| gx_ok _ _ _ -> _ => specialize (H HG)
| gx_rt _ _ -> _ => specialize (H GRT)
| PALib _ -> _ => specialize (H TL)
| afree_cf_rule_c_x _ _ _ _ _ _ _ -> _ => specialize (H AFREE)
| amemmove_realizes_x _ _ _ -> _ => specialize (H AMOVE)
| (forall a, in_rom _ a -> _) -> _ => specialize (H ROMS)
end.
(* two live blocks at different addresses share no byte (ARx_blocks_law's pairwise disjointness) *)
Lemma ld_blk_disj_x : forall ly S Hp W mem md p1 n1 p2 n2 a,
ARx ly S Hp W mem md -> In (p1, n1) (ablocks B ly S) -> In (p2, n2) (ablocks B ly S) -> p1 <> p2 ->
p1 <= a < p1 + req_size n1 -> ~ (p2 <= a < p2 + req_size n2).
Proof.
intros ly S Hp W mem md p1 n1 p2 n2 a HAR H1 H2 Hne Ha Hb.
destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md p1 n1 HAR H1) as (_ & _ & _ & _ & _ & Hpw).
pose proof (in_map (fun b : Z * Z => (fst b, req_size (snd b))) _ _ H1) as Hx. cbn [fst snd] in Hx.
pose proof (in_map (fun b : Z * Z => (fst b, req_size (snd b))) _ _ H2) as Hy. cbn [fst snd] in Hy.
assert (Hne2 : (p1, req_size n1) <> (p2, req_size n2)) by (intros E; injection E as E _; exact (Hne E)).
pose proof (pairwise_zdisjoint_split _ _ _ Hpw (in_split_2 _ _ _ Hx Hy Hne2)) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
Qed.

Ltac ldl := unfold LDROP_STK, LDROP_FRAME, ASTACK, AREC in *; lia.
Ltac ldz := cbn [Z.of_N N.to_nat Pos.to_nat Z.mul Pos.mul Pos.iter_op Nat.add Nat.mul]; ldl.

(* list_drop(l, i) at 0x85814: the prologue to 0x8585c, the body (ld_bodyX_x: the free, the memmove, the store of
   n - 1) to 0x858c0, the epilogue and the return; then the list at LA is ldrop_list l i (alist_at_drop). *)
Theorem pb_list_drop_cx_x : ldrop_spec_x B PST ARx MT RP G A_list_dropP.
Proof.
intros W ly S Hp regs mem md ch LA l lines i HPRE H10 H11 HL Hi HLA8 HLA4 Hcap32 HZS HLGx HVoff Hmo kr HRM HCNT Hrom.
destruct l as [v cap recs junk].
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof HG as HGok.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HLG : forall a, LA <= a < LA + 16 -> inG G a) by (intros a Ha; exact (proj1 (HLGx a Ha))).
pose proof ld_entry_x as LE. ld_inst LE. pose proof ld_LA_range as LR. ld_inst LR.
pose proof (LR LA HLG) as HLAR. clear LR.
destruct (LE W ly S Hp regs mem md ch LA (HarnessRep.HL v cap recs junk) lines i HPRE H10 H11 HL Hi HLA8 HZS HLG)
  as [HS SHOK].
clear LE.
(* the list before the call *)
pose proof HL as (M1 & M2 & M3 & Mawr & (Hn0 & Hcap) & Hvb & HND & Hvni & HRF).
unfold HarnessRep.hl_n in M2, Hn0, Hvb, Hcap32.
cbn [HarnessRep.hl_v HarnessRep.hl_cap HarnessRep.hl_recs HarnessRep.hl_junk]
  in M1, M2, M3, Mawr, Hn0, Hcap, Hvb, HND, Hvni, HRF, Hi, Hcap32.
assert (HiZ : 0 <= Z.of_nat i < Z.of_nat (length recs)) by lia.
destruct Hvb as [(Hc0 & _) | (Hcpos & Hvin & _ & _)]; [lia|].
destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md _ _ HAR Hvin) as (Hv16 & Hv4096 & Hvceil & _ & _ & _).
assert (Hvreq : req_size (AREC * cap) = AREC * cap)
by (unfold req_size; destruct (Z.eqb_spec (AREC * cap) 0); unfold AREC in *; lia).
rewrite Hvreq in Hvceil.
pose proof (proj1 (Forall_forall _ _) HRF _ (nth_In _ (0, []) Hi)) as (Hsin & _ & _ & _).
destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md _ _ HAR Hsin) as (_ & Hs4096 & Hsceil & _ & _ & _).
assert (Hsreq : req_size (Z.of_nat (length (snd (nth i recs (0, [])))) + 1) =
  Z.of_nat (length (snd (nth i recs (0, [])))) + 1)
by (unfold req_size; destruct (Z.eqb_spec (Z.of_nat (length (snd (nth i recs (0, [])))) + 1) 0); lia).
rewrite Hsreq in Hsceil.
assert (Hs64 : 0 <= fst (nth i recs (0, [])) < 2 ^ 64) by lia.
assert (Hlen0 : 0 <= Z.of_nat (length (snd (nth i recs (0, []))))) by lia.
assert (Hvne : v <> fst (nth i recs (0, []))).
{ intros Ev. apply Hvni. rewrite Ev. apply in_map. apply nth_In. exact Hi. }
assert (HSLO : alloc_ceiling + 16384 <= spZ regs - 48) by ldl.
(* the journal: the vector and record i's text are the bytes the body may write or free *)
set (FP := [(v, v + AREC * cap); (fst (nth i recs (0, [])),
  fst (nth i recs (0, [])) + req_size (Z.of_nat (length (snd (nth i recs (0, [])))) + 1))]).
pose proof (ajournal_gx_init_x SEGS B PST ARx G 0 [] LDROP_STK FP ly S Hp W regs mem md ch HPRE ltac:(lia) eq_refl
  ltac:(lia) ltac:(intros a Ha; lia)) as HJ.
remember (Eimg (Ereg regs (ld_extra (HarnessRep.HL v cap recs junk)))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs (ld_extra (HarnessRep.HL v cap recs junk))) E)
by (rewrite HE; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EE : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs rr)
by (intros m rr Hm; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hm).
assert (E1 : ew E 1 = getr regs 1) by exact (EE 1%nat 1%bv eq_refl).
assert (E2 : ew E 2 = getr regs 2) by exact (EE 2%nat 2%bv eq_refl).
assert (E3 : ew E 3 = w64 (as_gp B)) by (rewrite (EE 3%nat 3%bv eq_refl); exact Hgp).
assert (E4 : ew E 4 = w64 (as_tp B)) by (rewrite (EE 4%nat 4%bv eq_refl); exact Htp).
assert (E10 : ew E 10 = Z_to_bv 64 LA) by (rewrite (EE 10%nat 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 (Z.of_nat i)) by (rewrite (EE 11%nat 11%bv eq_refl); exact H11).
assert (E32 : ew E 32 = Z_to_bv 64 v)
by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (Z.of_nat (length recs)))
by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 cap)
by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 SB)
by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
clear HE EE.
assert (BV10 : base_val E (Some 10%nat) = LA)
by (cbn [base_val]; rewrite E10; apply unsigned_lit_small; lia).
unfold cfg_at. change (w64 A_list_dropP) with (Z_to_bv 64 A_list_dropP).
unfold A_list_dropP, A_list_drop.
(* ---- the prologue, 0x85814 .. 0x8585c ---- *)
paj_run_to_tok_x RUNTO HS HJ SHOK ld_Bspan A_ld_body.
{ lazymatch goal with |- awr_ok_x ?E ?rs ?G ?XO ?OUT ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok_x E rs' G XO OUT stk sp0 fp b0 bc ly own) end.
  apply awr_ok_x_cons_awr0; [awr_ok_tac; try exact Usp|].
  apply awr_ok_x_cons_awr0; [awr_ok_tac|].
  apply awr_ok_x_cons_awr0; [awr_ok_tac|].
  apply awr_ok_x_cons_g; [|apply awr_ok_x_nil].
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi]. rewrite BV10. intros a Ha. apply HLG. lia. }
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3.
prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9.
prreg HS (10%bv : bv 5) Q10. prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19.
(* the registers at the body's entry *)
assert (Ub : spZ (ms_regs ms) = spZ regs - LDROP_FRAME).
{ unfold spZ at 1. rewrite Q2, Usp. rewrite unsigned_lit_small by ldl. unfold LDROP_FRAME. lia. }
assert (R1 : getr (ms_regs ms) 1 = getr regs 1) by (rewrite Q1; exact E1).
assert (R3 : getr (ms_regs ms) 3 = w64 (as_gp B)) by (rewrite Q3; exact E3).
assert (R4 : getr (ms_regs ms) 4 = w64 (as_tp B)) by (rewrite Q4; exact E4).
assert (R8 : getr (ms_regs ms) 8 = w64 (Z.of_nat i)) by (rewrite Q8; exact E11).
assert (R9 : getr (ms_regs ms) 9 = w64 LA) by (rewrite Q9; exact E10).
assert (R10 : getr (ms_regs ms) 10 = w64 (v + AREC * Z.of_nat i)).
{ rewrite Q10, E11, E32, ld_addr_eq by ldl. unfold w64, AREC. f_equal; lia. }
assert (R18 : getr (ms_regs ms) 18 = w64 (SB + LA / 8)).
{ rewrite Q18, E10, E35, ld_srl3 by lia. rewrite YI08.alu64_add_lit. unfold w64. f_equal. lia. }
assert (R19 : getr (ms_regs ms) 19 = w64 SB) by (rewrite Q19; exact E35).
(* the prologue wrote only its frame and (in the region's window, but not in fact) the list head *)
assert (HNS : forall a, a < alloc_ceiling -> ~ (spZ regs - LDROP_FRAME <= a < spZ regs)) by (intros a Ha Hc; ldl).
assert (KEEP0 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - LDROP_FRAME <= a < spZ regs) -> ~ (LA <= a < LA + 16) ->
  aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem a).
{ intros a Ha Hs Hl. apply (aview_kept_out E _ (w_H W) mem (ms_mem ms) HFr a Ha).
  intros (r & Hin & Hr). cbn [ss_mem ss_ld ld_regions In] in Hin.
  destruct Hin as [<- | [<- | [<- | [<- | []]]]];
  unfold stack_region, got_regionP, bcell_regionP, ld_lreg in Hr;
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr.
  - rewrite Usp in Hr. unfold LDROP_FRAME in *. lia.
  - lia.
  - lia.
  - rewrite E10, unsigned_lit_small in Hr by lia. lia. }
assert (HBK : forall p m a, In (p, m) (ablocks B ly S) -> p <= a < p + req_size m ->
  aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem a).
{ intros p m a Hin Hr. destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md _ _ HAR Hin) as (_ & Hp4 & Hpc & _).
  apply KEEP0; [lia | apply HNS; lia |].
  intros Hl. apply (blk_img_x SEGS B ARx LAWS ly S Hp W mem md p m a HAR Hin Hr). exact (proj1 (HG a (HLG a Hl))). }
(* the list head at the body's entry, read off the list region *)
pose proof (st_ok_mem_ok SEGS _ _ _ HS) as (_ & Hrok & _).
pose proof (proj1 (Forall_forall _ _) Hrok (ld_lreg 10)
  ltac:(cbn [ss_mem]; right; right; right; left; reflexivity)) as (_ & _ & HLw & HLch).
cbn [ld_lreg YP09.r_base YP09.r_wlo YP09.r_whi YP09.r_chunks ms_mem restrict] in HLw, HLch.
rewrite BV10 in HLw, HLch.
assert (MvC : val_mem SEGS (arm W (ms_mem ms)) LA 8 v).
{ pose proof (proj1 (Forall_forall _ _) HLch _ ltac:(left; reflexivity)) as Hc.
  pose proof (val_of_chunk_ok SEGS E _ LA _ _ _ v Hc) as V. rewrite Z.add_0_r in V. apply V.
  - cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  - ldz.
  - ldz. }
assert (MnC : val_mem SEGS (arm W (ms_mem ms)) (LA + 8) 4 (Z.of_nat (length recs))).
{ pose proof (proj1 (Forall_forall _ _) HLch _ ltac:(right; left; reflexivity)) as Hc.
  pose proof (val_of_chunk_ok SEGS E _ LA _ _ _ (Z.of_nat (length recs)) Hc) as V. apply V.
  - cbn [sv_denot]. rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  - ldz.
  - ldz. }
assert (McC : val_mem SEGS (arm W (ms_mem ms)) (LA + 12) 4 cap).
{ pose proof (proj1 (Forall_forall _ _) HLch _ ltac:(right; right; left; reflexivity)) as Hc.
  pose proof (val_of_chunk_ok SEGS E _ LA _ _ _ cap Hc) as V. apply V.
  - cbn [sv_denot]. rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  - ldz.
  - ldz. }
assert (MawrC : awr W (ms_mem ms) LA 16) by (intros j Hj; exact (HLw j Hj)).
assert (KLA : forall a, LA <= a < LA + 8 \/ LA + 12 <= a < LA + 16 ->
  aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem a).
{ intros a [Ha|Ha].
  - replace a with (LA + (a - LA)) by lia.
    apply (ld_aview_agree W W mem (ms_mem ms) LA 8 v); [exact M1 | exact MvC | simpl Z.of_nat; lia].
  - replace a with ((LA + 12) + (a - (LA + 12))) by lia.
    apply (ld_aview_agree W W mem (ms_mem ms) (LA + 12) 4 cap); [exact M3 | exact McC | simpl Z.of_nat; lia]. }
(* record i's text pointer, a vector byte the prologue kept *)
pose proof (ld_rec_ptr B ly S W mem LA (HarnessRep.HL v cap recs junk) lines i HL Hi) as Ms0.
cbn [HarnessRep.hl_v HarnessRep.hl_recs] in Ms0. rewrite Z.mod_small in Ms0 by lia.
assert (MsC : val_mem SEGS (arm W (ms_mem ms)) (v + AREC * Z.of_nat i) 8 (fst (nth i recs (0, [])))).
{ unfold AREC. apply (val_mem_kept SEGS (w_H W) (w_H W) mem (ms_mem ms)); [|exact Ms0].
  intros k Hk. simpl Z.of_nat in Hk. apply (HBK v (AREC * cap)); [exact Hvin | rewrite Hvreq; ldl]. }
(* the ROM view: no ROM byte is in the frame or in G *)
assert (HromC : rom_view SEGS W (ms_mem ms)).
{ intros a Hin. destruct (ROMS a Hin) as (_ & _ & HnG).
  assert (Himg : in_img SEGS a) by (destruct Hin as (sg & Hsg & _ & Hr); exists sg; split; [exact Hsg | exact Hr]).
  pose proof (pa_img_range a Himg) as Har.
  rewrite (KEEP0 a ltac:(lia) ltac:(apply HNS; lia) ltac:(intros Hl; exact (HnG (HLG a Hl)))).
  exact (Hrom a Hin). }
assert (FPs : In (fst (nth i recs (0, [])), Z.of_nat (length (snd (nth i recs (0, [])))) + 1) (ablocks B ly S) ->
  forall j, 0 <= j < req_size (Z.of_nat (length (snd (nth i recs (0, [])))) + 1) ->
  inFP FP (fst (nth i recs (0, [])) + j)).
{ intros _ j Hj. exists (fst (nth i recs (0, [])),
    fst (nth i recs (0, [])) + req_size (Z.of_nat (length (snd (nth i recs (0, [])))) + 1)).
  split; [right; left; reflexivity | cbn [fst snd]; lia]. }
assert (FPv : forall a, v <= a < v + AREC * cap -> inFP FP a).
{ intros a Ha. exists (v, v + AREC * cap). split; [left; reflexivity | cbn [fst snd]; lia]. }
(* ---- the body, 0x8585c .. 0x858c0 (W1's ld_bodyX_x) ---- *)
pose proof ld_bodyX_x as LB. ld_inst LB.
eapply SRr_bind.
{ exact (LB W (ms_regs ms) (ms_mem ms) _ (spZ regs) FP ly S Hp W mem md [] ly S Hp 0 LA v (Z.of_nat (length recs)) cap i
    (fst (nth i recs (0, []))) (Z.of_nat (length (snd (nth i recs (0, []))))) (getr regs 1) kr
    HJ Ub R1 Hra Hra4 R3 R4 R8 R9 R10 R18 R19 HiZ (conj Hn0 Hcap) HLA8 HLG HZS MvC MnC McC MawrC MsC Hs64
    Hvin Hsin Hlen0 Hvne FPs FPv Hcap32 Hmo
    (* the free's room premise: MT_rk charges 1 for a free (W_contract_x.v:258), so Z.to_nat (mo_free MT_rk) + kr
       is 1 + kr by conversion; its count premise is the spec's, cnt_ok being cnt_ok_pk at peak 0 *)
    HRM HCNT HromC). }
cbv beta. intros W' c' Hwle' (ly' & S' & Hp' & regs' & mem' & md' & -> & HJ' & HCL & Hbl & Hfrs & Hmole & HRM' & HKhi &
  HKimg & HKblk & Hmv & Hn' & Hawr' & Hapr & Herrb).
clear LB.
pose proof HJ as HARb. apply ajournal_gx_AR_x in HARb.
pose proof HJ' as HAR'. apply ajournal_gx_AR_x in HAR'.
pose proof HJ' as (_ & _ & (memS' & HJi' & _) & _). rewrite !Z.add_0_r in HJi'.
pose proof HJi' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPR' & _).
destruct (alx_const _ _ _ LAWS _ _ _ _ _ _ HARb) as (Kc1 & _ & Kg1 & _).
destruct (alx_const _ _ _ LAWS _ _ _ _ _ _ HAR') as (Kc2 & _ & Kg2 & _).
rewrite HBgot, HBcell in Kg1, Kg2. rewrite HBcell in Kc1, Kc2.
pose proof (val_mem_of_rdword SEGS _ _ _ _ Kg1) as VG1. pose proof (val_mem_of_rdword SEGS _ _ _ _ Kg2) as VG2.
pose proof (val_mem_of_rdword SEGS _ _ _ _ Kc1) as VC1. pose proof (val_mem_of_rdword SEGS _ _ _ _ Kc2) as VC2.
(* back at 0x858c0: splice the body's result, dropping the list region (the body changed l->n); s2 is not
   kept by the body (it holds &l->n across the memmove), so it is havocked too, and the epilogue reloads it *)
jafter_stretch_keep_hi HS 36%nat regs' (mrestrict (w_H W') mem') (18%bv :: CLOB) A_ld_epi [0;1;2]%nat HS2.
match type of HS2 with ?P1 -> ?Q1 -> _ =>
assert (HP : P1); [|assert (HQ : Q1); [|specialize (HS2 HP HQ); clear HP HQ]] end.
{ intros r0 Hr0. cbn [ms_regs restrict]. exact (HCL r0 Hr0). }
{ cbn [ms_mem restrict].
  apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
  - split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Usp.
    + intros a Ha. apply (mbyte_of_aview SEGS). apply HKhi; [ldl | rewrite Ub; ldl].
    + intros a Ha _. apply (apresent_writable SEGS). apply HPR'. ldl.
  - exact (region_kept_val_at E _ _ (A_OBJ 0) (VAL (A_OBJ 0)) 8 (VAL (A_OBJ 32)) 0 0 _
      (HEI (A_OBJ 0) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) VG1 VG2 ltac:(lia)).
  - exact (region_kept_val_at E _ _ (A_OBJ 32) (VAL (A_OBJ 32)) 8 SHADOW_OFF 0 0 _
      (HEI (A_OBJ 32) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) VC1 VC2 ltac:(lia)). }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 36 (map (getr regs') (18%bv :: CLOB))) as Ea eqn:HEa in HS.
assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDa : forall m0, (m0 < 36)%nat -> ew Ea m0 = ew E m0)
by (intros m0 Hm0; rewrite HEa; apply YN3v.ew_havoc_old; exact Hm0).
assert (HAEa : env_agree 32 (Ereg regs (ld_extra (HarnessRep.HL v cap recs junk))) Ea)
by (rewrite HEa; apply env_agree_havoc_ge; [cbv; lia | exact HAE]).
clear HEa.
assert (Uspa : bv_unsigned (ew Ea 2) = spZ regs) by (rewrite OLDa by (cbv; lia); exact Usp).
assert (SHOK2 : sh_ok SEGS ld_Bx [] Ea (mrestrict (w_H W') mem')) by constructor.
(* ---- the epilogue, 0x858c0 .. the ret ---- *)
paj_run_tok_x RUN HS HJ' SHOK2 ld_Bspan.
{ lazymatch goal with |- awr_ok_x ?E ?rs ?G ?XO ?OUT ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok_x E rs' G XO OUT stk sp0 fp b0 bc ly own) end.
  apply awr_ok_x_cons_awr0; [awr_ok_tac; try exact Uspa|].
  apply awr_ok_x_cons_awr0; [awr_ok_tac|].
  apply awr_ok_x_cons_awr0; [awr_ok_tac|].
  apply awr_ok_x_nil. }
(* the epilogue wrote only the frame *)
assert (KEEP3 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - LDROP_FRAME <= a < spZ regs) ->
  aview SEGS (w_H W') (ms_mem ms0) a = aview SEGS (w_H W') mem' a).
{ intros a Ha Hno.
  lazymatch type of HFr0 with frame_of ?Ev ?rs _ _ =>
    apply (aview_kept_out Ev rs (w_H W') mem' (ms_mem ms0) HFr0 a Ha) end.
  intros (r & Hin & Hr). vm_compute in Hin.
  repeat (destruct Hin as [<- | Hin];
    [cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?Uspa in Hr;
     unfold LDROP_FRAME in Hno; lia |]).
  destruct Hin. }
prreg HS (1%bv : bv 5) R1f.
eapply (RET W' _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. unfold ldrop_post_x. cbv beta.
exists ly', S', Hp'.
lazymatch goal with |- exists _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ => exists r, m, d end.
split; [cbn [ms_regs]; rewrite R1f; rewrite OLDa by (cbv; lia); rewrite E1, Hra; reflexivity|].
split; [apply (ajournal_gx_materialize_x SEGS B PST ARx LAWS Hsegs); exact HJ'|].
split.
{ lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
  eapply (aregs_preserved_of_st_ok SEGS _ Ev _ _ regs (ld_extra (HarnessRep.HL v cap recs junk)) HS);
  [exact HAEa | vm_compute; reflexivity] end. }
split.
{ intros a Hia Hoa Hea Hpa. apply (apresent_grows (w_H W') mem' (ms_mem ms0) a HG1).
  apply (Hapr a Hia Hoa Hea). apply (apresent_grows (w_H W) mem (ms_mem ms) a HG0). exact Hpa. }
split.
{ (* errno's view: errno is an image byte (pal_env) off the frame and off the list head (gx_rt); the prologue and
     the epilogue wrote neither, and the body kept its view (ldb_post_x) *)
  intros j Hj. pose proof (pal_env B TL) as (_ & HeImg & _).
  assert (HeI : in_img SEGS (as_errno B + j)) by (apply HeImg; lia).
  pose proof (pa_img_range _ HeI) as HeR.
  assert (HeL : ~ (LA <= as_errno B + j < LA + 16)) by (intros Hc; exact (proj1 (GRT _ (HLG _ Hc)) ltac:(lia))).
  rewrite KEEP3 by (first [apply HNS; lia | lia]).
  rewrite (Herrb j Hj).
  exact (KEEP0 (as_errno B + j) ltac:(lia) ltac:(apply HNS; lia) HeL). }
split.
{ (* the representation half: the list at LA after the call is ldrop_list l i *)
  pose proof alist_at_drop as AD. ld_inst AD.
  apply (AD ly S W mem ly' S' W' (ms_mem ms0) LA (HarnessRep.HL v cap recs junk) lines i HL Hi);
  cbn [HarnessRep.hl_v HarnessRep.hl_cap HarnessRep.hl_recs HarnessRep.hl_junk]; unfold HarnessRep.hl_n;
  cbn [HarnessRep.hl_recs].
  - exact Hbl.
  - (* the head but its count: an image byte of G, kept by the body and by the epilogue *)
    intros a Ha. assert (HaG : LA <= a < LA + 16) by lia.
    rewrite KEEP3 by ldl.
    rewrite (HKimg a (proj1 (HG a (HLG a HaG))) (proj1 (proj2 (HG a (HLG a HaG)))) (proj1 (GRT a (HLG a HaG))) ltac:(lia)).
    exact (KLA a Ha).
  - apply (awr_kept_w W' W' mem' (ms_mem ms0) LA 16);
    [intros x _ Hpa; exact (apresent_grows _ _ _ x HG1 Hpa) | apply wle_refl | exact Hawr'].
  - apply (val_mem_kept SEGS (w_H W') (w_H W') mem' (ms_mem ms0)); [|exact Hn'].
    intros k Hk. simpl Z.of_nat in Hk. apply KEEP3; ldl.
  - (* the records above i, one record lower *)
    intros k Hk. rewrite KEEP3 by ldl. rewrite (Hmv k Hk).
    apply (HBK v (AREC * cap)); [exact Hvin | rewrite Hvreq; ldl].
  - (* the rest of the vector *)
    intros a Ha.
    assert (Hva : v <= a < v + req_size (AREC * cap)) by (rewrite Hvreq; ldl).
    rewrite KEEP3 by ldl.
    rewrite (HKblk v (AREC * cap) a Hvin Hva).
    + exact (HBK v (AREC * cap) a Hvin Hva).
    + exact (ld_blk_disj_x ly S Hp W mem md _ _ _ _ a HAR Hvin Hsin Hvne Hva).
    + ldl.
  - (* the texts of the other records *)
    intros r Hr a Ha.
    cbn [ldrop_list HarnessRep.hl_recs] in Hr.
    destruct (ld_recs_drop recs i r Hi ltac:(apply NoDup_ListNoDup; exact HND) Hr) as (HrIn & Hrne).
    pose proof (proj1 (Forall_forall _ _) HRF r HrIn) as (Hrin & _ & _ & _).
    destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md _ _ HAR Hrin) as (_ & Hr4096 & Hrceil & _ & _ & _).
    assert (Hrreq : req_size (Z.of_nat (length (snd r)) + 1) = Z.of_nat (length (snd r)) + 1)
    by (unfold req_size; destruct (Z.eqb_spec (Z.of_nat (length (snd r)) + 1) 0); lia).
    rewrite Hrreq in Hrceil.
    assert (Hra' : fst r <= a < fst r + req_size (Z.of_nat (length (snd r)) + 1)) by (rewrite Hrreq; lia).
    assert (Hrv : fst r <> v) by (intros Ev; apply Hvni; rewrite <- Ev; apply in_map; exact HrIn).
    rewrite KEEP3 by ldl.
    rewrite (HKblk _ _ a Hrin Hra').
    + exact (HBK _ _ a Hrin Hra').
    + exact (ld_blk_disj_x ly S Hp W mem md _ _ _ _ a HAR Hrin Hsin Hrne Hra').
    + intros Hm. apply (ld_blk_disj_x ly S Hp W mem md _ _ _ _ a HAR Hrin Hvin Hrv Hra'). rewrite Hvreq. ldl. }
split; [exact Hbl | split; [exact Hmole | exact HRM']].
Qed.
(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0): the walk at a world relation R, stated over a Theorem Labs lane's ldrop_spec_xR
   (W_contract_xR_g3.v; R right after ARx).  pb_list_drop_cx_xR is pb_list_drop_cx_x above with the journal init
   ajournal_gx_init_x -> ajournal_gx_init_xR (R_refl), ajournal_gx_AR_x / ajournal_gx_materialize_x -> their _xR
   twins, the runs -> paj_run_x_xG / paj_run_to_x_xG with paj_run_tok_xR / paj_run_to_tok_xR, the bind -> SRrG_bind SEGS
   R R_trans, the body -> W_list_drop.v's ld_bodyX_xR (its free at AFREE_R, with RO_ARx; its memmove at the
   strict AMOVE), the return -> the strict step lifted by SRr_SRrG (WLE_R), the post ldrop_post_x -> ldrop_post_xR.
   Every other token is the strict text's.  The free rule is the R caller-context form (W_journal_x.v
   afree_cf_rule_c_xR .. RO CTX R). ---- *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
Variable RO : (word -> option byte) -> Prop.
Hypothesis RO_ARx : forall ly S Hp (W : world SEGS) mem md, ARx ly S Hp W mem md -> RO mem.
Hypothesis AFREE_R : afree_cf_rule_c_xR SEGS B PST ARx MT RP RO CTX R.
Let RUNG := paj_run_x_xG B PST ARx LAWS R G HG 0 [].
Let RUNTOG := paj_run_to_x_xG B PST ARx LAWS R G HG 0 [].
(* :182 pb_list_drop_cx_x (line at 87fe4e86c75) *)
Theorem pb_list_drop_cx_xR : ldrop_spec_xR B PST ARx R MT RP G A_list_dropP.
Proof.
intros W ly S Hp regs mem md ch LA l lines i HPRE H10 H11 HL Hi HLA8 HLA4 Hcap32 HZS HLGx HVoff Hmo kr HRM HCNT Hrom.
destruct l as [v cap recs junk].
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof HG as HGok.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HLG : forall a, LA <= a < LA + 16 -> inG G a) by (intros a Ha; exact (proj1 (HLGx a Ha))).
pose proof ld_entry_x as LE. ld_inst LE. pose proof ld_LA_range as LR. ld_inst LR.
pose proof (LR LA HLG) as HLAR. clear LR.
destruct (LE W ly S Hp regs mem md ch LA (HarnessRep.HL v cap recs junk) lines i HPRE H10 H11 HL Hi HLA8 HZS HLG)
  as [HS SHOK].
clear LE.
(* the list before the call *)
pose proof HL as (M1 & M2 & M3 & Mawr & (Hn0 & Hcap) & Hvb & HND & Hvni & HRF).
unfold HarnessRep.hl_n in M2, Hn0, Hvb, Hcap32.
cbn [HarnessRep.hl_v HarnessRep.hl_cap HarnessRep.hl_recs HarnessRep.hl_junk]
  in M1, M2, M3, Mawr, Hn0, Hcap, Hvb, HND, Hvni, HRF, Hi, Hcap32.
assert (HiZ : 0 <= Z.of_nat i < Z.of_nat (length recs)) by lia.
destruct Hvb as [(Hc0 & _) | (Hcpos & Hvin & _ & _)]; [lia|].
destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md _ _ HAR Hvin) as (Hv16 & Hv4096 & Hvceil & _ & _ & _).
assert (Hvreq : req_size (AREC * cap) = AREC * cap)
by (unfold req_size; destruct (Z.eqb_spec (AREC * cap) 0); unfold AREC in *; lia).
rewrite Hvreq in Hvceil.
pose proof (proj1 (Forall_forall _ _) HRF _ (nth_In _ (0, []) Hi)) as (Hsin & _ & _ & _).
destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md _ _ HAR Hsin) as (_ & Hs4096 & Hsceil & _ & _ & _).
assert (Hsreq : req_size (Z.of_nat (length (snd (nth i recs (0, [])))) + 1) =
  Z.of_nat (length (snd (nth i recs (0, [])))) + 1)
by (unfold req_size; destruct (Z.eqb_spec (Z.of_nat (length (snd (nth i recs (0, [])))) + 1) 0); lia).
rewrite Hsreq in Hsceil.
assert (Hs64 : 0 <= fst (nth i recs (0, [])) < 2 ^ 64) by lia.
assert (Hlen0 : 0 <= Z.of_nat (length (snd (nth i recs (0, []))))) by lia.
assert (Hvne : v <> fst (nth i recs (0, []))).
{ intros Ev. apply Hvni. rewrite Ev. apply in_map. apply nth_In. exact Hi. }
assert (HSLO : alloc_ceiling + 16384 <= spZ regs - 48) by ldl.
(* the journal: the vector and record i's text are the bytes the body may write or free *)
set (FP := [(v, v + AREC * cap); (fst (nth i recs (0, [])),
  fst (nth i recs (0, [])) + req_size (Z.of_nat (length (snd (nth i recs (0, [])))) + 1))]).
pose proof (ajournal_gx_init_xR SEGS B PST ARx R_refl G 0 [] LDROP_STK FP ly S Hp W regs mem md ch HPRE ltac:(lia) eq_refl
  ltac:(lia) ltac:(intros a Ha; lia)) as HJ.
remember (Eimg (Ereg regs (ld_extra (HarnessRep.HL v cap recs junk)))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs (ld_extra (HarnessRep.HL v cap recs junk))) E)
by (rewrite HE; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EE : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs rr)
by (intros m rr Hm; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hm).
assert (E1 : ew E 1 = getr regs 1) by exact (EE 1%nat 1%bv eq_refl).
assert (E2 : ew E 2 = getr regs 2) by exact (EE 2%nat 2%bv eq_refl).
assert (E3 : ew E 3 = w64 (as_gp B)) by (rewrite (EE 3%nat 3%bv eq_refl); exact Hgp).
assert (E4 : ew E 4 = w64 (as_tp B)) by (rewrite (EE 4%nat 4%bv eq_refl); exact Htp).
assert (E10 : ew E 10 = Z_to_bv 64 LA) by (rewrite (EE 10%nat 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 (Z.of_nat i)) by (rewrite (EE 11%nat 11%bv eq_refl); exact H11).
assert (E32 : ew E 32 = Z_to_bv 64 v)
by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (Z.of_nat (length recs)))
by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 cap)
by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 SB)
by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
clear HE EE.
assert (BV10 : base_val E (Some 10%nat) = LA)
by (cbn [base_val]; rewrite E10; apply unsigned_lit_small; lia).
unfold cfg_at. change (w64 A_list_dropP) with (Z_to_bv 64 A_list_dropP).
unfold A_list_dropP, A_list_drop.
(* ---- the prologue, 0x85814 .. 0x8585c ---- *)
paj_run_to_tok_xR RUNTOG HS HJ SHOK ld_Bspan A_ld_body.
{ lazymatch goal with |- awr_ok_x ?E ?rs ?G ?XO ?OUT ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok_x E rs' G XO OUT stk sp0 fp b0 bc ly own) end.
  apply awr_ok_x_cons_awr0; [awr_ok_tac; try exact Usp|].
  apply awr_ok_x_cons_awr0; [awr_ok_tac|].
  apply awr_ok_x_cons_awr0; [awr_ok_tac|].
  apply awr_ok_x_cons_g; [|apply awr_ok_x_nil].
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi]. rewrite BV10. intros a Ha. apply HLG. lia. }
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3.
prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9.
prreg HS (10%bv : bv 5) Q10. prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19.
(* the registers at the body's entry *)
assert (Ub : spZ (ms_regs ms) = spZ regs - LDROP_FRAME).
{ unfold spZ at 1. rewrite Q2, Usp. rewrite unsigned_lit_small by ldl. unfold LDROP_FRAME. lia. }
assert (R1 : getr (ms_regs ms) 1 = getr regs 1) by (rewrite Q1; exact E1).
assert (R3 : getr (ms_regs ms) 3 = w64 (as_gp B)) by (rewrite Q3; exact E3).
assert (R4 : getr (ms_regs ms) 4 = w64 (as_tp B)) by (rewrite Q4; exact E4).
assert (R8 : getr (ms_regs ms) 8 = w64 (Z.of_nat i)) by (rewrite Q8; exact E11).
assert (R9 : getr (ms_regs ms) 9 = w64 LA) by (rewrite Q9; exact E10).
assert (R10 : getr (ms_regs ms) 10 = w64 (v + AREC * Z.of_nat i)).
{ rewrite Q10, E11, E32, ld_addr_eq by ldl. unfold w64, AREC. f_equal; lia. }
assert (R18 : getr (ms_regs ms) 18 = w64 (SB + LA / 8)).
{ rewrite Q18, E10, E35, ld_srl3 by lia. rewrite YI08.alu64_add_lit. unfold w64. f_equal. lia. }
assert (R19 : getr (ms_regs ms) 19 = w64 SB) by (rewrite Q19; exact E35).
(* the prologue wrote only its frame and (in the region's window, but not in fact) the list head *)
assert (HNS : forall a, a < alloc_ceiling -> ~ (spZ regs - LDROP_FRAME <= a < spZ regs)) by (intros a Ha Hc; ldl).
assert (KEEP0 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - LDROP_FRAME <= a < spZ regs) -> ~ (LA <= a < LA + 16) ->
  aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem a).
{ intros a Ha Hs Hl. apply (aview_kept_out E _ (w_H W) mem (ms_mem ms) HFr a Ha).
  intros (r & Hin & Hr). cbn [ss_mem ss_ld ld_regions In] in Hin.
  destruct Hin as [<- | [<- | [<- | [<- | []]]]];
  unfold stack_region, got_regionP, bcell_regionP, ld_lreg in Hr;
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr.
  - rewrite Usp in Hr. unfold LDROP_FRAME in *. lia.
  - lia.
  - lia.
  - rewrite E10, unsigned_lit_small in Hr by lia. lia. }
assert (HBK : forall p m a, In (p, m) (ablocks B ly S) -> p <= a < p + req_size m ->
  aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem a).
{ intros p m a Hin Hr. destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md _ _ HAR Hin) as (_ & Hp4 & Hpc & _).
  apply KEEP0; [lia | apply HNS; lia |].
  intros Hl. apply (blk_img_x SEGS B ARx LAWS ly S Hp W mem md p m a HAR Hin Hr). exact (proj1 (HG a (HLG a Hl))). }
(* the list head at the body's entry, read off the list region *)
pose proof (st_ok_mem_ok SEGS _ _ _ HS) as (_ & Hrok & _).
pose proof (proj1 (Forall_forall _ _) Hrok (ld_lreg 10)
  ltac:(cbn [ss_mem]; right; right; right; left; reflexivity)) as (_ & _ & HLw & HLch).
cbn [ld_lreg YP09.r_base YP09.r_wlo YP09.r_whi YP09.r_chunks ms_mem restrict] in HLw, HLch.
rewrite BV10 in HLw, HLch.
assert (MvC : val_mem SEGS (arm W (ms_mem ms)) LA 8 v).
{ pose proof (proj1 (Forall_forall _ _) HLch _ ltac:(left; reflexivity)) as Hc.
  pose proof (val_of_chunk_ok SEGS E _ LA _ _ _ v Hc) as V. rewrite Z.add_0_r in V. apply V.
  - cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  - ldz.
  - ldz. }
assert (MnC : val_mem SEGS (arm W (ms_mem ms)) (LA + 8) 4 (Z.of_nat (length recs))).
{ pose proof (proj1 (Forall_forall _ _) HLch _ ltac:(right; left; reflexivity)) as Hc.
  pose proof (val_of_chunk_ok SEGS E _ LA _ _ _ (Z.of_nat (length recs)) Hc) as V. apply V.
  - cbn [sv_denot]. rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  - ldz.
  - ldz. }
assert (McC : val_mem SEGS (arm W (ms_mem ms)) (LA + 12) 4 cap).
{ pose proof (proj1 (Forall_forall _ _) HLch _ ltac:(right; right; left; reflexivity)) as Hc.
  pose proof (val_of_chunk_ok SEGS E _ LA _ _ _ cap Hc) as V. apply V.
  - cbn [sv_denot]. rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  - ldz.
  - ldz. }
assert (MawrC : awr W (ms_mem ms) LA 16) by (intros j Hj; exact (HLw j Hj)).
assert (KLA : forall a, LA <= a < LA + 8 \/ LA + 12 <= a < LA + 16 ->
  aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem a).
{ intros a [Ha|Ha].
  - replace a with (LA + (a - LA)) by lia.
    apply (ld_aview_agree W W mem (ms_mem ms) LA 8 v); [exact M1 | exact MvC | simpl Z.of_nat; lia].
  - replace a with ((LA + 12) + (a - (LA + 12))) by lia.
    apply (ld_aview_agree W W mem (ms_mem ms) (LA + 12) 4 cap); [exact M3 | exact McC | simpl Z.of_nat; lia]. }
(* record i's text pointer, a vector byte the prologue kept *)
pose proof (ld_rec_ptr B ly S W mem LA (HarnessRep.HL v cap recs junk) lines i HL Hi) as Ms0.
cbn [HarnessRep.hl_v HarnessRep.hl_recs] in Ms0. rewrite Z.mod_small in Ms0 by lia.
assert (MsC : val_mem SEGS (arm W (ms_mem ms)) (v + AREC * Z.of_nat i) 8 (fst (nth i recs (0, [])))).
{ unfold AREC. apply (val_mem_kept SEGS (w_H W) (w_H W) mem (ms_mem ms)); [|exact Ms0].
  intros k Hk. simpl Z.of_nat in Hk. apply (HBK v (AREC * cap)); [exact Hvin | rewrite Hvreq; ldl]. }
(* the ROM view: no ROM byte is in the frame or in G *)
assert (HromC : rom_view SEGS W (ms_mem ms)).
{ intros a Hin. destruct (ROMS a Hin) as (_ & _ & HnG).
  assert (Himg : in_img SEGS a) by (destruct Hin as (sg & Hsg & _ & Hr); exists sg; split; [exact Hsg | exact Hr]).
  pose proof (pa_img_range a Himg) as Har.
  rewrite (KEEP0 a ltac:(lia) ltac:(apply HNS; lia) ltac:(intros Hl; exact (HnG (HLG a Hl)))).
  exact (Hrom a Hin). }
assert (FPs : In (fst (nth i recs (0, [])), Z.of_nat (length (snd (nth i recs (0, [])))) + 1) (ablocks B ly S) ->
  forall j, 0 <= j < req_size (Z.of_nat (length (snd (nth i recs (0, [])))) + 1) ->
  inFP FP (fst (nth i recs (0, [])) + j)).
{ intros _ j Hj. exists (fst (nth i recs (0, [])),
    fst (nth i recs (0, [])) + req_size (Z.of_nat (length (snd (nth i recs (0, [])))) + 1)).
  split; [right; left; reflexivity | cbn [fst snd]; lia]. }
assert (FPv : forall a, v <= a < v + AREC * cap -> inFP FP a).
{ intros a Ha. exists (v, v + AREC * cap). split; [left; reflexivity | cbn [fst snd]; lia]. }
(* ---- the body, 0x8585c .. 0x858c0 (ld_bodyX_xR) ---- *)
pose proof ld_bodyX_xR as LB. ld_inst LB. specialize (LB R R_trans WLE_R RO RO_ARx AFREE_R).
eapply (SRrG_bind SEGS R R_trans).
{ exact (LB W (ms_regs ms) (ms_mem ms) _ (spZ regs) FP ly S Hp W mem md [] ly S Hp 0 LA v (Z.of_nat (length recs)) cap i
    (fst (nth i recs (0, []))) (Z.of_nat (length (snd (nth i recs (0, []))))) (getr regs 1) kr
    HJ Ub R1 Hra Hra4 R3 R4 R8 R9 R10 R18 R19 HiZ (conj Hn0 Hcap) HLA8 HLG HZS MvC MnC McC MawrC MsC Hs64
    Hvin Hsin Hlen0 Hvne FPs FPv Hcap32 Hmo
    (* the free's room premise: MT_rk charges 1 for a free (W_contract_x.v:258), so Z.to_nat (mo_free MT_rk) + kr
       is 1 + kr by conversion; its count premise is the spec's, cnt_ok being cnt_ok_pk at peak 0 *)
    HRM HCNT HromC). }
cbv beta. intros W' c' HR' (ly' & S' & Hp' & regs' & mem' & md' & -> & HJ' & HCL & Hbl & Hfrs & Hmole & HRM' & HKhi &
  HKimg & HKblk & Hmv & Hn' & Hawr' & Hapr & Herrb).
clear LB.
pose proof HJ as HARb. apply ajournal_gx_AR_xR in HARb.
pose proof HJ' as HAR'. apply ajournal_gx_AR_xR in HAR'.
pose proof HJ' as (_ & _ & (memS' & HJi' & _) & _). rewrite !Z.add_0_r in HJi'.
pose proof HJi' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPR' & _).
destruct (alx_const _ _ _ LAWS _ _ _ _ _ _ HARb) as (Kc1 & _ & Kg1 & _).
destruct (alx_const _ _ _ LAWS _ _ _ _ _ _ HAR') as (Kc2 & _ & Kg2 & _).
rewrite HBgot, HBcell in Kg1, Kg2. rewrite HBcell in Kc1, Kc2.
pose proof (val_mem_of_rdword SEGS _ _ _ _ Kg1) as VG1. pose proof (val_mem_of_rdword SEGS _ _ _ _ Kg2) as VG2.
pose proof (val_mem_of_rdword SEGS _ _ _ _ Kc1) as VC1. pose proof (val_mem_of_rdword SEGS _ _ _ _ Kc2) as VC2.
(* back at 0x858c0: splice the body's result, dropping the list region (the body changed l->n); s2 is not
   kept by the body (it holds &l->n across the memmove), so it is havocked too, and the epilogue reloads it *)
jafter_stretch_keep_hi HS 36%nat regs' (mrestrict (w_H W') mem') (18%bv :: CLOB) A_ld_epi [0;1;2]%nat HS2.
match type of HS2 with ?P1 -> ?Q1 -> _ =>
assert (HP : P1); [|assert (HQ : Q1); [|specialize (HS2 HP HQ); clear HP HQ]] end.
{ intros r0 Hr0. cbn [ms_regs restrict]. exact (HCL r0 Hr0). }
{ cbn [ms_mem restrict].
  apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
  - split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Usp.
    + intros a Ha. apply (mbyte_of_aview SEGS). apply HKhi; [ldl | rewrite Ub; ldl].
    + intros a Ha _. apply (apresent_writable SEGS). apply HPR'. ldl.
  - exact (region_kept_val_at E _ _ (A_OBJ 0) (VAL (A_OBJ 0)) 8 (VAL (A_OBJ 32)) 0 0 _
      (HEI (A_OBJ 0) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) VG1 VG2 ltac:(lia)).
  - exact (region_kept_val_at E _ _ (A_OBJ 32) (VAL (A_OBJ 32)) 8 SHADOW_OFF 0 0 _
      (HEI (A_OBJ 32) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) VC1 VC2 ltac:(lia)). }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 36 (map (getr regs') (18%bv :: CLOB))) as Ea eqn:HEa in HS.
assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDa : forall m0, (m0 < 36)%nat -> ew Ea m0 = ew E m0)
by (intros m0 Hm0; rewrite HEa; apply YN3v.ew_havoc_old; exact Hm0).
assert (HAEa : env_agree 32 (Ereg regs (ld_extra (HarnessRep.HL v cap recs junk))) Ea)
by (rewrite HEa; apply env_agree_havoc_ge; [cbv; lia | exact HAE]).
clear HEa.
assert (Uspa : bv_unsigned (ew Ea 2) = spZ regs) by (rewrite OLDa by (cbv; lia); exact Usp).
assert (SHOK2 : sh_ok SEGS ld_Bx [] Ea (mrestrict (w_H W') mem')) by constructor.
(* ---- the epilogue, 0x858c0 .. the ret ---- *)
paj_run_tok_xR RUNG HS HJ' SHOK2 ld_Bspan.
{ lazymatch goal with |- awr_ok_x ?E ?rs ?G ?XO ?OUT ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok_x E rs' G XO OUT stk sp0 fp b0 bc ly own) end.
  apply awr_ok_x_cons_awr0; [awr_ok_tac; try exact Uspa|].
  apply awr_ok_x_cons_awr0; [awr_ok_tac|].
  apply awr_ok_x_cons_awr0; [awr_ok_tac|].
  apply awr_ok_x_nil. }
(* the epilogue wrote only the frame *)
assert (KEEP3 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - LDROP_FRAME <= a < spZ regs) ->
  aview SEGS (w_H W') (ms_mem ms0) a = aview SEGS (w_H W') mem' a).
{ intros a Ha Hno.
  lazymatch type of HFr0 with frame_of ?Ev ?rs _ _ =>
    apply (aview_kept_out Ev rs (w_H W') mem' (ms_mem ms0) HFr0 a Ha) end.
  intros (r & Hin & Hr). vm_compute in Hin.
  repeat (destruct Hin as [<- | Hin];
    [cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?Uspa in Hr;
     unfold LDROP_FRAME in Hno; lia |]).
  destruct Hin. }
prreg HS (1%bv : bv 5) R1f.
apply (SRr_SRrG SEGS R WLE_R). eapply (RET W' _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. unfold ldrop_post_xR. cbv beta.
exists ly', S', Hp'.
lazymatch goal with |- exists _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ => exists r, m, d end.
split; [cbn [ms_regs]; rewrite R1f; rewrite OLDa by (cbv; lia); rewrite E1, Hra; reflexivity|].
split; [apply (ajournal_gx_materialize_xR SEGS B PST ARx LAWS Hsegs); exact HJ'|].
split.
{ lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
  eapply (aregs_preserved_of_st_ok SEGS _ Ev _ _ regs (ld_extra (HarnessRep.HL v cap recs junk)) HS);
  [exact HAEa | vm_compute; reflexivity] end. }
split.
{ intros a Hia Hoa Hea Hpa. apply (apresent_grows (w_H W') mem' (ms_mem ms0) a HG1).
  apply (Hapr a Hia Hoa Hea). apply (apresent_grows (w_H W) mem (ms_mem ms) a HG0). exact Hpa. }
split.
{ (* errno's view: errno is an image byte (pal_env) off the frame and off the list head (gx_rt); the prologue and
     the epilogue wrote neither, and the body kept its view (ldb_post_xR) *)
  intros j Hj. pose proof (pal_env B TL) as (_ & HeImg & _).
  assert (HeI : in_img SEGS (as_errno B + j)) by (apply HeImg; lia).
  pose proof (pa_img_range _ HeI) as HeR.
  assert (HeL : ~ (LA <= as_errno B + j < LA + 16)) by (intros Hc; exact (proj1 (GRT _ (HLG _ Hc)) ltac:(lia))).
  rewrite KEEP3 by (first [apply HNS; lia | lia]).
  rewrite (Herrb j Hj).
  exact (KEEP0 (as_errno B + j) ltac:(lia) ltac:(apply HNS; lia) HeL). }
split.
{ (* the representation half: the list at LA after the call is ldrop_list l i *)
  pose proof alist_at_drop as AD. ld_inst AD.
  apply (AD ly S W mem ly' S' W' (ms_mem ms0) LA (HarnessRep.HL v cap recs junk) lines i HL Hi);
  cbn [HarnessRep.hl_v HarnessRep.hl_cap HarnessRep.hl_recs HarnessRep.hl_junk]; unfold HarnessRep.hl_n;
  cbn [HarnessRep.hl_recs].
  - exact Hbl.
  - (* the head but its count: an image byte of G, kept by the body and by the epilogue *)
    intros a Ha. assert (HaG : LA <= a < LA + 16) by lia.
    rewrite KEEP3 by ldl.
    rewrite (HKimg a (proj1 (HG a (HLG a HaG))) (proj1 (proj2 (HG a (HLG a HaG)))) (proj1 (GRT a (HLG a HaG))) ltac:(lia)).
    exact (KLA a Ha).
  - apply (awr_kept_w W' W' mem' (ms_mem ms0) LA 16);
    [intros x _ Hpa; exact (apresent_grows _ _ _ x HG1 Hpa) | apply wle_refl | exact Hawr'].
  - apply (val_mem_kept SEGS (w_H W') (w_H W') mem' (ms_mem ms0)); [|exact Hn'].
    intros k Hk. simpl Z.of_nat in Hk. apply KEEP3; ldl.
  - (* the records above i, one record lower *)
    intros k Hk. rewrite KEEP3 by ldl. rewrite (Hmv k Hk).
    apply (HBK v (AREC * cap)); [exact Hvin | rewrite Hvreq; ldl].
  - (* the rest of the vector *)
    intros a Ha.
    assert (Hva : v <= a < v + req_size (AREC * cap)) by (rewrite Hvreq; ldl).
    rewrite KEEP3 by ldl.
    rewrite (HKblk v (AREC * cap) a Hvin Hva).
    + exact (HBK v (AREC * cap) a Hvin Hva).
    + exact (ld_blk_disj_x ly S Hp W mem md _ _ _ _ a HAR Hvin Hsin Hvne Hva).
    + ldl.
  - (* the texts of the other records *)
    intros r Hr a Ha.
    cbn [ldrop_list HarnessRep.hl_recs] in Hr.
    destruct (ld_recs_drop recs i r Hi ltac:(apply NoDup_ListNoDup; exact HND) Hr) as (HrIn & Hrne).
    pose proof (proj1 (Forall_forall _ _) HRF r HrIn) as (Hrin & _ & _ & _).
    destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md _ _ HAR Hrin) as (_ & Hr4096 & Hrceil & _ & _ & _).
    assert (Hrreq : req_size (Z.of_nat (length (snd r)) + 1) = Z.of_nat (length (snd r)) + 1)
    by (unfold req_size; destruct (Z.eqb_spec (Z.of_nat (length (snd r)) + 1) 0); lia).
    rewrite Hrreq in Hrceil.
    assert (Hra' : fst r <= a < fst r + req_size (Z.of_nat (length (snd r)) + 1)) by (rewrite Hrreq; lia).
    assert (Hrv : fst r <> v) by (intros Ev; apply Hvni; rewrite <- Ev; apply in_map; exact HrIn).
    rewrite KEEP3 by ldl.
    rewrite (HKblk _ _ a Hrin Hra').
    + exact (HBK _ _ a Hrin Hra').
    + exact (ld_blk_disj_x ly S Hp W mem md _ _ _ _ a HAR Hrin Hsin Hrne Hra').
    + intros Hm. apply (ld_blk_disj_x ly S Hp W mem md _ _ _ _ a HAR Hrin Hvin Hrv Hra'). rewrite Hvreq. ldl. }
split; [exact Hbl | split; [exact Hmole | exact HRM']].
Qed.
End wR.
End dc.
(* The strong-rule form, its statement and Section hypotheses unchanged: the strong rule gives the context rule at
   the one-row table [[BASE + AF_fr_list_drop + 0x60]] (W_journal_x.v afree_cf_rule_c_weak_x). *)
Section d.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
Hypothesis HP0 : forall ly S Hp W mem md, ARx ly S Hp W mem md -> Hp = [].
Variable MT : ameter_ops.
Variable RP : roomp.
Variable G : list (Z * Z).
Hypothesis HG : gx_ok SEGS B G.
Hypothesis GRT : gx_rt B G.
Hypothesis TL : PALib B.
Hypothesis AFREE : afree_cf_rule_x SEGS B PST ARx MT RP.
Hypothesis AMOVE : amemmove_realizes_x B ARx (SIGMA WS_asan_memmove).
Hypothesis ROMS : forall a, in_rom SEGS a ->
(Exists (in_zr a) (as_owned_static B) -> rom_pinned SEGS B a) /\ ~ (as_errno B <= a < as_errno B + 4) /\ ~ inG G a.
Theorem pb_list_drop_x : ldrop_spec_x B PST ARx MT RP G A_list_dropP.
Proof.
pose proof (afree_cf_rule_c_weak_x SEGS B PST ARx MT RP [[BASE + AF_fr_list_drop + 0x60]] AFREE) as AFREEc.
assert (HCTX0 : In [BASE + AF_fr_list_drop + 0x60] [[BASE + AF_fr_list_drop + 0x60]]) by (left; reflexivity).
eapply pb_list_drop_cx_x; eassumption.
Qed.
(* route R: pb_list_drop_x at a world relation R.  The strong R rule gives the R context rule at the one-row table
   [[BASE + AF_fr_list_drop + 0x60]] (W_journal_x.v afree_cf_rule_c_weak_xR). *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
Variable RO : (word -> option byte) -> Prop.
Hypothesis RO_ARx : forall ly S Hp (W : world SEGS) mem md, ARx ly S Hp W mem md -> RO mem.
Hypothesis AFREE_R : afree_cf_rule_xR SEGS B PST ARx MT RP RO R.
(* :503 pb_list_drop_x *)
Theorem pb_list_drop_xR : ldrop_spec_xR B PST ARx R MT RP G A_list_dropP.
Proof.
pose proof (afree_cf_rule_c_weak_xR SEGS B PST ARx MT RP RO [[BASE + AF_fr_list_drop + 0x60]] AFREE_R) as AFREEc.
assert (HCTX0 : In [BASE + AF_fr_list_drop + 0x60] [[BASE + AF_fr_list_drop + 0x60]]) by (left; reflexivity).
eapply pb_list_drop_cx_xR with (R := R) (RO := RO); eassumption.
Qed.
End wR.
(* The G-generic form: a G-generic ldrop_spec over gx_ok and gx_rt alone was deleted from W_contract.v at
   7086983dbc8, because the body (ld_bodyX_x) needs ROMS at the G it runs at, i.e. no ROM byte in G (at least none
   in the list head's 16 bytes), and neither gx_ok, gx_rt nor the relation gives that.  W_journal.v's rom_out G
   gives ROMS, so a caller that holds gx_ok, gx_rt and rom_out at its G takes pb_list_drop_ro_x below. *)
End d.
Section e.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
Hypothesis HP0 : forall ly S Hp W mem md, ARx ly S Hp W mem md -> Hp = [].
Variable MT : ameter_ops.
Variable RP : roomp.
Hypothesis TL : PALib B.
Hypothesis AFREE : afree_cf_rule_x SEGS B PST ARx MT RP.
Hypothesis AMOVE : amemmove_realizes_x B ARx (SIGMA WS_asan_memmove).
Theorem pb_list_drop_ro_x : forall G, gx_ok SEGS B G -> gx_rt B G -> rom_out SEGS B G ->
ldrop_spec_x B PST ARx MT RP G A_list_dropP.
Proof.
intros G HG GRT HRO. eapply pb_list_drop_x; try eassumption.
intros a Ha. destruct (HRO a Ha) as (HnG & Hpin & Hne & _). exact (conj Hpin (conj Hne HnG)).
Qed.
(* route R: pb_list_drop_ro_x at a world relation R, from pb_list_drop_xR *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
Variable RO : (word -> option byte) -> Prop.
Hypothesis RO_ARx : forall ly S Hp (W : world SEGS) mem md, ARx ly S Hp W mem md -> RO mem.
Hypothesis AFREE_R : afree_cf_rule_xR SEGS B PST ARx MT RP RO R.
(* :526 pb_list_drop_ro_x *)
Theorem pb_list_drop_ro_xR : forall G, gx_ok SEGS B G -> gx_rt B G -> rom_out SEGS B G ->
ldrop_spec_xR B PST ARx R MT RP G A_list_dropP.
Proof.
intros G HG GRT HRO. eapply pb_list_drop_xR with (R := R) (RO := RO); try eassumption.
intros a Ha. destruct (HRO a Ha) as (HnG & Hpin & Hne & _). exact (conj Hpin (conj Hne HnG)).
Qed.
End wR.
End e.
(* The G-generic form at the caller-context rule: what an instance with only afree_cf_rule_c_x at a table CTX
   holding [BASE + AF_fr_list_drop + 0x60] takes (top_x: AFREE_x at K0's CTX_AFREE, whose row 0x85874 this is). *)
Section ec.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
Hypothesis HP0 : forall ly S Hp W mem md, ARx ly S Hp W mem md -> Hp = [].
Variable MT : ameter_ops.
Variable RP : roomp.
Variable CTX : list (list Z).
Hypothesis HCTX : In [BASE + AF_fr_list_drop + 0x60] CTX.
Hypothesis TL : PALib B.
Hypothesis AFREE : afree_cf_rule_c_x SEGS B PST ARx MT RP CTX.
Hypothesis AMOVE : amemmove_realizes_x B ARx (SIGMA WS_asan_memmove).
Theorem pb_list_drop_ro_cx_x : forall G, gx_ok SEGS B G -> gx_rt B G -> rom_out SEGS B G ->
ldrop_spec_x B PST ARx MT RP G A_list_dropP.
Proof.
intros G HG GRT HRO. eapply pb_list_drop_cx_x; try eassumption.
intros a Ha. destruct (HRO a Ha) as (HnG & Hpin & Hne & _). exact (conj Hpin (conj Hne HnG)).
Qed.
(* route R: pb_list_drop_ro_cx_x at a world relation R, from pb_list_drop_cx_xR *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
Variable RO : (word -> option byte) -> Prop.
Hypothesis RO_ARx : forall ly S Hp (W : world SEGS) mem md, ARx ly S Hp W mem md -> RO mem.
Hypothesis AFREE_R : afree_cf_rule_c_xR SEGS B PST ARx MT RP RO CTX R.
(* :549 pb_list_drop_ro_cx_x *)
Theorem pb_list_drop_ro_cx_xR : forall G, gx_ok SEGS B G -> gx_rt B G -> rom_out SEGS B G ->
ldrop_spec_xR B PST ARx R MT RP G A_list_dropP.
Proof.
intros G HG GRT HRO. eapply pb_list_drop_cx_xR with (R := R) (RO := RO) (CTX := CTX); try eassumption.
intros a Ha. destruct (HRO a Ha) as (HnG & Hpin & Hne & _). exact (conj Hpin (conj Hne HnG)).
Qed.
End wR.
End ec.

(* ---- THE AR STATEMENTS, re-derived (route (b), step 3): pb_list_drop's and pb_list_drop_ro's statements are the
   AR walk's, byte-identical, now corollaries of pb_list_drop_x / pb_list_drop_ro_x at ARx := ARi0 (cgif's AR with
   the head set empty), PST := [].  Their Sections take LX0 (the laws at ARi0) in place of LAWS: the instance builds
   it once, W_journal_x.AR_laws_x_ARi0 (YCbqG.AR_laws_x_of_AR ..).  The bridge is W_contract_x.ldrop_spec_x_AR0; HP0
   at ARi0 is ARi0_hp0; the callee hypotheses stay in their AR form and become the generic ones at ARi0 through the
   kit's W_journal_x.afree_cf_rule_x_of_AR0 and W_sites_x.amemmove_realizes_x_of_AR0. ---- *)
Section dAR.
Variable B : asyms.
Variable MT : ameter_ops.
Variable G : list (Z * Z).
Hypothesis LX0 : AR_laws_x SEGS B (ARi0 SEGS B) 0.
Hypothesis HG : gx_ok SEGS B G.
Hypothesis GRT : gx_rt B G.
Hypothesis TL : PALib B.
Hypothesis AFREE : afree_cf_rule SEGS B MT.
Hypothesis AMOVE : amemmove_realizes B (SIGMA WS_asan_memmove).
(* rom_view has to cross the free call (W_list_drop.v's ROMS, the same text: acall_kept keeps an image byte outside
   the allocator's statics and errno, and the statics' read-only bytes are AR's pinned const cells). *)
Hypothesis ROMS : forall a, in_rom SEGS a ->
(Exists (in_zr a) (as_owned_static B) -> rom_pinned SEGS B a) /\ ~ (as_errno B <= a < as_errno B + 4) /\ ~ inG G a.
Theorem pb_list_drop : ldrop_spec B MT G A_list_dropP.
Proof.
apply ldrop_spec_x_AR0.
assert (HP0 : forall ly S Hp W mem md, ARi0 SEGS B ly S Hp W mem md -> Hp = []) by apply ARi0_hp0.
pose proof (afree_cf_rule_x_of_AR0 SEGS B MT AFREE) as AFREE0.
pose proof (amemmove_realizes_x_of_AR0 B (SIGMA WS_asan_memmove) AMOVE) as AMOVE0.
eapply pb_list_drop_x; eassumption.
Qed.
End dAR.
Section eAR.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis LX0 : AR_laws_x SEGS B (ARi0 SEGS B) 0.
Hypothesis TL : PALib B.
Hypothesis AFREE : afree_cf_rule SEGS B MT.
Hypothesis AMOVE : amemmove_realizes B (SIGMA WS_asan_memmove).
Theorem pb_list_drop_ro : forall G, gx_ok SEGS B G -> gx_rt B G -> rom_out SEGS B G ->
ldrop_spec B MT G A_list_dropP.
Proof.
intros G HG GRT HRO. apply ldrop_spec_x_AR0.
assert (HP0 : forall ly S Hp W mem md, ARi0 SEGS B ly S Hp W mem md -> Hp = []) by apply ARi0_hp0.
pose proof (afree_cf_rule_x_of_AR0 SEGS B MT AFREE) as AFREE0.
pose proof (amemmove_realizes_x_of_AR0 B (SIGMA WS_asan_memmove) AMOVE) as AMOVE0.
eapply pb_list_drop_ro_x; eassumption.
Qed.
End eAR.
End b.
End a.

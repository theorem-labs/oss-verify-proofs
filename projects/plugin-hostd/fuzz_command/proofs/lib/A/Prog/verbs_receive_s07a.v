(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: helpers of segment S07 (route add, 0x8d8fc) of the walk of verbs_receive on the
   ASan build of plugin-hostd/fuzz_command (lib/A/Prog/verbs_receive_iface.v, vr_s07_stmt). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YI08 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05 YI00 YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaDenot PaLibG PaLibF PaLibH PaCallRun PaCall PaArt.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs VerbsRun StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require verbs_receive_route VerbsFacts.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdObj CmdRo CmdBase CmdRep CmdAddr.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require RtString RtNumber RtAlloc04 RtShadow.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
descriptors_add_c reply_c sup_add_c sup_reply_code_c sup_resp_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import verbs_receive_c verbs_receive_iface verbs_receive_kit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Module VRR := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.verbs_receive_route.
Module PV := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec.Verbs.

(* ---------------------------------------------------------------------------------------------------------------
   Reader facts *)
Lemma aval_val : forall segs H mem a n v, aval_mem (aview segs H mem) a n v -> val_mem segs (mrestrict H mem) a n v.
Proof.
intros segs H mem a n v Hr k Hk. pose proof (Hr k Hk) as Hb.
destruct (aview_byte segs H mem _ _ Hb) as (b & Hm & Hbv & Hrange). rewrite Hm. f_equal. apply bv_eq.
rewrite Z_to_bv_unsigned. unfold bv_wrap. rewrite <- Hbv. rewrite Z.mod_small; [reflexivity|].
change (bv_modulus 8) with 256. exact Hrange.
Qed.
Lemma atoks_atA_agree : forall (rd rd' : reader) tok ptrs tks cb ncb,
atoks_atA rd tok ptrs tks cb ncb ->
(forall k, 0 <= k < 8 * Z.of_nat (length ptrs) -> rd' (tok + k) = rd (tok + k)) ->
(forall k, 0 <= k < ncb -> rd' (cb + k) = rd (cb + k)) ->
atoks_atA rd' tok ptrs tks cb ncb.
Proof.
intros rd rd' tok ptrs tks cb ncb (H8 & Hlen & Hp & Hw) HT HB.
split; [exact H8|]. split; [exact Hlen|]. split.
- intros i p Hi. apply (aval_mem_agree rd rd' _ 8 _ (Hp i p Hi)).
  assert (Hi' : (i < length ptrs)%nat) by (apply nth_error_Some; rewrite Hi; discriminate).
  intros k Hk. change (Z.of_nat 8) with 8 in Hk.
  replace (tok + 8 * Z.of_nat i + k) with (tok + (8 * Z.of_nat i + k)) by lia. apply HT. lia.
- intros i p w Hi Hw'. destruct (Hw i p w Hi Hw') as (Hs & Hl & Hc1 & Hc2).
  split; [|split; [exact Hl | split; [exact Hc1 | exact Hc2]]].
  apply (astr_atR_agree rd rd' _ _ (cb + ncb - p) Hs); [lia|].
  intros k Hk. replace (p + k) with (cb + (p - cb + k)) by lia. apply HB. lia.
Qed.
Lemma aval_of_abytes : forall rd a l n v, abytes_atR rd a l -> length l = n ->
(forall k, (k < n)%nat -> bv_unsigned (nth k l (Z_to_bv 8 0)) = le_byte v n k) -> aval_mem rd a n v.
Proof. intros rd a l n v H Hl Hk k Hkn. rewrite (H k ltac:(lia)). f_equal. apply Hk. exact Hkn. Qed.
Lemma got_of_ro : forall rd, cmd_ro_ok rd -> cmd_got_ok rd.
Proof.
intros rd [Hb _]. unfold cmd_ro_bytes in Hb.
repeat match type of Hb with _ /\ _ => let H := fresh "R" in destruct Hb as [H Hb] end.
unfold cmd_got_ok.
repeat split; (eapply aval_of_abytes; [eassumption | reflexivity |
  intros k Hk; do 8 (destruct k as [|k]; [vm_compute; reflexivity|]); lia]).
Qed.

(* ---------------------------------------------------------------------------------------------------------------
   The model's view of the add route *)
Lemma route_add : forall tk, VRR.route tk = VRR.RAdd -> tk <> [] -> exists args, tk = PV.Lit.verb_add :: args.
Proof.
intros [|v args] H Hne; [congruence|]. exists args. cbn [VRR.route] in H.
destruct (PV.list_eqb v PV.Lit.verb_add) eqn:E; [apply PV.list_eqb_eq in E; subst; reflexivity|].
exfalso. unfold VRR.route_mid, VRR.route_tail, VRR.route_conn, VRR.route_cd in H.
repeat match type of H with
| context [if ?b then _ else _] => destruct b
| context [match ?x with Some _ => _ | None => _ end] => destruct x
| context [match ?x with [] => _ | _ :: _ => _ end] => destruct x
end; discriminate.
Qed.
Lemma st_add : forall D args, PV.toks D = PV.Lit.verb_add :: args -> vr_st D = PV.add_m atoi_a args.
Proof. intros D args H. unfold vr_st, PV.receive. rewrite H. reflexivity. Qed.
Lemma evr_add : forall R D args, PV.toks D = PV.Lit.verb_add :: args ->
ev_route R (PV.line D) (PV.toks D) (vr_st D) = ev_step R (PV.add_m atoi_a args).
Proof. intros R D args H. rewrite (st_add D args H), H. reflexivity. Qed.
Lemma dropw_le : forall p l, (length (PV.dropw p l) <= length l)%nat.
Proof. intros p l; induction l as [|x l IH]; cbn [PV.dropw length]; [lia|]. destruct (p x); cbn [length]; lia. Qed.
Lemma upto0_strnlen : forall D, Z.of_nat (length (PV.upto0 D)) = StrFun.strnlen_res (Z.of_nat (length D)) D.
Proof.
intros D. unfold StrFun.strnlen_res. rewrite Nat2Z.id, firstn_all. unfold PV.upto0.
induction D as [|b D IH]; cbn [PV.upto length StrFun.find_byte]; [reflexivity|].
destruct (bv_unsigned b =? 0) eqn:E; cbn [length]; [lia|].
destruct (StrFun.find_byte 0 D) as [i|] eqn:Ei; rewrite ?Ei in IH; cbn iota beta in IH |- *; lia.
Qed.
Lemma line_le_l : forall D n, Z.of_nat (length D) = n -> Z.of_nat (length (PV.line D)) <= vr_l n D.
Proof.
intros D n Hn. unfold vr_l, PV.line, PV.trim. rewrite length_rev.
pose proof (dropw_le PV.is_trail (rev (PV.upto0 D))) as L. rewrite length_rev in L.
pose proof (upto0_strnlen D) as U. rewrite Hn in U. lia.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* ---------------------------------------------------------------------------------------------------------------
   The symbolic state at a point of S07: every register an atom of its own value; two read-only regions, the spill
   slots of the real frame that S07 reloads (s1+24 line, s1+32 shadow(F)+4, s1+40 F, s1+56 copy) and the words
   tok[1..m] of the side-stack frame (at s6 = F+32), each holding an atom of the environment's extra part *)
Definition spill07 : YP09.region :=
YP09.mkRegion (Some 9%nat) 24 64 0 0
[YP09.mkChunk 24 (CVal 8 (SOff 32 0)); YP09.mkChunk 32 (CVal 8 (SOff 33 0));
 YP09.mkChunk 40 (CVal 8 (SOff 34 0)); YP09.mkChunk 56 (CVal 8 (SOff 35 0))].
Definition tok07 (m : nat) : YP09.region :=
YP09.mkRegion (Some 22%nat) 8 (8 + 8 * Z.of_nat m) 0 0
(map (fun i => YP09.mkChunk (8 + 8 * Z.of_nat i) (CVal 8 (SOff (36 + i) 0))) (seq 0 m)).
Definition ss07 (pc : Z) (m : nat) : sstate := mkSS pc sr_atoms [spill07; tok07 m] None (mkFacts [] [] []).
Definition E07 (regs : bvmap 5 word) (q shf F c : Z) (tps : list Z) : env :=
Eimg (Ereg regs (map (Z_to_bv 64) ([q; shf; F; c] ++ tps))).

Lemma E07_reg : forall regs q shf F c tps n (r : bv 5), Z.of_nat n = bv_unsigned r ->
ew (E07 regs q shf F c tps) n = getr regs r.
Proof.
intros regs q shf F c tps n r Hn. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
unfold E07. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn.
Qed.
Lemma E07_ext : forall regs q shf F c tps j v, (j < 100)%nat -> nth_error ([q; shf; F; c] ++ tps) j = Some v ->
ew (E07 regs q shf F c tps) (32 + j) = Z_to_bv 64 v.
Proof.
intros regs q shf F c tps j v Hj100 H. pose proof (nth_error_Some ([q; shf; F; c] ++ tps) j) as [Hl _].
assert (Hj : (j < length ([q; shf; F; c] ++ tps))%nat) by (apply Hl; rewrite H; discriminate).
unfold E07. rewrite Eimg_low by (unfold A_TEXT; lia).
rewrite ew_Ereg_extra. rewrite (map_nth (Z_to_bv 64) _ 0). erewrite nth_error_nth; [reflexivity | exact H].
Qed.
Lemma E07_env : forall regs q shf F c tps, img_env VAL A_LIM (E07 regs q shf F c tps).
Proof. intros. unfold E07. apply Eimg_env. Qed.

Ltac chunk07 Hv X :=
apply (chunk_ok_val SEGS _ _ _ _ 8 _ _ X); [exact (proj2 Hv) | cbn; lia | apply aval_val; exact (proj1 Hv)].

Lemma seed07 : forall (W : world SEGS) regs mem pc s1 F q c tps,
getr regs 9 = Z_to_bv 64 s1 -> getr regs 22 = Z_to_bv 64 (F + 32) ->
alloc_ceiling <= s1 -> s1 + 64 <= 2 ^ 47 -> 4096 <= F -> F + 1024 <= alloc_ceiling ->
aval_mem (rdW W mem) (s1 + 24) 8 q -> aval_mem (rdW W mem) (s1 + 32) 8 (shadow_addr F + 4) ->
aval_mem (rdW W mem) (s1 + 40) 8 F -> aval_mem (rdW W mem) (s1 + 56) 8 c ->
0 <= q < 2 ^ 64 -> 0 <= c < 2 ^ 64 -> 0 <= shadow_addr F + 4 < 2 ^ 64 ->
(forall i p, nth_error tps i = Some p -> aval_mem (rdW W mem) (F + 40 + 8 * Z.of_nat i) 8 p /\ 0 <= p < 2 ^ 64) ->
(length tps <= 4)%nat ->
st_ok_pi SEGS VAL (E07 regs q (shadow_addr F + 4) F c tps) (ss07 pc (length tps))
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS))).
Proof.
intros W regs mem pc s1 F q c tps H9 H22 Hs1 Hs1h HF0 HF1 Vq Vsh VF Vc Rq Rc Rsh Htp Hlen.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
set (E := E07 regs q (shadow_addr F + 4) F c tps).
assert (E9 : bv_unsigned (ew E 9) = s1).
{ unfold E. rewrite (E07_reg _ _ _ _ _ _ 9 9%bv eq_refl), H9. apply unsigned_lit_small. lia. }
assert (E22 : bv_unsigned (ew E 22) = F + 32).
{ unfold E. rewrite (E07_reg _ _ _ _ _ _ 22 22%bv eq_refl), H22. apply unsigned_lit_small. lia. }
assert (X32 : sv_denot E (SOff 32 0) = Z_to_bv 64 q).
{ cbn [sv_denot]. unfold E. rewrite (E07_ext _ _ _ _ _ _ 0 q ltac:(lia) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
assert (X33 : sv_denot E (SOff 33 0) = Z_to_bv 64 (shadow_addr F + 4)).
{ cbn [sv_denot]. unfold E. rewrite (E07_ext _ _ _ _ _ _ 1 _ ltac:(lia) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
assert (X34 : sv_denot E (SOff 34 0) = Z_to_bv 64 F).
{ cbn [sv_denot]. unfold E. rewrite (E07_ext _ _ _ _ _ _ 2 _ ltac:(lia) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
assert (X35 : sv_denot E (SOff 35 0) = Z_to_bv 64 c).
{ cbn [sv_denot]. unfold E. rewrite (E07_ext _ _ _ _ _ _ 3 _ ltac:(lia) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
assert (XT : forall i p, nth_error tps i = Some p -> sv_denot E (SOff (36 + i) 0) = Z_to_bv 64 p).
{ intros i p Hi. assert (Hil : (i < length tps)%nat) by (apply nth_error_Some; rewrite Hi; discriminate).
  cbn [sv_denot]. unfold E. replace (36 + i)%nat with (32 + (4 + i))%nat by lia.
  rewrite (E07_ext _ _ _ _ _ _ (4 + i) p ltac:(lia)); [rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity|].
  rewrite nth_error_app2 by (cbn; lia). cbn [length]. replace (4 + i - 4)%nat with i by lia. exact Hi. }
rewrite restrict_mkst_fx. unfold ss07. apply pa_entry_st_ok_full.
- unfold E, E07. apply regs_ok_Eimg_Ereg.
- destruct tps as [|t1 [|t2 [|t3 [|t4 [|t5 tps]]]]]; cbn [length] in *; try lia; vm_compute; reflexivity.
- apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  + unfold region_ok, spill07. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    * chunk07 (conj Vq Rq) X32.
    * chunk07 (conj Vsh Rsh) X33.
    * apply (chunk_ok_val SEGS _ _ _ _ 8 _ _ X34); [cbn; lia | cbn; lia | apply aval_val; exact VF].
    * chunk07 (conj Vc Rc) X35.
  + unfold region_ok, tok07. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E22. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_forall. intros ch Hch. apply in_map_iff in Hch as (i & <- & Hi). apply in_seq in Hi.
    destruct (nth_error tps i) as [p|] eqn:Ep; [|apply nth_error_None in Ep; lia].
    destruct (Htp i p Ep) as [Vp Rp].
    apply (chunk_ok_val SEGS _ _ _ _ 8 _ _ (XT i p Ep)); [exact Rp | cbn; lia |].
    apply aval_val. replace (F + 32 + (8 + 8 * Z.of_nat i)) with (F + 40 + 8 * Z.of_nat i) by lia. exact Vp.
- cbn [pairwise_disjoint all_disjoint]. split; [|split; exact I]. split; [|exact I].
  unfold extent_disjoint, spill07, tok07. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E9, E22. right. lia.
- split; [exact I | split; exact I].
Qed.

(* ---------------------------------------------------------------------------------------------------------------
   Carrying a boundary state over a step that keeps every byte below the allocation ceiling but the errno cell, and
   the real frame above s1 (a run without stores, or a runtime entry whose window lies under s1) *)
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Hypothesis TL : PALib B.
Hypothesis ROA : vr_ro_of_aro B.
Hypothesis RECC : vr_rec_cells B.
Hypothesis RRO : vr_relro_img.
Hypothesis PROGU : vr_prog_unowned B.
Hypothesis RPG : vr_pg_not_ro.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.

Lemma vr_s1_bounds : forall (e : vrE), vr_sp0 e mod 16 = 0 ->
vr_sp0 e - 208 <= vr_s1 e <= vr_sp0 e - 192 /\ (vr_s1 e - vr_sp0 e) mod 16 = 0.
Proof.
intros e H. unfold vr_s1. set (x := vr_sp0 e) in *.
pose proof (Z.mod_pos_bound (x - 192) 32 ltac:(lia)).
assert (Hm : (x - 192) mod 32 = 0 \/ (x - 192) mod 32 = 16).
{ pose proof (Z.div_mod x 16 ltac:(lia)). pose proof (Z.div_mod (x - 192) 32 ltac:(lia)). lia. }
destruct Hm as [Hm|Hm]; rewrite Hm; split; [lia | | lia |].
- replace (x - 192 - 0 - x) with (-192) by lia. reflexivity.
- replace (x - 192 - 16 - x) with (-208) by lia. reflexivity.
Qed.

Lemma vr_stk_ge : 4 * ESTACK + 208 <= VERBS_RECEIVE_STK /\ ASTACK + 208 <= VERBS_RECEIVE_STK.
Proof. unfold VERBS_RECEIVE_STK. unfold ESTACK, ASTACK. lia. Qed.
Lemma toks_le_64 : forall D, (length (PV.toks D) <= 64)%nat.
Proof. intros D. unfold PV.toks. apply firstn_le_length. Qed.

Lemma c07_wr : forall e pos F q c tp tmps rl rl' Rc Oc qv k kmax nm nmax lyc Sc Wc regsc regsc' memc memc' mdc mdc',
vr_core B MT e pos F tmps vr_sh2 (vr_sl3 F q c) rl Rc Oc qv k kmax nm nmax lyc Sc Wc regsc memc mdc ->
vr_line B e q Wc memc -> vr_copy B e F c tp Wc memc ->
ajournal SEGS B VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e)
  [(4, pos)] lyc Sc Wc memc' mdc' k ->
(forall a, 0 <= a < alloc_ceiling -> ~ (as_errno B <= a < as_errno B + 4) -> rdW Wc memc' a = rdW Wc memc a) ->
(forall a, vr_s1 e <= a < vr_sp0 e -> rdW Wc memc' a = rdW Wc memc a) ->
vr_rv regsc' (vr_base B e ++ rl') ->
In (vr_lb e q) tmps -> In (vr_cb e c) tmps -> Z.of_nat (length (e_D e)) = e_n e ->
vr_core B MT e pos F tmps vr_sh2 (vr_sl3 F q c) rl' Rc Oc qv k kmax nm nmax lyc Sc Wc regsc' memc' mdc' /\
vr_line B e q Wc memc' /\ vr_copy B e F c tp Wc memc'.
Proof.
intros e pos F q c tp tmps rl rl' Rc Oc qv k kmax nm nmax lyc Sc Wc regsc regsc' memc memc' mdc mdc'
Hcore Hline Hcopy HJ' KL KS Hrv' Hlb Hcb HDn.
destruct Hcore as (HJ & Hk & Hm & Hnm & Hfr & Hrv & Hsv & Hsp & Henv & Hrec & Hd & Hperm & Hq).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ' as (HAR' & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & Hstatic & _).
pose proof Hstatic as (Hal & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof vr_stk_ge as [Hstk4 Hstk5]. unfold ESTACK, ASTACK in *.
destruct (vr_s1_bounds e Hal) as [Hs1 _].
pose proof (pal_env B TL) as ((He0 & He1) & Heimg & _).
destruct Hfr as (HF & Hflag & Hsh).
assert (Hin4 : In (4, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS lyc Sc Wc memc' mdc' 4 pos HAR' Hin4) as (HF0 & HF1 & _).
rewrite <- HF in HF0, HF1. change (fs_frame_bytes 4) with 1024 in HF1.
assert (Hfimg : forall a, F <= a < F + 1024 -> ~ (as_errno B <= a < as_errno B + 4)).
{ intros a Ha He. apply (frm_img SEGS B LAWS lyc Sc Wc memc' mdc' 4 pos a HAR' Hin4); [rewrite <- HF; exact Ha | exact (Heimg a He)]. }
assert (Hblk : forall p n, In (p, n) (ablocks B lyc Sc) -> forall a, p <= a < p + n ->
  rdW Wc memc' a = rdW Wc memc a).
{ intros p n Hpn a Ha. destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR' Hpn) as (_ & Hp4 & Hpc & _ & _ & _ & Hn).
  pose proof (req_size_pos n ltac:(lia)) as [_ Hrq]. apply KL; [lia|].
  intros He. apply (blk_img SEGS B LAWS lyc Sc Wc memc' mdc' p n a HAR' Hpn ltac:(lia)). exact (Heimg a He). }
assert (Hpg : forall a, inFP cmd_PG a -> rdW Wc memc' a = rdW Wc memc a).
{ intros a Ha. destruct (PROGU a Ha) as (Hi & _ & Hne). pose proof (pa_segs_low a Hi). apply KL; [lia | exact Hne]. }
assert (Hbl : forall b, In b tmps -> In b (ablocks B lyc Sc)).
{ intros b Hb. apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. right. apply in_or_app. left. exact Hb. }
assert (Haro : arodata_okP SEGS RLO RHI B (rdW Wc memc')).
{ destruct Henv as (Haro & _). intros a Hro Ho He. rewrite KL; [exact (Haro a Hro Ho He) | | exact He].
  destruct Hro as [(s & Hs & _ & Hr) | Hr].
  - pose proof (pa_segs_low a (ex_intro _ s (conj Hs Hr))). lia.
  - pose proof (pa_segs_low a (RRO a Hr)). lia. }
destruct (RECC lyc Sc Wc memc' mdc' HAR') as (Hfl & Hag & Hev).
pose proof (ROA lyc Sc Wc memc' mdc' HAR' Haro) as Hro.
split; [|split].
- split; [exact HJ'|]. split; [exact Hk|]. split; [exact Hm|]. split; [exact Hnm|].
  split.
  { split; [exact HF|]. split.
    - rewrite (rdword_ext (rdW Wc memc) (rdW Wc memc')); [exact Hflag|]. intros j Hj. apply KL; [lia|]. apply Hfimg. lia.
    - intros i Hi. assert (HF8 : 0 <= F / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
      rewrite KL; [exact (Hsh i Hi) | unfold shadow_addr, SHADOW_OFF; lia | unfold shadow_addr, SHADOW_OFF; lia]. }
  split; [exact Hrv'|].
  split.
  { intros j r Hj. apply (aval_mem_agree _ _ _ 8 _ (Hsv j r Hj)). intros kk Hkk.
    assert (Hj' : (j < length vr_saved_regs)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
    change (length vr_saved_regs) with 13%nat in Hj'. change (Z.of_nat 8) with 8 in Hkk.
    apply KS. lia. }
  split.
  { unfold vr_spill in *. rewrite Forall_forall in Hsp |- *. intros ov Hov. specialize (Hsp ov Hov).
    apply (aval_mem_agree _ _ _ 8 _ Hsp). intros kk Hkk. change (Z.of_nat 8) with 8 in Hkk. apply KS.
    assert (Hov' : 0 <= fst ov <= 72).
    { unfold vr_sl3 in Hov. repeat (destruct Hov as [<-|Hov]; [cbn; lia|]). destruct Hov. }
    lia. }
  split.
  { split; [exact Haro|]. split; [exact (got_of_ro _ Hro)|]. split; [exact Hro|].
    split; [exact Hag|]. split; [exact Hfl | exact Hev]. }
  split.
  { apply (rec_repA_agree B lyc Sc lyc Sc (rdW Wc memc) (rdW Wc memc') Rc Oc Hrec).
    - intros pn _ H. exact H.
    - intros kk Hkk. apply Hpg. exists (A_G_REC, A_G_REC + 960). split; [left; reflexivity|]. cbn [fst snd].
      unfold REC_SIZE in Hkk. lia.
    - intros kk Hkk. apply Hpg. exists (A_REC_SPILL, A_REC_SPILL + 56). split; [right; left; reflexivity|]. cbn [fst snd].
      unfold SC_SIZE in Hkk. lia.
    - intros [p n] Hpn kk Hkk. cbn [fst snd] in *. apply (Hblk p n); [exact (rec_repA_in_blocks B _ _ _ _ _ _ Hrec Hpn) | lia]. }
  split; [exact Hd|]. split; [exact Hperm|].
  apply (aval_mem_agree _ _ _ 4 _ Hq). intros kk Hkk. apply Hpg.
  exists (A_G_QUITTING, A_G_QUITTING + 4). split; [right; right; left; reflexivity|]. cbn [fst snd]. lia.
- destruct Hline as [Hfq Hstr]. split; [exact Hfq|].
  apply (astr_atR_agree _ _ _ _ (vr_l (e_n e) (e_D e) + 1) Hstr).
  + pose proof (line_le_l (e_D e) (e_n e) HDn). lia.
  + intros kk Hkk. apply (Hblk q (vr_l (e_n e) (e_D e) + 1)); [exact (Hbl _ Hlb) | lia].
- destruct Hcopy as [Hfc Htk]. split; [exact Hfc|].
  apply (atoks_atA_agree _ _ _ _ _ _ _ Htk).
  + intros kk Hkk. pose proof (proj1 (proj2 Htk)) as Hlt. rewrite Hlt in Hkk. pose proof (toks_le_64 (e_D e)).
    apply KL; [lia | apply Hfimg; lia].
  + intros kk Hkk. apply (Hblk c (Z.of_nat (length (PV.line (e_D e))) + 1)); [exact (Hbl _ Hcb) | lia].
Qed.

Lemma nodup_app_disj : forall (A : Type) (l1 l2 : list A) x, List.NoDup (l1 ++ l2) -> In x l1 -> In x l2 -> False.
Proof.
induction l1 as [|a l1 IH]; intros l2 x H H1 H2; [destruct H1|]. cbn in H. apply List.NoDup_cons_iff in H as [Hn H].
destruct H1 as [<-|H1]; [apply Hn; apply in_or_app; right; exact H2 | exact (IH l2 x H H1 H2)].
Qed.
Lemma abl_nodup : forall ly S W mem md, AR SEGS B ly S W mem md -> List.NoDup (ablocks B ly S).
Proof.
intros ly S W mem md HAR.
assert (Hpos : Forall (fun b => 0 <= snd b) (ablocks B ly S)).
{ apply Forall_forall. intros [p n] Hin. destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR Hin) as (_ & _ & _ & _ & _ & _ & Hn). cbn. lia. }
assert (Hpw : pairwise zdisjoint (map (fun b => (fst b, req_size (snd b))) (ablocks B ly S))).
{ destruct (ablocks B ly S) as [|[p0 n0] l0] eqn:El; [cbn; exact I|].
  assert (Hin : In (p0, n0) (ablocks B ly S)) by (rewrite El; left; reflexivity).
  pose proof (al_blocks _ _ LAWS _ _ _ _ _ p0 n0 HAR Hin) as (_ & _ & _ & _ & _ & Hpw & _).
  rewrite El in Hpw. exact Hpw. }
apply (List.NoDup_map_inv (fun b => (fst b, req_size (snd b)))).
revert Hpos Hpw. generalize (ablocks B ly S). intros l.
induction l as [|b l IH]; intros Hpos Hpw; cbn in *; [constructor|].
destruct Hpw as [Hf Hp]. apply Forall_cons_iff in Hpos as [Hb Hpos'].
constructor; [|exact (IH Hpos' Hp)].
intros Hin. rewrite Forall_forall in Hf. pose proof (Hf _ Hin) as Hd.
pose proof (req_size_pos (snd b) Hb) as [H1 _]. unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
Qed.
Lemma perm_tmp_notin : forall ly S W mem md Oc tmps rest b, AR SEGS B ly S W mem md ->
Permutation (ablocks B ly S) (Oc ++ tmps ++ rest) -> In b tmps -> ~ In b Oc.
Proof.
intros ly S W mem md Oc tmps rest b HAR Hp Hb Hin. pose proof (abl_nodup ly S W mem md HAR) as Hnd.
apply (Permutation_NoDup Hp) in Hnd. apply (nodup_app_disj _ Oc (tmps ++ rest) b Hnd Hin). apply in_or_app. left. exact Hb.
Qed.

(* the frame chain at a program call of S07: the prologue's saves of ra and s0 at s0-8 and s0-16 push one record *)
Lemma chain07 : forall e pos lyc Sc Wc memc mdc k,
vr_ent B MT e ->
ajournal SEGS B VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e)
  [(4, pos)] lyc Sc Wc memc mdc k ->
vr_saved e Wc memc ->
exists ch1, achain lyc (rdW Wc memc) (vr_s1 e) (vr_sp0 e) ch1.
Proof.
intros e pos lyc Sc Wc memc mdc k Hent HJ Hsv.
pose proof Hent as (HPRE & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HrecE & _).
pose proof HPRE as (HAR0 & Hrok & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & _).
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & F1 & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
pose proof Hstk as (Hal & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof vr_stk_ge as [Hstk4 Hstk5]. unfold ESTACK, ASTACK in *.
change (spZ (e_regs e)) with (vr_sp0 e) in *.
destruct (vr_s1_bounds e Hal) as [Hs1 _].
destruct (Z_lt_le_dec (vr_sp0 e) (ly_top (e_ly e) - 16)) as [Hlt|Hge].
- exists ((vr_sp0 e, raZ (e_regs e), s0Z (e_regs e)) :: e_ch e).
  apply (achain_ly_top (e_ly e) lyc); [exact Etop|].
  apply (achain_push (e_ly e) (rdW (e_W e) (e_mem e))).
  + exact Hch.
  + lia.
  + intros a Ha. apply F1; [lia | lia |].
    intros (r & Hr & Hra). unfold vr_fp in Hr. apply in_app_or in Hr as [Hr|Hr].
    * unfold VERBS_RECEIVE_PG in Hr. unfold A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE, A_G_QUITTING in Hr.
      repeat (destruct Hr as [<-|Hr]; [cbn [fst snd] in Hra; lia|]). destruct Hr.
    * unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([p n] & <- & Hpn). cbn [fst snd] in Hra.
      pose proof (rec_repA_in_blocks B _ _ _ _ _ _ HrecE Hpn) as Hin.
      destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR0 Hin) as (_ & _ & Hc & _). lia.
  + pose proof (Hsv 0%nat 1 eq_refl) as H0. replace (vr_sp0 e - 8 - 8 * Z.of_nat 0) with (vr_sp0 e - 8) in H0 by lia.
    apply rdword_of_val_mem; [apply aval_val; exact H0 | apply bv_unsigned_in_range].
  + pose proof (Hsv 1%nat 8 eq_refl) as H0. replace (vr_sp0 e - 8 - 8 * Z.of_nat 1) with (vr_sp0 e - 16) in H0 by lia.
    apply rdword_of_val_mem; [apply aval_val; exact H0 | apply bv_unsigned_in_range].
  + exact Hra4.
  + lia.
  + pose proof (Z.div_mod (vr_sp0 e) 16 ltac:(lia)) as Hdm. rewrite Hal in Hdm.
    rewrite Hdm, Z.add_0_r. replace (16 * (vr_sp0 e / 16)) with ((2 * (vr_sp0 e / 16)) * 8) by lia. apply Z_mod_mult.
  + lia.
  + lia.
- exists []. left. split; [right; left; rewrite Etop; lia | reflexivity].
Qed.

(* Carrying a boundary state over a program call (cl_callS_wide): the callee's journal keeps the real frame above
   its window, the side-stack frame, the blocks it neither frees nor holds in its footprint, and the image bytes no
   runtime owns; the recorder's state after the call is the callee's post *)
Lemma c07_call : forall e pos F q c tp tmps tmps' rl rl' Rc Rc' Oc Oc' qv k k' kmax kmax' nm nm' nmax nmax'
  lyc Sc Wc regsc memc mdc ly2 S2 W2 regs2 mem2 md2 STK1 FP1 EV1,
vr_core B MT e pos F tmps vr_sh2 (vr_sl3 F q c) rl Rc Oc qv k kmax nm nmax lyc Sc Wc regsc memc mdc ->
vr_line B e q Wc memc -> vr_copy B e F c tp Wc memc ->
ajournal SEGS B VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e)
  [(4, pos)] ly2 S2 W2 mem2 md2 k' ->
ajournal SEGS B STK1 (vr_s1 e) FP1 lyc Sc Wc memc mdc [] ly2 S2 W2 mem2 md2 EV1 ->
vr_sp0 e - VERBS_RECEIVE_STK <= vr_s1 e - STK1 ->
(forall a, inFP FP1 a -> (A_G_REC <= a < A_G_REC + REC_SIZE) \/ (A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE) \/
   exists b n, In (b, n) Oc /\ b <= a < b + req_size n) ->
(forall pn, In pn (ablocks B lyc Sc) -> ~ In pn Oc -> In pn (ablocks B ly2 S2)) ->
In (vr_lb e q) tmps -> In (vr_cb e c) tmps -> Z.of_nat (length (e_D e)) = e_n e ->
k' <= kmax' -> vr_meter MT e S2 k' nm' -> nm' <= nmax' ->
vr_rv regs2 (vr_base B e ++ rl') ->
rec_repA B ly2 S2 (rdW W2 mem2) Rc' Oc' -> ~ In (e_data e, Z.max (e_n e) 1) Oc' ->
Permutation (ablocks B ly2 S2) (Oc' ++ tmps' ++ e_rest e) ->
vr_core B MT e pos F tmps' vr_sh2 (vr_sl3 F q c) rl' Rc' Oc' qv k' kmax' nm' nmax' ly2 S2 W2 regs2 mem2 md2 /\
vr_line B e q W2 mem2 /\ vr_copy B e F c tp W2 mem2.
Proof.
intros e pos F q c tp tmps tmps' rl rl' Rc Rc' Oc Oc' qv k k' kmax kmax' nm nm' nmax nmax'
  lyc Sc Wc regsc memc mdc ly2 S2 W2 regs2 mem2 md2 STK1 FP1 EV1
  Hcore Hline Hcopy HJ' HJ1 HSTK1 HFP1 Hsurv Hlb Hcb HDn Hk' Hm' Hnm' Hrv' Hrec' Hd' Hperm'.
destruct Hcore as (HJ & Hk & Hm & Hnm & Hfr & Hrv & Hsv & Hsp & Henv & Hrec & Hd & Hperm & Hq).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & Hstatic & _).
pose proof Hstatic as (Hal & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof HJ1 as (HAR2 & Hly2 & _ & _ & _ & Hfrs2 & _ & _ & G1 & G2 & G3 & G4 & _).
pose proof Hly2 as (_ & _ & _ & _ & _ & EF & _).
pose proof vr_stk_ge as [Hstk4 Hstk5]. unfold ESTACK, ASTACK in *.
destruct (vr_s1_bounds e Hal) as [Hs1 _].
pose proof (pal_env B TL) as ((He0 & He1) & Heimg & _).
destruct Hfr as (HF & Hflag & Hsh).
assert (Hin4 : In (4, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS lyc Sc Wc memc mdc 4 pos HAR Hin4) as (HF0 & HF1 & _).
rewrite <- HF in HF0, HF1. change (fs_frame_bytes 4) with 1024 in HF1.
assert (HF8 : 0 <= F / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
assert (Hpgimg : forall a, (A_G_REC <= a < A_G_REC + REC_SIZE) \/ (A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE) -> in_img SEGS a).
{ intros a Ha. apply (PROGU a). unfold cmd_PG, A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in *.
  destruct Ha as [Ha|Ha]; [exists (0x5e3740, 0x5e3740 + 960) | exists (0x5e3be0, 0x5e3be0 + 56)];
  (split; [cbn; tauto | cbn [fst snd]; lia]). }
assert (Hnf_ceil : forall a, alloc_ceiling <= a -> ~ inFP FP1 a).
{ intros a Ha Hf. destruct (HFP1 a Hf) as [Hg | [Hg | (b & n & Hbn & Hb)]].
  - pose proof (pa_segs_low a (Hpgimg a (or_introl Hg))). lia.
  - pose proof (pa_segs_low a (Hpgimg a (or_intror Hg))). lia.
  - destruct (al_blocks _ _ LAWS _ _ _ _ _ b n HAR (rec_repA_in_blocks B _ _ _ _ _ _ Hrec Hbn)) as (_ & _ & Hc & _). lia. }
assert (Hnf_frame : forall a, (F <= a < F + 1024) \/ (shadow_addr F <= a < shadow_addr F + 128) -> ~ inFP FP1 a).
{ intros a Ha Hf. destruct (HFP1 a Hf) as [Hg | [Hg | (b & n & Hbn & Hb)]].
  - destruct Ha as [Ha|Ha].
    + apply (frm_img SEGS B LAWS lyc Sc Wc memc mdc 4 pos a HAR Hin4); [rewrite <- HF; exact Ha | exact (Hpgimg a (or_introl Hg))].
    + pose proof (pa_segs_low a (Hpgimg a (or_introl Hg))). unfold shadow_addr, SHADOW_OFF in Ha. unfold kLowMemEnd in *. lia.
  - destruct Ha as [Ha|Ha].
    + apply (frm_img SEGS B LAWS lyc Sc Wc memc mdc 4 pos a HAR Hin4); [rewrite <- HF; exact Ha | exact (Hpgimg a (or_intror Hg))].
    + pose proof (pa_segs_low a (Hpgimg a (or_intror Hg))). unfold shadow_addr, SHADOW_OFF in Ha. unfold kLowMemEnd in *. lia.
  - pose proof (rec_repA_in_blocks B _ _ _ _ _ _ Hrec Hbn) as Hin.
    destruct (al_blocks _ _ LAWS _ _ _ _ _ b n HAR Hin) as (_ & Hb4 & Hbc & Happ & _ & _ & Hn).
    pose proof (req_size_pos n ltac:(lia)) as [Hr1 _].
    destruct Ha as [Ha|Ha].
    + pose proof (sep_block_frame SEGS B LAWS lyc Sc Wc memc mdc b n 4 pos HAR Hin Hin4) as Hdj.
      unfold zdisjoint in Hdj. cbn [fst snd] in Hdj. rewrite <- HF in Hdj. change (fs_frame_bytes 4) with 1024 in Hdj. lia.
    + pose proof (shadow_addr_bounds F ltac:(unfold kHighMemEnd; lia)) as [SBlo _].
      pose proof (shadow_addr_bounds (F + 1024) ltac:(unfold kHighMemEnd; lia)) as [_ SBhi].
      pose proof (shadow_range_end F 1024 ltac:(lia)) as SRE. change (1024 / 8) with 128 in SRE.
      unfold in_app, kLowShadowBeg, kHighMemBeg, kLowMemEnd, kHighShadowEnd, ASAN_CEIL in *. lia. }
assert (Hblk2 : forall p n, In (p, n) (ablocks B lyc Sc) -> ~ In (p, n) Oc -> forall a, p <= a < p + n ->
  rdW W2 mem2 a = rdW Wc memc a).
{ intros p n Hpn Hno a Ha. pose proof (Hsurv _ Hpn Hno) as Hpn2.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR Hpn) as (_ & _ & _ & _ & _ & _ & Hn).
  pose proof (req_size_pos n ltac:(lia)) as [_ Hrq].
  replace a with (p + (a - p)) by lia. apply (G2 p n (a - p) Hpn Hpn2 ltac:(lia)).
  intros Hf. destruct (HFP1 _ Hf) as [Hg | [Hg | (b & m & Hbm & Hb)]].
  - exact (blk_img SEGS B LAWS lyc Sc Wc memc mdc p n (p + (a - p)) HAR Hpn ltac:(lia) (Hpgimg _ (or_introl Hg))).
  - exact (blk_img SEGS B LAWS lyc Sc Wc memc mdc p n (p + (a - p)) HAR Hpn ltac:(lia) (Hpgimg _ (or_intror Hg))).
  - assert (Hne : (b, m) <> (p, n)) by (intros E; rewrite E in Hbm; exact (Hno Hbm)).
    pose proof (sep_blocks SEGS B LAWS lyc Sc Wc memc mdc b m p n HAR (rec_repA_in_blocks B _ _ _ _ _ _ Hrec Hbm) Hpn Hne) as Hdj.
    unfold zdisjoint in Hdj. cbn [fst snd] in Hdj. lia. }
assert (Hfr2 : forall a, F <= a < F + 1024 -> rdW W2 mem2 a = rdW Wc memc a).
{ intros a Ha. apply (G4 4 pos a Hin4); [left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite <- HF; change (fs_frame_bytes 4) with 1024; lia|].
  apply Hnf_frame. left. exact Ha. }
assert (Hsh2 : forall a, shadow_addr F <= a < shadow_addr F + 128 -> rdW W2 mem2 a = rdW Wc memc a).
{ intros a Ha. apply (G4 4 pos a Hin4); [right; unfold in_zr; cbn [fst snd]; rewrite <- HF; change (fs_frame_bytes 4 / 8) with 128; lia|].
  apply Hnf_frame. right. exact Ha. }
assert (Hstk2 : forall a, vr_s1 e <= a < vr_sp0 e -> rdW W2 mem2 a = rdW Wc memc a).
{ intros a Ha. apply G1; [lia | lia | apply Hnf_ceil; lia]. }
assert (Hsink : ~ YI16.sink_open_fp FP1).
{ intros (r & Hr & H0). destruct (HFP1 0 (ex_intro _ r (conj Hr H0))) as [Hg | [Hg | (b & n & Hbn & Hb)]].
  - unfold A_G_REC in Hg. lia.
  - unfold A_REC_SPILL in Hg. lia.
  - destruct (al_blocks _ _ LAWS _ _ _ _ _ b n HAR (rec_repA_in_blocks B _ _ _ _ _ _ Hrec Hbn)) as (_ & Hb4 & _). lia. }
assert (Hbl : forall b, In b tmps -> In b (ablocks B lyc Sc)).
{ intros b Hb. apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. right. apply in_or_app. left. exact Hb. }
assert (Haro : arodata_okP SEGS RLO RHI B (rdW W2 mem2)).
{ destruct Henv as (Haro & _). intros a Hro Ho He.
  assert (Hi : in_img SEGS a) by (destruct Hro as [(s & Hs & _ & Hr) | Hr]; [exists s; split; [exact Hs | exact Hr] | exact (RRO a Hr)]).
  rewrite (G3 a Hi Ho He); [exact (Haro a Hro Ho He)|].
  apply fp_spares_closed; [exact Hsink|]. intros Hf. destruct (HFP1 a Hf) as [Hg | [Hg | (b & n & Hbn & Hb)]].
  - apply (RPG a); [|exact Hro]. exists (A_G_REC, A_G_REC + 960). split; [left; reflexivity | unfold REC_SIZE in Hg; cbn [fst snd]; lia].
  - apply (RPG a); [|exact Hro]. exists (A_REC_SPILL, A_REC_SPILL + 56). split; [right; left; reflexivity | unfold SC_SIZE in Hg; cbn [fst snd]; lia].
  - exact (blk_img SEGS B LAWS lyc Sc Wc memc mdc b n a HAR (rec_repA_in_blocks B _ _ _ _ _ _ Hrec Hbn) Hb Hi). }
destruct (RECC ly2 S2 W2 mem2 md2 HAR2) as (Hfl & Hag & Hev).
pose proof (ROA ly2 S2 W2 mem2 md2 HAR2 Haro) as Hro.
assert (Hlbno : ~ In (vr_lb e q) Oc) by exact (perm_tmp_notin _ _ _ _ _ _ _ _ _ HAR Hperm Hlb).
assert (Hcbno : ~ In (vr_cb e c) Oc) by exact (perm_tmp_notin _ _ _ _ _ _ _ _ _ HAR Hperm Hcb).
split; [|split].
- split; [exact HJ'|]. split; [exact Hk'|]. split; [exact Hm'|]. split; [exact Hnm'|].
  split.
  { split; [unfold frame_addr in *; rewrite EF; exact HF|]. split.
    - unfold flag_addr in *. rewrite EF. rewrite (rdword_ext (rdW Wc memc) (rdW W2 mem2)); [exact Hflag|].
      intros j Hj. apply Hfr2. lia.
    - intros i Hi. rewrite Hsh2; [exact (Hsh i Hi) | lia]. }
  split; [exact Hrv'|].
  split.
  { intros j r Hj. apply (aval_mem_agree _ _ _ 8 _ (Hsv j r Hj)). intros kk Hkk.
    assert (Hj' : (j < length vr_saved_regs)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
    change (length vr_saved_regs) with 13%nat in Hj'. change (Z.of_nat 8) with 8 in Hkk.
    apply Hstk2. lia. }
  split.
  { unfold vr_spill in *. rewrite Forall_forall in Hsp |- *. intros ov Hov. specialize (Hsp ov Hov).
    apply (aval_mem_agree _ _ _ 8 _ Hsp). intros kk Hkk. change (Z.of_nat 8) with 8 in Hkk. apply Hstk2.
    assert (Hov' : 0 <= fst ov <= 72).
    { unfold vr_sl3 in Hov. repeat (destruct Hov as [<-|Hov]; [cbn; lia|]). destruct Hov. }
    lia. }
  split.
  { split; [exact Haro|]. split; [exact (got_of_ro _ Hro)|]. split; [exact Hro|].
    split; [exact Hag|]. split; [exact Hfl | exact Hev]. }
  split; [exact Hrec'|]. split; [exact Hd'|]. split; [exact Hperm'|].
  apply (aval_mem_agree _ _ _ 4 _ Hq). intros kk Hkk. change (Z.of_nat 4) with 4 in Hkk.
  assert (Hpq : inFP cmd_PG (A_G_QUITTING + kk)).
  { exists (A_G_QUITTING, A_G_QUITTING + 4). split; [right; right; left; reflexivity | cbn [fst snd]; lia]. }
  destruct (PROGU _ Hpq) as (Hi & Ho & He).
  apply (G3 _ Hi Ho He). apply fp_spares_closed; [exact Hsink|]. intros Hf.
  destruct (HFP1 _ Hf) as [Hg | [Hg | (b & n & Hbn & Hb)]].
  + unfold A_G_REC, REC_SIZE, A_G_QUITTING in *. lia.
  + unfold A_REC_SPILL, SC_SIZE, A_G_QUITTING in *. lia.
  + exact (blk_img SEGS B LAWS lyc Sc Wc memc mdc b n _ HAR (rec_repA_in_blocks B _ _ _ _ _ _ Hrec Hbn) Hb Hi).
- destruct Hline as [Hfq Hstr]. split; [exact Hfq|].
  apply (astr_atR_agree _ _ _ _ (vr_l (e_n e) (e_D e) + 1) Hstr).
  + pose proof (line_le_l (e_D e) (e_n e) HDn). lia.
  + intros kk Hkk. apply (Hblk2 q (vr_l (e_n e) (e_D e) + 1)); [exact (Hbl _ Hlb) | exact Hlbno | lia].
- destruct Hcopy as [Hfc Htk]. split; [exact Hfc|].
  apply (atoks_atA_agree _ _ _ _ _ _ _ Htk).
  + intros kk Hkk. pose proof (proj1 (proj2 Htk)) as Hlt. rewrite Hlt in Hkk. pose proof (toks_le_64 (e_D e)).
    apply Hfr2. lia.
  + intros kk Hkk. apply (Hblk2 c (Z.of_nat (length (PV.line (e_D e))) + 1)); [exact (Hbl _ Hcb) | exact Hcbno | lia].
Qed.
End e.

End f.
End d.

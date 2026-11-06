(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK11 YK0i YK0j YK1b YK0s YK15 YN06
YQ0j YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ07 YQ08 YO3v.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YI00 YI02 YI08 YI0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Lemma mbyte_of_frame_g : forall segs E rs (m m' : word -> option byte) a,
frame_of E rs m m' -> 0 <= a < 2 ^ 64 ->
(forall r, In r rs -> ~ (base_val E (r_base r) + r_wlo r <= a < base_val E (r_base r) + r_whi r)) ->
mbyte segs m' a = mbyte segs m a.
Proof.
intros segs E rs m m' a HF Ha Hout. unfold mbyte. rewrite HF; [reflexivity|].
rewrite unsigned_lit_small by exact Ha. intros (r & Hin & Hr). exact (Hout r Hin Hr).
Qed.
Ltac nat_lt_lit_g := apply (proj1 (Nat.ltb_lt _ _)); reflexivity.
Ltac ew_havocG := repeat (rewrite ew_havoc_old; [|nat_lt_lit_g]).
Ltac mb_frame_g HF rng win :=
lazymatch type of HF with frame_of ?E ?rs ?m ?m' =>
rewrite (mbyte_of_frame_g _ E rs m m' _ HF); [ | rng |
let r := fresh "r" in let Hr := fresh "Hr" in
intros r Hr; cbv [In] in Hr;
repeat (destruct Hr as [<- | Hr]; [cbn [r_base r_wlo r_whi base_val]; ew_havocG; win |]);
[ .. | destruct Hr ] ]
end.
Ltac frame_chain HF HF1 HF2 :=
lazymatch type of HF with frame_of ?E ?rs ?m0 ?m1 =>
lazymatch type of HF1 with frame_of _ ?rs1 _ ?m2 =>
assert (HF2 : frame_of E rs m0 m2)
by (apply (frame_of_trans E rs rs1 m0 m1 m2); [vm_compute; reflexivity | exact HF | exact HF1])
end end.
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section J.
Variable B : malloc_syms.
Variable MR : MR_t.
Lemma stack_ok_stk_le : forall STK STK' sp mem,
stack_ok B STK' sp mem -> 0 <= STK <= STK' -> stack_ok B STK sp mem.
Proof.
intros STK STK' sp mem (Hal & H0 & Hceil & H63 & Hw) Hle.
split; [exact Hal|]. split; [lia|]. split; [lia|]. split; [exact H63|].
intros a Ha. apply Hw. lia.
Qed.
Lemma fn_pre_stk_le : forall STK STK' L A regs mem md,
fn_pre B MR STK' L A regs mem md -> 0 <= STK <= STK' -> fn_pre B MR STK L A regs mem md.
Proof.
intros STK STK' L A regs mem md (HH & Hra & Hst & Htp & Herr) Hle.
split; [exact HH|]. split; [exact Hra|]. split; [| split; [exact Htp | exact Herr]].
eapply stack_ok_stk_le; [exact Hst | exact Hle].
Qed.
Lemma journal_stk_le : forall STK STK' sp0 FP L A mem md L' A' mem' md',
journal B MR STK sp0 FP L A mem md L' A' mem' md' -> STK <= STK' -> stack_ok B STK' sp0 mem ->
journal B MR STK' sp0 FP L A mem md L' A' mem' md'.
Proof.
intros STK STK' sp0 FP L A mem md L' A' mem' md'
(HH & Hvm & Hhigh & Hblk & Hgone & (Hal & Hstk0 & Hceil & H63 & Hstw) & Herr & Himg) Hle
(_ & Hstk0' & Hceil' & _ & Hstw').
split; [exact HH|]. split; [exact Hvm|]. split.
{ intros a Ha Hna. apply Hhigh; [exact Ha | lia]. }
split; [exact Hblk|]. split; [exact Hgone|]. split.
{ split; [exact Hal|]. split; [exact Hstk0'|]. split; [exact Hceil'|]. split; [exact H63|].
intros a Ha. destruct (Z_lt_le_dec a (sp0 - STK)) as [Hb|Hb].
- apply (proj1 (proj2 (Hhigh a ltac:(lia) ltac:(lia)))). apply Hstw'. exact Ha.
- apply Hstw. lia. }
split; [exact Herr | exact Himg].
Qed.
Lemma heap_sep_app2 : MR_laws B MR -> forall L A mem md (l1 l2 : list (Z * Z)) x y,
heap_ok MR L A mem md -> Permutation (blocks L A) (l1 ++ l2) -> In x l1 -> In y l2 ->
fst x + snd x <= fst y \/ fst y + snd y <= fst x.
Proof.
intros LAWS L A mem md l1 l2 x y HH HP Hx Hy. destruct (in_split _ _ Hx) as (a & b & ->).
apply (heap_sep_perm _ _ LAWS L A mem md x (a ++ b ++ l2) y HH).
- eapply Permutation_trans; [exact HP|]. rewrite <- app_assoc. cbn [app]. apply Permutation_sym.
replace (a ++ b ++ l2) with (a ++ (b ++ l2)) by reflexivity. apply Permutation_middle.
- apply in_app_iff. right. apply in_app_iff. right. exact Hy.
Qed.
End J.

Section JF.
Variable B : malloc_syms.
Variable MR : MR_t.
Hypothesis LAWS : MR_laws B MR.
Hypothesis IMG : img_laws B MR.
Variable tbl : ctable.
Hypothesis tbl_ok : table_ok (ms_segs B) tbl.
Local Notation segs := (ms_segs B).
Lemma SR_runF_J : forall n E ss ss' st ms STK sp0 FP L A mem md Lc Ac mdc Q,
st_okF segs E ss ms ->
sym_runFN segs tbl n ss = (ss', st) ->
match st with RS_ecall => False | _ => True end ->
journal B MR STK sp0 FP L A mem md Lc Ac (ms_mem ms) mdc ->
wr_ok E (ss_mem ss) STK sp0 FP (blocks L A) (blocks Lc Ac) ->
(forall ms', st_okF segs E ss' ms' -> journal B MR STK sp0 FP L A mem md Lc Ac (ms_mem ms') mdc ->
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') -> mem_grows (ms_mem ms) (ms_mem ms') ->
SR segs (mkCfg ms' mdc) Q) ->
SR segs (mkCfg ms mdc) Q.
Proof.
intros n E ss ss' st ms STK sp0 FP L A mem md Lc Ac mdc Q HS Hrun Hst HJ Hwr Hk.
destruct (msteps_runF_gen segs tbl tbl_ok n E ss ss' st ms HS Hrun) as (ms' & Hms & HS' & Hfr).
destruct (heap_model B MR LAWS _ _ _ _ (proj1 HJ)) as (Hh & Hl & _).
apply (SR_msteps segs ms ms' mdc Q Hh Hl Hms). apply Hk.
- destruct st; [exact HS' | destruct Hst | exact HS'].
- eapply (journal_exec B MR LAWS IMG); [exact HJ | exact Hfr | apply (msteps_mem_grows segs); exact Hms | exact Hwr].
- exact Hfr.
- apply (msteps_mem_grows segs). exact Hms.
Qed.
Lemma SR_runF_to_J : forall n stop E ss ss' st ms STK sp0 FP L A mem md Lc Ac mdc Q,
st_okF segs E ss ms ->
sym_run_toFN segs tbl n stop ss = (ss', st) ->
match st with RS_ecall => False | _ => True end ->
journal B MR STK sp0 FP L A mem md Lc Ac (ms_mem ms) mdc ->
wr_ok E (ss_mem ss) STK sp0 FP (blocks L A) (blocks Lc Ac) ->
(forall ms', st_okF segs E ss' ms' -> journal B MR STK sp0 FP L A mem md Lc Ac (ms_mem ms') mdc ->
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') -> mem_grows (ms_mem ms) (ms_mem ms') ->
SR segs (mkCfg ms' mdc) Q) ->
SR segs (mkCfg ms mdc) Q.
Proof.
intros n stop E ss ss' st ms STK sp0 FP L A mem md Lc Ac mdc Q HS Hrun Hst HJ Hwr Hk.
destruct (msteps_runF_to_gen segs tbl tbl_ok n stop E ss ss' st ms HS Hrun) as (ms' & Hms & HS' & Hfr).
destruct (heap_model B MR LAWS _ _ _ _ (proj1 HJ)) as (Hh & Hl & _).
apply (SR_msteps segs ms ms' mdc Q Hh Hl Hms). apply Hk.
- destruct st; [exact HS' | destruct Hst | exact HS'].
- eapply (journal_exec B MR LAWS IMG); [exact HJ | exact Hfr | apply (msteps_mem_grows segs); exact Hms | exact Hwr].
- exact Hfr.
- apply (msteps_mem_grows segs). exact Hms.
Qed.
Lemma wr_ok_cons_win : forall E r rs STK sp0 FP bl0 blc n b,
r_base r = Some n -> bv_unsigned (ew E n) = b ->
sp0 - STK <= b + r_wlo r -> b + r_whi r <= sp0 ->
wr_ok E rs STK sp0 FP bl0 blc -> wr_ok E (r :: rs) STK sp0 FP bl0 blc.
Proof.
intros E r rs STK sp0 FP bl0 blc n b Hb Hn Hlo Hhi H a (r' & [<-|Hin] & Ha).
- left. rewrite Hb in Ha. cbn [base_val] in Ha. rewrite Hn in Ha. lia.
- apply H. exists r'. auto.
Qed.
End JF.
Section g.
Variable segs : list Segment.
Variable tbl : ctable.
Hypothesis tbl_ok : table_ok segs tbl.
Lemma pure_stretch_to : forall n stop E ss ss' st ms,
st_ok segs E ss ms -> sym_run_toN segs tbl n stop ss = (ss', st) ->
match st with RS_ecall => False | _ => True end ->
all_ro (ss_mem ss) = true -> ss_resv ss' = None ->
exists regs', msteps segs ms (mkst regs' (Z_to_bv 64 (ss_pc ss')) (ms_mem ms) (seg_rom segs)) /\
st_ok segs E ss' (mkst regs' (Z_to_bv 64 (ss_pc ss')) (ms_mem ms) (seg_rom segs)).
Proof.
intros n stop E ss ss' st ms HS Hrun Hst Hro Hrv.
destruct (pure_run_to segs tbl tbl_ok n stop E ss ss' st ms ms (ms_mem ms) HS Hrun Hst Hro (mst_refl _ _) ltac:(intros; reflexivity))
as (ms' & HS' & Hms & Hmem).
assert (Hm : ms_mem ms' = ms_mem ms) by (apply FunctionalExtensionality.functional_extensionality; exact Hmem).
pose proof (st_ok_mkst segs E ss' ms' HS' Hrv) as Hshape. rewrite Hm in Hshape.
exists (ms_regs ms'). rewrite <- Hshape. split; [exact Hms | exact HS'].
Qed.
Lemma pure_stretchF_to : forall n stop E ss ss' st ms,
st_okF segs E ss ms -> sym_run_toFN segs tbl n stop ss = (ss', st) ->
match st with RS_ecall => False | _ => True end ->
all_ro (ss_mem ss) = true -> ss_resv ss' = None ->
exists ms', msteps segs ms ms' /\ st_okF segs E ss' ms' /\ ms_mem ms' = ms_mem ms /\
ms' = @mkst (fp_of ms') (ms_regs ms') (Z_to_bv 64 (ss_pc ss')) (ms_mem ms) (seg_rom segs).
Proof.
intros n stop E ss ss' st ms HS Hrun Hst Hro Hrv.
destruct (msteps_runF_to_gen segs tbl tbl_ok n stop E ss ss' st ms HS Hrun) as (ms' & Hms & HS' & Hfr).
assert (HS'' : st_okF segs E ss' ms') by (destruct st; [exact HS' | destruct Hst | exact HS']).
assert (Hm : ms_mem ms' = ms_mem ms).
{ apply FunctionalExtensionality.functional_extensionality. intros x. apply (frame_of_ro E _ _ _ Hro Hfr). }
exists ms'. split; [exact Hms|]. split; [exact HS''|]. split; [exact Hm|].
rewrite <- Hm. exact (st_okF_mkst segs E ss' ms' HS'' Hrv).
Qed.
Lemma pure_stretchF : forall n E ss ss' st ms,
st_okF segs E ss ms -> sym_runFN segs tbl n ss = (ss', st) ->
match st with RS_ecall => False | _ => True end ->
all_ro (ss_mem ss) = true -> ss_resv ss' = None ->
exists ms', msteps segs ms ms' /\ st_okF segs E ss' ms' /\ ms_mem ms' = ms_mem ms /\
ms' = @mkst (fp_of ms') (ms_regs ms') (Z_to_bv 64 (ss_pc ss')) (ms_mem ms) (seg_rom segs).
Proof.
intros n E ss ss' st ms HS Hrun Hst Hro Hrv.
destruct (msteps_runF_gen segs tbl tbl_ok n E ss ss' st ms HS Hrun) as (ms' & Hms & HS' & Hfr).
assert (HS'' : st_okF segs E ss' ms') by (destruct st; [exact HS' | destruct Hst | exact HS']).
assert (Hm : ms_mem ms' = ms_mem ms).
{ apply FunctionalExtensionality.functional_extensionality. intros x. apply (frame_of_ro E _ _ _ Hro Hfr). }
exists ms'. split; [exact Hms|]. split; [exact HS''|]. split; [exact Hm|].
rewrite <- Hm. exact (st_okF_mkst segs E ss' ms' HS'' Hrv).
Qed.
Lemma st_okF_pin_reg : forall E ss ms (r : reg) e,
st_okF segs E ss ms -> r <> 0%bv -> getr (ms_regs ms) r = sv_denot E e ->
st_okF segs E (mkSST (ss_pc ss) (sr_set (ss_regs ss) r e) (ss_fregs ss) (ss_mem ss) (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros E ss ms r e (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) Hr He.
unfold st_okF; cbn. repeat (split; [assumption|]). split; [apply regs_ok_pin; assumption|]. split; assumption.
Qed.
Lemma entry_st_ok_env : forall E pc sr (regs : bvmap 5 word) (rs : smem) (G : facts) mem,
regs_ok E sr regs ->
regions_wf rs = true ->
Forall (region_ok segs E mem) rs ->
pairwise_disjoint E rs ->
facts_ok E G ->
st_ok segs E (mkSS pc sr rs None G) (mkst regs (Z_to_bv 64 pc) mem (seg_rom segs)).
Proof.
intros E pc sr regs rs G mem Hsr Hwf Hrs Hpd HG.
unfold st_ok. cbn [ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_regs ms_mem mkst
ss_pc ss_regs ss_mem ss_resv ss_facts resv_denot].
repeat (split; [reflexivity|]). split; [exact Hsr|]. split; [| exact HG].
split; [exact Hwf|]. split; [exact Hrs | exact Hpd].
Qed.
Lemma pure_stretch_to_mkst : forall n stop E ss ss' st regs pc mem,
st_ok segs E ss (mkst regs pc mem (seg_rom segs)) -> sym_run_toN segs tbl n stop ss = (ss', st) ->
match st with RS_ecall => False | _ => True end ->
all_ro (ss_mem ss) = true -> ss_resv ss' = None ->
exists regs', msteps segs (mkst regs pc mem (seg_rom segs)) (mkst regs' (Z_to_bv 64 (ss_pc ss')) mem (seg_rom segs)) /\
st_ok segs E ss' (mkst regs' (Z_to_bv 64 (ss_pc ss')) mem (seg_rom segs)).
Proof. intros n stop E ss ss' st regs pc mem. apply (pure_stretch_to n stop E ss ss' st (mkst regs pc mem (seg_rom segs))). Qed.
End g.

Lemma regs_preserved_of_list : forall (regs0 regs2 : bvmap 5 word),
(forall r : reg, In r CALLEE_SAVED -> getr regs2 r = getr regs0 r) -> regs_preserved regs0 regs2.
Proof.
intros regs0 regs2 H r Hr. apply H. unfold callee_saved in Hr. cbv [CALLEE_SAVED In].
assert (H' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
repeat (destruct H' as [->|H']; [repeat (first [left; apply bv_eq; reflexivity | right])|]).
subst. repeat (first [left; apply bv_eq; reflexivity | right]).
Qed.
Lemma regs_preserved_in : forall (regs0 regs2 : bvmap 5 word) (r : reg),
regs_preserved regs0 regs2 -> In r CALLEE_SAVED -> getr regs2 r = getr regs0 r.
Proof.
intros regs0 regs2 r H Hr. cbv [CALLEE_SAVED In] in Hr.
repeat (destruct Hr as [<-|Hr];
[ lazymatch goal with |- getr _ ?rr = _ =>
let z := eval vm_compute in (bv_unsigned rr) in
exact (H z ltac:(unfold callee_saved; lia)) end |]).
destruct Hr.
Qed.
Lemma fregs_preserved_trans : forall f1 f2 f3,
fregs_preserved f1 f2 -> fregs_preserved f2 f3 -> fregs_preserved f1 f3.
Proof. intros f1 f2 f3 H1 H2 r Hr. rewrite (H2 r Hr). apply H1. exact Hr. Qed.

Definition FT_STK (h : Z) : Z := 16 * (h + 1) + ALLOC_STACK.

Lemma FT_STK_le_FREETREE : forall h, 0 <= h <= TREE_HMAX -> 0 <= FT_STK h <= FREETREE_STK.
Proof. intros h Hh. unfold FT_STK, FREETREE_STK, ALLOC_STACK, TREE_HMAX in *. lia. Qed.

Definition theight (t : tree) : Z := Z.of_nat (tree_height t).
Lemma theight_nonneg : forall t, 0 <= theight t.
Proof. intros t. unfold theight. lia. Qed.
Lemma theight_node_l : forall n l r, theight l + 1 <= theight (TNode n l r).
Proof. intros n l r. unfold theight. cbn [tree_height]. lia. Qed.
Lemma theight_node_r : forall n l r, theight r + 1 <= theight (TNode n l r).
Proof. intros n l r. unfold theight. cbn [tree_height]. lia. Qed.
Lemma tnode_mean3 : forall n, length (tn_mean n) = 3%nat ->
exists m0 m1 m2, n = mkTN (tn_addr n) [m0; m1; m2] (tn_imin n) (tn_imax n) (tn_cut n) (tn_cidx n).
Proof.
intros [a mean imin imax cut cidx] Hl. cbn in *.
destruct mean as [|m0 [|m1 [|m2 [|x l]]]]; cbn in Hl; try discriminate.
exists m0, m1, m2. reflexivity.
Qed.
Lemma node_vals_expand : forall c0 c1 n leaf, length (tn_mean n) = 3%nat ->
node_vals c0 c1 n leaf =
[c0; c1; nth 0 (tn_mean n) 0; nth 1 (tn_mean n) 0; nth 2 (tn_mean n) 0; tn_imin n; tn_imax n; tn_cut n; tn_cidx n; leaf].
Proof.
intros c0 c1 [a mean imin imax cut cidx] leaf Hl. cbn in *.
destruct mean as [|m0 [|m1 [|m2 [|x l]]]]; cbn in Hl; try discriminate. reflexivity.
Qed.
Lemma tree_blocks_in_nodes : forall t b, In b (tree_blocks t) <-> exists n, In n (tree_nodes t) /\ b = (tn_addr n, NODE_SIZE).
Proof.
intros t b. rewrite tree_blocks_nodes, in_map_iff. split.
- intros (n & <- & Hin). exists n. auto.
- intros (n & Hin & ->). exists n. auto.
Qed.


End d.
Ltac jrunF LAWS tblok HS HJ :=
lazymatch type of HS with
| st_okF ?segs ?E ?ss ?ms =>
lazymatch type of tblok with
| table_ok _ ?tbl =>
let r := eval vm_compute in (sym_runFN segs tbl FUEL ss) in
lazymatch r with
| (?ss', ?st) =>
let Hrun := fresh "Hrun" in
assert (Hrun : sym_runFN segs tbl FUEL ss = (ss', st)) by (vm_compute; reflexivity);
let ms' := fresh "ms" in
let IMG := lazymatch goal with IMG : img_laws _ _ |- _ => IMG end in
eapply (SR_runF_J _ _ LAWS IMG _ tblok FUEL E ss ss' st ms _ _ _ _ _ _ _ _ _ _ _ HS Hrun I HJ);
clear Hrun;
[ | clear HS HJ;
try match type of ms with machine_state => clear ms | _ => idtac end;
let HF := fresh "HF" in let HG := fresh "HG" in
intros ms' HS HJ HF HG;
lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 =>
let rsv := eval vm_compute in rs in change (frame_of E1 rsv m1 m2) in HF end ]
end
end
end.
Ltac jrunF_to LAWS tblok HS HJ stop :=
lazymatch type of HS with
| st_okF ?segs ?E ?ss ?ms =>
lazymatch type of tblok with
| table_ok _ ?tbl =>
let r := eval vm_compute in (sym_run_toFN segs tbl FUEL stop ss) in
lazymatch r with
| (?ss', ?st) =>
let Hrun := fresh "Hrun" in
assert (Hrun : sym_run_toFN segs tbl FUEL stop ss = (ss', st)) by (vm_compute; reflexivity);
let ms' := fresh "ms" in
let IMG := lazymatch goal with IMG : img_laws _ _ |- _ => IMG end in
eapply (SR_runF_to_J _ _ LAWS IMG _ tblok FUEL stop E ss ss' st ms _ _ _ _ _ _ _ _ _ _ _ HS Hrun I HJ);
clear Hrun;
[ | clear HS HJ;
try match type of ms with machine_state => clear ms | _ => idtac end;
let HF := fresh "HF" in let HG := fresh "HG" in
intros ms' HS HJ HF HG;
lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 =>
let rsv := eval vm_compute in rs in change (frame_of E1 rsv m1 m2) in HF end ]
end
end
end.
Ltac jbranchF tbl HS :=
lazymatch type of HS with
| st_okF ?segs ?E ?ss ?ms =>
let why := sym_whyF segs tbl ss in
lazymatch why with
| SR_branch ?c ?a ?b =>
apply (SR_sym_branchF segs E ss ms _ _ c a b HS); clear HS;
let Hc := fresh "Hc" in intros Hc HS
| _ => fail "jbranchF: state is not stuck at a branch:" why
end
end.
Ltac pure_to tblok HS stop :=
lazymatch type of HS with
| st_ok ?segs ?E ?ss ?ms =>
lazymatch type of tblok with
| table_ok _ ?tbl =>
let r := eval vm_compute in (sym_run_toN segs tbl FUEL stop ss) in
lazymatch r with
| (?ss', ?st) =>
let Hrun := fresh "Hrun" in
assert (Hrun : sym_run_toN segs tbl FUEL stop ss = (ss', st)) by (vm_compute; reflexivity);
let regs' := fresh "regs" in let Hms := fresh "Hms" in let HS' := fresh "HS'" in
first
[ lazymatch ms with
| @mkst ?f ?regs ?pc ?mem _ =>
destruct (@pure_stretch_to_mkst f segs tbl tblok FUEL stop E ss ss' st regs pc mem HS Hrun I
ltac:(vm_compute; reflexivity) ltac:(reflexivity)) as (regs' & Hms & HS')
end
| destruct (pure_stretch_to segs tbl tblok FUEL stop E ss ss' st ms HS Hrun I
ltac:(vm_compute; reflexivity) ltac:(reflexivity)) as (regs' & Hms & HS') ];
clear Hrun HS; rename HS' into HS; cbn [ss_pc] in Hms, HS
end
end
end.
Tactic Notation "jregF" constr(HS) constr(r) "as" ident(Hr) :=
lazymatch type of HS with
| st_okF ?segs ?E ?ss ?ms =>
pose proof (st_okF_reg segs E ss ms r HS) as Hr;
eval_sr_get_in Hr; cbn [sv_denot] in Hr;
repeat (rewrite ew_havoc_old in Hr; [|cbv; lia]);
rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned in Hr
end.
Ltac eval_sfr_get_in H :=
repeat match type of H with context [sfr_get ?a ?b] =>
let v := eval vm_compute in (sfr_get a b) in change (sfr_get a b) with v in H end.
Tactic Notation "jfregF" constr(HS) constr(r) "as" ident(Hr) :=
lazymatch type of HS with
| st_okF ?segs ?E ?ss ?ms =>
pose proof (st_okF_freg segs E ss ms r HS) as Hr;
eval_sfr_get_in Hr; cbn [sv_denot] in Hr;
repeat (rewrite ew_havoc_old in Hr; [|cbv; lia]);
rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned in Hr
end.
Ltac mb_frames rng win :=
repeat match goal with
| HF : frame_of _ _ ?m ?m' |- mbyte _ ?m' _ = _ => mb_frame_g HF rng win
end.
Ltac pureF_to tblok HS stop :=
lazymatch type of HS with
| st_okF ?segs ?E ?ss ?ms =>
lazymatch type of tblok with
| table_ok _ ?tbl =>
let r := eval vm_compute in (sym_run_toFN segs tbl FUEL stop ss) in
lazymatch r with
| (?ss', ?st) =>
let Hrun := fresh "Hrun" in
assert (Hrun : sym_run_toFN segs tbl FUEL stop ss = (ss', st)) by (vm_compute; reflexivity);
let ms' := fresh "ms" in let Hms := fresh "Hms" in let HS' := fresh "HS'" in
let Hmem := fresh "Hmem" in let Hsh := fresh "Hsh" in
destruct (pure_stretchF_to segs tbl tblok FUEL stop E ss ss' st ms HS Hrun I
ltac:(vm_compute; reflexivity) ltac:(reflexivity)) as (ms' & Hms & HS' & Hmem & Hsh);
clear Hrun HS; rename HS' into HS; cbn [ss_pc] in Hsh
end
end
end.
Ltac pureF tblok HS :=
lazymatch type of HS with
| st_okF ?segs ?E ?ss ?ms =>
lazymatch type of tblok with
| table_ok _ ?tbl =>
let r := eval vm_compute in (sym_runFN segs tbl FUEL ss) in
lazymatch r with
| (?ss', ?st) =>
let Hrun := fresh "Hrun" in
assert (Hrun : sym_runFN segs tbl FUEL ss = (ss', st)) by (vm_compute; reflexivity);
let ms' := fresh "ms" in let Hms := fresh "Hms" in let HS' := fresh "HS'" in
let Hmem := fresh "Hmem" in let Hsh := fresh "Hsh" in
destruct (pure_stretchF segs tbl tblok FUEL E ss ss' st ms HS Hrun I
ltac:(vm_compute; reflexivity) ltac:(reflexivity)) as (ms' & Hms & HS' & Hmem & Hsh);
clear Hrun HS; rename HS' into HS; cbn [ss_pc] in Hsh
end
end
end.

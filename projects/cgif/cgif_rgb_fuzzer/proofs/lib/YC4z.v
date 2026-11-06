(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK11 YK0s YK15.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YC04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YI1i YI08 YI0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB0z YF8z YC1d YC1a YC1b.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition rg_blk_kept (H H' : word -> bool) (m m' : word -> option byte) (b n : Z) : Prop :=
forall i, 0 <= i < n -> aview trasegs H' m' (b + i) = aview trasegs H m (b + i).

Lemma rg_blk_kept_trans : forall H1 H2 H3 (m1 m2 m3 : word -> option byte) b n,
rg_blk_kept H1 H2 m1 m2 b n -> rg_blk_kept H2 H3 m2 m3 b n -> rg_blk_kept H1 H3 m1 m3 b n.
Proof. intros H1 H2 H3 m1 m2 m3 b n K1 K2 i Hi. rewrite (K2 i Hi). apply K1. exact Hi. Qed.
Lemma rg_blk_kept_sub : forall H H' (m m' : word -> option byte) b n b' n',
rg_blk_kept H H' m m' b n -> b <= b' -> b' + n' <= b + n -> rg_blk_kept H H' m m' b' n'.
Proof. intros H H' m m' b n b' n' K Hlo Hhi i Hi. replace (b' + i) with (b + (b' - b + i)) by lia. apply K. lia. Qed.
Lemma rg_obj_at_blk_kept : forall H H' m m' p lay vals sz,
obj_at trasegs (mrestrict H m) p lay vals -> lay_inside lay sz = true -> rg_blk_kept H H' m m' p sz ->
obj_at trasegs (mrestrict H' m') p lay vals.
Proof.
intros H H' m m' p lay vals sz Ho Hl Hk. apply (obj_at_transport_range trasegs _ _ p lay vals sz Ho Hl).
intros i Hi. apply (mbyte_of_aview trasegs). apply Hk. exact Hi.
Qed.
Lemma rg_val_mem_blk_kept : forall H H' m m' b n a (k : nat) v,
val_mem trasegs (mrestrict H m) a k v -> rg_blk_kept H H' m m' b n -> b <= a -> a + Z.of_nat k <= b + n ->
val_mem trasegs (mrestrict H' m') a k v.
Proof.
intros H H' m m' b n a k v V K Hlo Hhi j Hj. rewrite <- (V j Hj).
apply (mbyte_of_aview trasegs). replace (a + Z.of_nat j) with (b + (a - b + Z.of_nat j)) by lia. apply K. lia.
Qed.
Lemma rg_lay_inside_CGIF : lay_inside LAY_CGIF 96 = true. Proof. vm_compute. reflexivity. Qed.
Lemma rg_lay_inside_Frame : lay_inside LAY_Frame 40 = true. Proof. vm_compute. reflexivity. Qed.
Lemma rg_lay_inside_Raw : lay_inside LAY_Raw 48 = true. Proof. vm_compute. reflexivity. Qed.
Lemma rg_tcgif_at_kept : forall H H' m m' g s1,
tcgif_at (mrestrict H m) g s1 -> rg_blk_kept H H' m m' g 96 -> rg_blk_kept H H' m m' (cg_raw s1) 48 ->
(forall f, In (Some f) (cg_frames s1) -> rg_blk_kept H H' m m' (fr_ptr f) 40) ->
tcgif_at (mrestrict H' m') g s1.
Proof.
intros H H' m m' g s1 (Hg & Hr & Hf) Kg Kr Kf. split; [|split].
- exact (rg_obj_at_blk_kept H H' m m' g LAY_CGIF _ 96 Hg rg_lay_inside_CGIF Kg).
- exact (rg_obj_at_blk_kept H H' m m' (cg_raw s1) LAY_Raw _ 48 Hr rg_lay_inside_Raw Kr).
- intros f Hin. exact (rg_obj_at_blk_kept H H' m m' (fr_ptr f) LAY_Frame _ 40 (Hf f Hin) rg_lay_inside_Frame (Kf f Hin)).
Qed.
Lemma rg_cgif_blocks_in_g : forall g s N, In (g, CGIF_SIZE) (cgif_blocks g s N).
Proof. intros. left. reflexivity. Qed.
Lemma rg_cgif_blocks_in_raw : forall g s N, In (cg_raw s, RAW_SIZE) (cgif_blocks g s N).
Proof. intros. right. left. reflexivity. Qed.
Lemma rg_frames_blocks_in : forall N fs f, In (Some f) fs -> In (fr_ptr f, FRAME_SIZE) (frames_blocks N fs).
Proof.
intros N fs f. induction fs as [|o fs IH]; intros H; [destruct H|].
destruct H as [-> | H]; cbn; [left; reflexivity|].
apply in_app_iff. right. apply IH. exact H.
Qed.
Lemma rg_cgif_blocks_in_frame : forall g s N f, In (Some f) (cg_frames s) -> In (fr_ptr f, FRAME_SIZE) (cgif_blocks g s N).
Proof. intros g s N f H. right. right. apply in_app_iff. right. apply rg_frames_blocks_in. exact H. Qed.
Lemma rg_tcgif_at_blocks_kept : forall (H H' : word -> bool) (m m' : word -> option byte) g s N,
tcgif_at (mrestrict H m) g s ->
(forall b sz, In (b, sz) (cgif_blocks g s N) -> rg_blk_kept H H' m m' b (req_size sz)) ->
tcgif_at (mrestrict H' m') g s.
Proof.
intros H H' m m' g s N Hat K.
apply (rg_tcgif_at_kept H H' m m' g s Hat).
- exact (K g CGIF_SIZE (rg_cgif_blocks_in_g g s N)).
- exact (K (cg_raw s) RAW_SIZE (rg_cgif_blocks_in_raw g s N)).
- intros f Hf. exact (K (fr_ptr f) FRAME_SIZE (rg_cgif_blocks_in_frame g s N f Hf)).
Qed.
Lemma rg_blk_kept_frame : forall E rs (H : word -> bool) (m m' : word -> option byte) b n,
frame_of E rs (mrestrict H m) (mrestrict H m') ->
(forall a, b <= a < b + n -> 0 <= a < 2 ^ 64 /\ ~ in_wrange E rs a) ->
rg_blk_kept H H m m' b n.
Proof.
intros E rs H m m' b n HF Hno i Hi. destruct (Hno (b + i) ltac:(lia)) as [Hr Hn].
apply (aview_eq_of trasegs). apply HF. rewrite unsigned_lit_small by lia. exact Hn.
Qed.
Lemma rg_optb_in : forall pa n, pa <> 0 -> In (pa, n) (optb pa n).
Proof. intros pa n Hp. unfold optb. rewrite (proj2 (Z.eqb_neq pa 0) Hp). left. reflexivity. Qed.
Lemma rg_trace0_of_ctx : forall (CTX U : list (list Z)) pc0 regs ch,
allb (fun sg => memZL (firstn kUnwindMax (pc0 :: flat_map (fun ra => if ra =? pc0 then [] else [ra]) sg)) U) CTX = true ->
In (raZ regs :: spine ch) CTX -> In (call_trace0 pc0 regs ch) U.
Proof.
intros CTX U pc0 regs ch Hall Hin. rewrite call_trace_of_spine. apply memZL_In.
exact (allb_In (fun sg => memZL (firstn kUnwindMax (pc0 :: flat_map (fun ra => if ra =? pc0 then [] else [ra]) sg)) U) CTX _ Hall Hin).
Qed.
Lemma rg_tree_at_kept : forall (H H' : word -> bool) (m m' : word -> option byte) t,
tree_at trasegs (mrestrict H m) t ->
(forall b sz, In (b, sz) (tree_blocks t) -> rg_blk_kept H H' m m' b (req_size sz)) ->
tree_at trasegs (mrestrict H' m') t.
Proof.
intros H H' m m'. induction t as [|n|n l IHl r IHr]; intros Hat K; cbn [tree_at] in *.
- exact I.
- destruct Hat as (Hn0 & Hlen & c0 & c1 & Ho). split; [exact Hn0|]. split; [exact Hlen|]. exists c0, c1.
apply (rg_obj_at_blk_kept H H' m m' (tn_addr n) LAY_Node _ NODE_SIZE Ho (proj1 lay_inside_Node)).
exact (K (tn_addr n) NODE_SIZE ltac:(left; reflexivity)).
- destruct Hat as (Hn0 & Hlen & Ho & Hl & Hr). split; [exact Hn0|]. split; [exact Hlen|]. split; [|split].
+ apply (rg_obj_at_blk_kept H H' m m' (tn_addr n) LAY_Node _ NODE_SIZE Ho (proj1 lay_inside_Node)).
exact (K (tn_addr n) NODE_SIZE ltac:(left; reflexivity)).
+ apply IHl; [exact Hl|]. intros b sz Hb. apply K. cbn [tree_blocks]. right. apply in_app_iff. left. exact Hb.
+ apply IHr; [exact Hr|]. intros b sz Hb. apply K. cbn [tree_blocks]. right. apply in_app_iff. right. exact Hb.
Qed.
Lemma rg_node_fields : forall m a c0 c1 n leaf,
length (tn_mean n) = 3%nat -> obj_at trasegs m a LAY_Node (node_vals c0 c1 n leaf) ->
val_mem trasegs m a 8 c0 /\ 0 <= c0 < 2 ^ 64 /\ val_mem trasegs m (a + 8) 8 c1 /\ 0 <= c1 < 2 ^ 64 /\
val_mem trasegs m (a + 50) 1 leaf /\ 0 <= leaf < 256.
Proof.
intros m a c0 c1 n leaf Hlen Ho. unfold node_vals in Ho.
destruct (tn_mean n) as [|m0 [|m1 [|m2 [|m3 l]]]]; try discriminate Hlen.
cbn [app obj_at LAY_Node] in Ho. unfold field_ok in Ho. cbn [fst snd N.to_nat Z.of_N Pos.to_nat] in Ho.
destruct Ho as ((V0 & R0) & (V8 & R8) & _ & _ & _ & _ & _ & _ & _ & (V50 & R50) & _).
rewrite Z.add_0_r in V0.
split; [exact V0|]. split; [exact R0|]. split; [exact V8|]. split; [exact R8|]. split; [exact V50|]. exact R50.
Qed.
Section d.
Variable B : asyms.
Hypothesis LAWS : AR_laws trasegs B.

Lemma rg_blk_kept_call : forall STK1 sp1 FP1 lyc Sc (W : world trasegs) memc mdc ly2 S2 W2 mem2 md2 k1 b n,
ajournal trasegs B STK1 sp1 FP1 lyc Sc W memc mdc [] ly2 S2 W2 mem2 md2 k1 ->
In (b, n) (ablocks B lyc Sc) -> In (b, n) (ablocks B ly2 S2) -> (forall i, 0 <= i < req_size n -> ~ inFP FP1 (b + i)) ->
rg_blk_kept (w_H W) (w_H W2) memc mem2 b (req_size n).
Proof.
intros STK1 sp1 FP1 lyc Sc W memc mdc ly2 S2 W2 mem2 md2 k1 b n HJ1 Hin Hin2 HnF i Hi.
pose proof HJ1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & G2 & _).
apply (G2 b n i Hin Hin2); [exact Hi | apply HnF; exact Hi].
Qed.
Lemma rg_sep_head_in : forall ly S W mem md x l y,
AR trasegs B ly S W mem md -> Permutation (ablocks B ly S) (x :: l) -> In y l ->
zdisjoint (block_rng x) (block_rng y).
Proof.
intros ly S W mem md x l y HAR HP Hy. apply in_split in Hy as (l1 & l2 & ->).
apply (sep_blocks_perm trasegs B LAWS ly S W mem md x y (l1 ++ l2) HAR).
eapply Permutation_trans; [exact HP|]. apply perm_skip. apply Permutation_sym. apply Permutation_middle.
Qed.
Lemma rg_sep_app_in : forall ly S W mem md l1 l2 x y,
AR trasegs B ly S W mem md -> Permutation (ablocks B ly S) (l1 ++ l2) -> In x l1 -> In y l2 ->
zdisjoint (block_rng x) (block_rng y).
Proof.
intros ly S W mem md l1 l2 x y HAR HP Hx Hy. apply in_split in Hx as (a1 & a2 & ->).
apply (rg_sep_head_in ly S W mem md x ((a1 ++ a2) ++ l2) y HAR).
- eapply Permutation_trans; [exact HP|]. rewrite <- app_assoc. cbn [app].
apply Permutation_sym. rewrite <- app_assoc. apply Permutation_middle.
- apply in_app_iff. right. exact Hy.
Qed.
Lemma rg_acall_kept_weaken : forall lyc Sc W memc W2 mem2 slo shi (E1 E2 : Z -> Prop),
(forall a, E1 a -> E2 a) ->
acall_kept trasegs B lyc Sc W memc W2 mem2 slo shi E1 -> acall_kept trasegs B lyc Sc W memc W2 mem2 slo shi E2.
Proof.
intros lyc Sc W memc W2 mem2 slo shi E1 E2 Himp (K1 & K2 & K3 & K4 & K5 & K6).
split; [exact K1|]. split; [intros b m i Hin Hi Hn; apply (K2 b m i Hin Hi); intros H1; apply Hn, Himp, H1|].
split; [exact K3|]. split; [intros cid pos a Hin Ha Hn; apply (K4 cid pos a Hin Ha); intros H1; apply Hn, Himp, H1|].
split; [exact K5 | exact K6].
Qed.
Hypothesis segs_low : forall a, in_img trasegs a -> 0 <= a < kLowMemEnd.
Hypothesis errno_low : api_env trasegs B.
Hypothesis ML : model_laws (as_universe B).
Lemma rg_aj_free_opt : afree_realizes trasegs B ->
forall W E ss ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k pa n (o : Z) spw raw ch rest,
st_ok trasegs E ss (restrict (w_H W) ms) -> ss_pc ss = pc_wrap_free (as_code B) -> ss_resv ss = None ->
ajournal trasegs B STK sp0 FP ly S W0 mem md own lyc Sc W (ms_mem ms) mdc k ->
Permutation (ablocks B lyc Sc) (optb pa n ++ rest) ->
getr (ms_regs ms) 10 = w64 pa ->
getr (ms_regs ms) 2 = sv_denot E (SOff 2 o) -> ew E 2 = spw -> bv_unsigned spw = sp0 ->
o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr (ms_regs ms) 3 = w64 (as_gp B) -> getr (ms_regs ms) 4 = w64 (as_tp B) ->
getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw ->
vev Sc < VEV_MAX ->
chain_pre lyc (aview trasegs (w_H W) (ms_mem ms)) (ms_regs ms) ch ->
In (call_trace0 (pc_free_ra0 (as_code B)) (ms_regs ms) ch) (as_universe B) ->
(pa <> 0 -> In (pa, n) (ablocks B ly S) -> forall i, 0 <= i < req_size n -> inFP FP (pa + i)) ->
SRr trasegs W (mkCfg ms mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom trasegs)) md2 /\
ajournal trasegs B STK sp0 FP ly S W0 mem md own ly2 S2 W2 mem2 md2 (k + 1) /\
aregs_preserved (ms_regs ms) regs2 /\
Permutation (ablocks B ly2 S2) rest /\
frames S2 = frames Sc /\
acall_kept trasegs B lyc Sc W (ms_mem ms) W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun a => pa <> 0 /\ pa <= a < pa + req_size n)).
Proof.
intros AFREE W E ss ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k pa n o spw raw ch rest
HS Hpc Hrv HJ HPerm Ha0 Hsp HE2 Hspw Hal Hneg Hbud Hgp Htp Hra Hraw Hev Hch Htr HFP.
unfold optb in HPerm. destruct (Z.eqb_spec pa 0) as [-> | Hp].
-
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & Hceil & Hslo & Hshi & H47 & _) & HQT).
pose proof asan_consts as (C1 & _). assert (ASTACK = 16384) as Has by reflexivity.
assert (Hsp' : spZ (ms_regs ms) = sp0 + o).
{ unfold spZ. rewrite Hsp. rewrite denot_SOff, HE2, Hspw. apply zcanon_small. zlia. }
rewrite (st_ok_restrict_mkst trasegs (w_H W) E ss ms HS Hrv), Hpc.
eapply SRr_mono.
{ eapply (aj_free_null_at trasegs B LAWS segs_low errno_low ML AFREE); eassumption. }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HPm & Hfr & HK).
exists ly2, S2, regs2, mem2, md2. split; [reflexivity|]. split; [exact HJ2|]. split; [exact HP2|].
split; [eapply Permutation_trans; [exact HPm | exact HPerm]|]. split; [exact Hfr|].
eapply rg_acall_kept_weaken; [|exact HK]. intros a [].
-
assert (Hin : In (pa, n) (ablocks B lyc Sc)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm | left; reflexivity]).
eapply SRr_mono.
{ eapply (aj_free trasegs B LAWS segs_low errno_low ML AFREE W E ss ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k pa n o spw raw ch);
try eassumption. intros Hin0. exact (HFP Hp Hin0). }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & (l1 & l2 & Ebl & Ebl2) & Hfr & HK).
exists ly2, S2, regs2, mem2, md2. split; [reflexivity|]. split; [exact HJ2|]. split; [exact HP2|].
split.
{ rewrite Ebl2. apply Permutation_sym. apply (@Permutation_cons_app_inv _ _ l1 l2 (pa, n)). rewrite <- Ebl.
apply Permutation_sym. exact HPerm. }
split; [exact Hfr|].
eapply rg_acall_kept_weaken; [|exact HK]. intros a Ha. split; [exact Hp | exact Ha].
Qed.
End d.
End c.

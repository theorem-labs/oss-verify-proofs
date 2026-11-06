(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: ported from proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v (entry state, region and fact proofs, the run/branch loop and its leaf) with the caller-journal leaf of lib/A/ACeu.v rfc_A_ok, aview_frame_off of lib/A/AD28.v (as kept_step) and frm_off_img of lib/A/ACeh.v (as frame_not_img) at c8557374ad2e to libreac/fuzz_knock: lib_asan3_0_listing -> knock_asan_listing, AF_asan3_cmpPixel -> AF_asan_reac_knock_step, tcmp_spec / tcmp_post -> tknock_step_specX / kn_post_step of lib/A/APgCSpec.v, cmp_entry / cmp_regions / cmp_facts / ss_cmp / cmp_SH / cmp_extra / EC / CBx / CBspan / pb_cmpPixel -> step_entry / step_regions / step_facts / ss_step / step_SH / step_extra / EK / KBx / KBspan / pb_knock_stepX; constants: TCMP_STK 16 + ESTACK -> T_step_STK 16, shadow-base atom 42 -> 39, GOT shadow slot / shadow-base cell A_OBJ 0 / A_OBJ 12 -> A_OBJ 1 / A_OBJ 7 (lib/Reusable/YC1f.v got_regionP / bcell_regionP / PALib), image bounds only through lib/Reusable/YImgTop.v (knock's 0x10000 .. 0x5f3000); the struct kp lies in a caller frame (cid, pos) of any class, written through awr_byte's in_frames case by In (cid, pos) own. *)
(* Modified by Theorem Labs, 2026-10: made from proofs/reac-pw/fuzz_qdisc/lib/A/QPgCheck.v at 236fd9c95ca (itself made from proofs/libreac/fuzz_knock/lib/A/APgStep.v at origin/ossv/recipes 6ebe35ba632: the save-slot region, its write obligation awr_stk / kwr_stk, the run / keep / leaf chain) with the kit-only plumbing of lib/A/RPgCfgChanges.v at 964efd2f474 (the image's own code table, cfg_wx / cfg_segs_low, kept_run, the leaf into lib/A/RPgCSpec.v's rl_post) for reac-pw/fuzz_role's image A (fuzz_role.asan): it walks check_absent 0x82bb4, check_role 0x82bdc and check_malformed 0x82c04 against rl_check_absent_specX / rl_check_role_specX / rl_check_malformed_specX on the concrete image lib/A/Img0.v rsegs; the entry state carries the registers the contract fixes (a0, a1, and a2 = a1 for check_role) as literals or as the atom they equal, so the engine decides every abort branch itself; qdisc's divisor-constant region, its arithmetic lemmas and its branch splits are dropped. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgCheck.v at 77f59d02b018 for reac-pw/fuzz_rate's
   image A (fuzz_rate.asan): module paths changed; the image is images.Asan's loaded segments instead of a lib/A/Img0
   module; the contracts are lib/A/RtPgCSpec.v's rt_check_absent_specX / rt_check_rate_specX / rt_check_malformed_specX
   (rt_cpre / rt_cpost, the same texts as role's rl_pre / rl_post) at rate's addresses; check_absent's and
   check_malformed's second literal is 0x5a5a5a5a (`lui` + `addiw`) where role's is 0x5a; check_decide (a0 = a1, the
   override a1 := the atom of a0) is added; the code table covers the four functions; the call-cut plumbing of
   proofs/reac-pw/fuzz_role/lib/A/RPgCheckStr.v at 77f59d02b018 (cs_eq, cs_eq_trans, cs_eq_of_pres, cs_eq_of_st_ok,
   sp_of_st_ok, L_ANS, L_ANS_cs, pres_of_cs) is added for the walks with a call. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgCheck.v; 692 of its 736 lines of code are new or changed and 246 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgEnt0Hd.v, with its module paths and numbers changed; 277 of its 652 lines of code are new or changed and 361 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgEnt0Hd.v at 97ea9c9eafa; for reac-pw/fuzz_headamp image A: module paths, the rs_ / rl_ / rm_ / RS_ / RM_ prefixes renamed to hs_ / hd_ / hm_ / HS_ / HM_; the real frame's cells R+0x58 -> R+0x80 and R+0xf8 -> R+0x118; F's object window [F+0x20, F+0x158); the frame for locals of class 4 (1024 bytes, 128 shadow bytes); hs_pre at the start pattern and hd_seg_pre's conjunct order (R mod 32, pp's block from hd_fresh_block); hm_sh's sixth scope flag (x) out of scope. *)
(* reac-pw/fuzz_headamp image A (fuzz_headamp.asan, pinned sha256
   f3e0669d2819724922df0556b11c2dcd22d1e16fe7e0fe1535ce784b34436c47; every address measured on the unstripped twin
   b5f352154c54a97c66fd92dfa228e8a854498f6cd313dba0107900546b043f9a, same loaded bytes except .note.gnu.build-id): HPgEnt0Def.r7_head_stmt,
   the head of ent_build's case 0 from both its entries (D = 0x81860 with the kind byte read, D0E = 0x818cc with no
   input left) to the two arms DIG = 0x81920 and ODD = 0x820c8. Proves no function (kind: segment lemma).

   HOW. The walk is the six blocks of lib/A/HPgEnt0HdB.v, chained with SRr_bind, by what is left of the input after
   the kind byte (r):
     r = []          hd_T0                      to DIG with c = p = 0, nothing more read
     r = [c]         hd_T1, hd_K1, hd_C         c read, p = 0, two bytes consumed
     r = c :: p :: _ hd_T1, hd_K2, hd_C         c and p read, three bytes consumed
     D0E             hd_TE                      to DIG with c = p = 0
   and hd_C goes to DIG when c < 200, to ODD otherwise. The facts each block asks are read off hs_cut_D by
   HPgEntBCut.eb_D_facts / eb_D_input (the input bytes at the cursor, their shadow and their place apart from the
   frames) and carried across the earlier blocks by their frame conditions; the cut at the arm (hd_build_DIG /
   hd_build_ODD) is the cut at the entry with the blocks' writes: the frame's shadow row from hs_PJ to hs_PG (t's
   twelve and ch's three granules in scope), [R+0x118] := what is left, and the registers of the arm. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v YI00 YI0m.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05 YO09 YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Layout Accessors Spa Tables.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import Img0 HPgBase HPgCSpec HPgImgA HPgMem HPgSeg.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgW7bBase HPgEnt0Def HPgEntBCut HPgEnt0HdB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
(* the cut record's projections, with the segments implicit as inside lib/A/HPgSeg.v *)
Local Arguments x_STK {segs} _. Local Arguments x_sp0 {segs} _. Local Arguments x_FP {segs} _.
Local Arguments x_ly {segs} _. Local Arguments x_S {segs} _. Local Arguments x_W0 {segs} _.
Local Arguments x_mem0 {segs} _. Local Arguments x_md0 {segs} _. Local Arguments x_own {segs} _.
Local Arguments x_k {segs} _. Local Arguments x_regs {segs} _. Local Arguments x_lyc {segs} _.
Local Arguments x_Sc {segs} _. Local Arguments x_W {segs} _. Local Arguments x_memc {segs} _.
Local Arguments x_mdc {segs} _. Local Arguments x_RLO {segs} _. Local Arguments x_RHI {segs} _.
Local Arguments x_e {segs} _. Local Arguments x_pos {segs} _.

(* every register any block of the head writes *)
Definition hd_clob : list (bv 5) := [5; 10; 11; 12; 17; 20; 24; 25; 27]%bv.

(* a register outside a concrete clobber list *)
Ltac hd_notin :=
let H := fresh "H" in intros H; cbn [In hd_clob] in H;
repeat (destruct H as [H|H]; [apply (f_equal (@bv_unsigned 5)) in H; vm_compute in H; discriminate H|]); exact H.
(* a register a block kept: rewrite with its keep clause Hk, then close with R *)
Ltac hd_kr Hk R := rewrite Hk; [exact R | cbv; discriminate | hd_notin].
(* one clobber list inside another *)
Ltac hd_sub := let q := fresh "q" in let X := fresh "X" in
intros q X; cbn [In hd_clob] in X |- *; tauto.
(* membership in a concrete location list of a cut *)
Ltac eb_in := cbn [hs_L_D hs_L_Dc hs_L_Dc0 hs_Rc hs_Rc0 hs_Kc app]; repeat (first [left; reflexivity | right]).

Lemma hd_sh_not_row : forall F x, F mod 8 = 0 -> ~ (F + 0x20 <= x < F + 0x158) ->
~ (shadow_addr F + 4 <= shadow_of_addr SHADOW_OFF x < shadow_addr F + 23).
Proof.
intros F x HF Hx Hin. unfold shadow_addr, shadow_of_addr in Hin.
pose proof (Z.div_mod x 8 ltac:(lia)) as Dx. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Mx.
pose proof (Z.div_mod F 8 ltac:(lia)) as DF. rewrite HF in DF. lia.
Qed.
Lemma hd_suffix_tl : forall (rest r : list byte) x, hs_suffix rest (x :: r) -> hs_suffix rest r.
Proof.
intros rest r x (j & Hj & E). exists (S j). split.
- destruct (Nat.le_gt_cases (length rest) j) as [Hle|Hlt]; [|lia].
  rewrite skipn_all2 in E by exact Hle. discriminate E.
- change (S j) with (1 + j)%nat. rewrite <- skipn_skipn, <- E. reflexivity.
Qed.

Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Let LAWS : AR_laws rsegs B := AR_laws_ok rsegs B.

(* ======================================== moving facts across blocks ======================================== *)
Lemma hd_at_get : forall H mem regs e (L : list (hd_loc * Z)) l v,
hs_at rsegs H mem regs e L -> In (l, v) L -> hd_at rsegs H mem regs e l v.
Proof. intros H mem regs e L l v HL Hin. exact (proj1 (Forall_forall _ _) HL (l, v) Hin). Qed.
(* what a location needs to keep its value between two states [lib/A/HPgProp.v pa_kept_loc / pa_at_move] *)
Definition hd_kept_loc (e : hd_env) (regs regs' : bvmap 5 word) (H : word -> bool)
(mem mem' : word -> option byte) (l : hd_loc) : Prop :=
match l with
| LReg r => getr regs' (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)
| LCell b o => forall j, 0 <= j < 8 -> aview rsegs H mem' (hd_xv e b + o + j) = aview rsegs H mem (hd_xv e b + o + j)
end.
Lemma hd_at_move : forall H mem regs mem' regs' e L,
hs_at rsegs H mem regs e L -> Forall (fun f => hd_kept_loc e regs regs' H mem mem' (fst f)) L ->
hs_at rsegs H mem' regs' e L.
Proof.
intros H mem regs mem' regs' e L HL HK. unfold hs_at in *.
induction L as [|[l v] L IH]; [constructor|].
inversion HL as [|? ? H1 H2]; subst. inversion HK as [|? ? K1 K2]; subst.
constructor; [|apply IH; assumption].
cbn [fst snd] in *. destruct l as [r|b o]; cbn [hd_at hd_kept_loc] in *.
- rewrite K1. exact H1.
- eapply val_mem_kept; [|exact H1]. intros j Hj. apply K1. lia.
Qed.
Lemma hd_keep2 : forall (r2 r3 r4 : bvmap 5 word) (c1 c2 c : list (bv 5)),
(forall q : bv 5, bv_unsigned q <> 0 -> ~ In q c1 -> getr r3 q = getr r2 q) ->
(forall q : bv 5, bv_unsigned q <> 0 -> ~ In q c2 -> getr r4 q = getr r3 q) ->
(forall q, In q c1 \/ In q c2 -> In q c) ->
forall q : bv 5, bv_unsigned q <> 0 -> ~ In q c -> getr r4 q = getr r2 q.
Proof.
intros r2 r3 r4 c1 c2 c K1 K2 Hs q Hq Hn.
rewrite (K2 q Hq ltac:(intros X; apply Hn, Hs; right; exact X)),
  (K1 q Hq ltac:(intros X; apply Hn, Hs; left; exact X)). reflexivity.
Qed.
Lemma hd_keep1 : forall (r2 r3 : bvmap 5 word) (c1 : list (bv 5)),
(forall q : bv 5, bv_unsigned q <> 0 -> ~ In q c1 -> getr r3 q = getr r2 q) ->
(forall q, In q c1 -> In q hd_clob) ->
forall q : bv 5, bv_unsigned q <> 0 -> ~ In q hd_clob -> getr r3 q = getr r2 q.
Proof. intros r2 r3 c1 K1 Hs q Hq Hn. exact (K1 q Hq (fun X => Hn (Hs q X))). Qed.
Lemma hd_mem2 : forall H m2 m3 m4 (W1 W2 Wt : Z -> Prop),
(forall a, 0 <= a < 2 ^ 64 -> ~ W1 a -> aview rsegs H m3 a = aview rsegs H m2 a) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ W2 a -> aview rsegs H m4 a = aview rsegs H m3 a) ->
(forall a, W1 a \/ W2 a -> Wt a) ->
forall a, 0 <= a < 2 ^ 64 -> ~ Wt a -> aview rsegs H m4 a = aview rsegs H m2 a.
Proof.
intros H m2 m3 m4 W1 W2 Wt K1 K2 Hs a Ha Hn.
rewrite (K2 a Ha ltac:(intros X; apply Hn, Hs; right; exact X)),
  (K1 a Ha ltac:(intros X; apply Hn, Hs; left; exact X)). reflexivity.
Qed.
Lemma hd_zero_kept : forall W m m' F j n,
hd_zero W m F j n ->
(forall i, j <= i < j + n -> aview rsegs (w_H W) m' (shadow_addr F + i) = aview rsegs (w_H W) m (shadow_addr F + i)) ->
hd_zero W m' F j n.
Proof. intros W m m' F j n Z0 K i Hi. rewrite K by exact Hi. exact (Z0 i Hi). Qed.

(* the frame's shadow row after two scope stores of v *)
Lemma hd_fsh_two : forall H mem H' mem' F pat (j1 k1 j2 k2 : nat) v,
hd_fsh rsegs H mem F pat ->
(forall i, Z.of_nat j1 <= i < Z.of_nat (j1 + k1) -> aview rsegs H' mem' (shadow_addr F + i) = Some v) ->
(forall i, Z.of_nat j2 <= i < Z.of_nat (j2 + k2) -> aview rsegs H' mem' (shadow_addr F + i) = Some v) ->
(forall i, 0 <= i < Z.of_nat (length pat) -> ~ (Z.of_nat j1 <= i < Z.of_nat (j1 + k1)) ->
 ~ (Z.of_nat j2 <= i < Z.of_nat (j2 + k2)) ->
 aview rsegs H' mem' (shadow_addr F + i) = aview rsegs H mem (shadow_addr F + i)) ->
hd_fsh rsegs H' mem' F (hm_setn (hm_setn pat j1 k1 v) j2 k2 v).
Proof.
intros H mem H' mem' F pat j1 k1 j2 k2 v P S1 S2 K i Hi.
rewrite !hm_setn_len in Hi.
rewrite hm_nth_setn by (rewrite hm_setn_len; lia).
destruct ((j2 <=? Z.to_nat i)%nat && (Z.to_nat i <? j2 + k2)%nat) eqn:E2.
- apply andb_prop in E2 as [A1 A2]. apply Nat.leb_le in A1. apply Nat.ltb_lt in A2. apply S2. lia.
- rewrite hm_nth_setn by lia.
  destruct ((j1 <=? Z.to_nat i)%nat && (Z.to_nat i <? j1 + k1)%nat) eqn:E1.
  + apply andb_prop in E1 as [A1 A2]. apply Nat.leb_le in A1. apply Nat.ltb_lt in A2. apply S1. lia.
  + rewrite K; [exact (P i ltac:(lia)) | lia | |].
    * intros [A1 A2]. apply andb_false_iff in E1 as [E|E]; [apply Nat.leb_gt in E | apply Nat.ltb_ge in E]; lia.
    * intros [A1 A2]. apply andb_false_iff in E2 as [E|E]; [apply Nat.leb_gt in E | apply Nat.ltb_ge in E]; lia.
Qed.

(* ======================================== the cut's journal part ======================================== *)
Lemma hd_core_step : forall cx (Ew : Z -> Prop) ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3,
hs_core rsegs B MT cx (hs_E1 rsegs cx) ly2 S2 W2 regs2 mem2 md2 ->
ajournal rsegs B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx) (x_own cx)
  ly2 S2 W2 mem3 md3 (x_k cx) ->
(forall r : Z, r = 2 \/ r = 3 \/ r = 4 -> getr regs3 (Z_to_bv 5 r) = getr regs2 (Z_to_bv 5 r)) ->
same_io md2 md3 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ Ew a -> aview rsegs (w_H W2) mem3 a = aview rsegs (w_H W2) mem2 a) ->
(forall a, Ew a -> hs_E1 rsegs cx a) ->
hs_core rsegs B MT cx (hs_E1 rsegs cx) ly2 S2 W2 regs3 mem3 md3.
Proof.
intros cx Ew ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 Hc HJ3 Hr3 Hio3 Hm3 HEw.
unfold hs_core, hs_mid in *. destruct Hc as (HJ & Hr & Hf & Hp & Hio & Hmo & Hm).
split; [exact HJ3|].
split; [intros r Hr'; rewrite (Hr3 r Hr'); exact (Hr r Hr')|].
split; [exact Hf|]. split; [exact Hp|].
split; [eapply same_io_trans; [exact Hio | exact Hio3]|].
split; [exact Hmo|].
intros a Ha Hs HE. rewrite <- (Hm a Ha Hs HE). apply Hm3; [exact Ha|]. intros HW. exact (HE (HEw a HW)).
Qed.
Lemma hd_E1 : forall cx a, hd_wTCN (e_R (x_e cx)) (e_F (x_e cx)) a -> hs_E1 rsegs cx a.
Proof.
intros cx a Ha. left. unfold hd_inw. cbn [hi_w1 headamp_himg_A].
destruct Ha as [Ha|[Ha|Ha]]; cbv [hd_wT hd_wCh hd_wN] in Ha.
- apply Exists_cons_tl. apply Exists_cons_hd. cbn [hd_xv fst snd]. lia.
- apply Exists_cons_tl. apply Exists_cons_hd. cbn [hd_xv fst snd]. lia.
- apply Exists_cons_tl. apply Exists_cons_tl. apply Exists_cons_hd. cbn [hd_xv fst snd]. lia.
Qed.
Lemma hd_base_move : forall cx sh np ps cnt es rest rr r r' ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3,
hs_pod_base rsegs B MT cx sh np ps cnt es rest rr r ly2 S2 W2 regs2 mem2 md2 ->
hs_core rsegs B MT cx (hs_E1 rsegs cx) ly3 S3 W3 regs3 mem3 md3 -> hs_suffix rest r' ->
hs_pod_base rsegs B MT cx sh np ps cnt es rest rr r' ly3 S3 W3 regs3 mem3 md3.
Proof.
intros cx sh np ps cnt es rest rr r r' ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3 (_ & Hin & _ & Hr) Hc Hs.
exact (conj Hc (conj Hin (conj Hs Hr))).
Qed.

(* a cut's context for the blocks, and where F and pp lie *)
Lemma hd_cut_facts : forall cx E ly2 S2 W2 regs2 mem2 md2,
hs_pre rsegs B cx (hi_shA headamp_himg_A) -> hs_core rsegs B MT cx E ly2 S2 W2 regs2 mem2 md2 ->
hd_ctx B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx) (x_own cx) (x_k cx)
  ly2 S2 W2 mem2 md2 (e_R (x_e cx)) (e_F (x_e cx)) (x_pos cx) /\
in_app (e_F (x_e cx)) 1024 /\ in_app (e_pp (x_e cx)) Layout.PP_SIZE.
Proof.
intros cx E ly2 S2 W2 regs2 mem2 md2 Hpre Hcore.
destruct Hpre as (HJc & _ & _ & _ & _ & ES & ER32 & ERS & ESTK & Hown & EF & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  (_ & Hppb & _)).
assert (ER16 : e_R (x_e cx) mod 16 = 0).
{ pose proof (Z.div_mod (e_R (x_e cx)) 32 ltac:(lia)) as D. rewrite ER32, Z.add_0_r in D. rewrite D.
  replace (32 * (e_R (x_e cx) / 32)) with ((2 * (e_R (x_e cx) / 32)) * 16) by ring. apply Z_mod_mult. }
destruct Hcore as (HJ & _).
pose proof HJc as (HARc & Hlyc & _ & _ & _ & Hfrsc & _).
pose proof HJ as (_ & Hly & _).
cbn [hi_cid hi_rsz headamp_himg_A] in Hown, EF, ERS.
assert (Hin3 : In (4, x_pos cx) (frames (x_Sc cx))) by (rewrite Hfrsc; apply in_or_app; left; exact Hown).
destruct (al_frames _ _ LAWS _ _ _ _ _ 4 (x_pos cx) HARc Hin3) as (_ & HFapp & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HARc Hppb) as (_ & _ & _ & Happ & _).
split; [|split].
- split; [exact HJ|]. split; [exact ER16|]. split; [rewrite <- ES; exact ERS|]. split; [exact ESTK|].
  split; [exact Hown|]. rewrite EF.
  rewrite (eb_frame_addr_le _ _ _ 4 (x_pos cx) Hly), (eb_frame_addr_le _ _ _ 4 (x_pos cx) Hlyc). reflexivity.
- rewrite EF. exact HFapp.
- exact Happ.
Qed.

(* ======================================== the cuts at the two arms ======================================== *)
Lemma hd_build_common : forall cx sh np ps cnt es rest rr r r3 ly2 S2 W2 regs2 mem2 md2 regs5 mem5 md5,
hs_pre rsegs B cx (hi_shA headamp_himg_A) ->
hs_pod_base rsegs B MT cx sh np ps cnt es rest rr r ly2 S2 W2 regs2 mem2 md2 ->
hs_at_cx rsegs cx W2 mem2 regs2 (hs_L_Dc0 rsegs cx sh np ps cnt es) ->
hs_fsh_at rsegs cx W2 mem2 hs_PJ ->
hs_pp_at rsegs cx W2 mem2 (pc_image (PbCut sh ps (Some es))) ->
garr8 rsegs (mrestrict (w_H W2) mem2) (e_F (x_e cx) + 0xf0) (hd_zbytes (zeros 104)) ->
ajournal rsegs B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx) (x_own cx)
  ly2 S2 W2 mem5 md5 (x_k cx) ->
same_io md2 md5 ->
(forall q : bv 5, bv_unsigned q <> 0 -> ~ In q hd_clob -> getr regs5 q = getr regs2 q) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ hd_wTCN (e_R (x_e cx)) (e_F (x_e cx)) a ->
 aview rsegs (w_H W2) mem5 a = aview rsegs (w_H W2) mem2 a) ->
hd_zero W2 mem5 (e_F (x_e cx)) 4 12 -> hd_zero W2 mem5 (e_F (x_e cx)) 20 3 ->
val_mem rsegs (mrestrict (w_H W2) mem5) (e_R (x_e cx) + 0x118) 8 (Z.of_nat (length r3)) ->
getr regs5 20 = w64 (e_F (x_e cx) + 0xa0) ->
hs_suffix rest r3 ->
hs_pod_base rsegs B MT cx sh np ps cnt es rest rr r3 ly2 S2 W2 regs5 mem5 md5 /\
hs_at_cx rsegs cx W2 mem5 regs5
 (hs_L_Dc0 rsegs cx sh np ps cnt es ++ [(LCell XR 0x118, Z.of_nat (length r3)); (LReg 20, e_F (x_e cx) + 0xa0)]) /\
hs_fsh_at rsegs cx W2 mem5 hs_PG /\
hs_pp_at rsegs cx W2 mem5 (pc_image (PbCut sh ps (Some es))) /\
garr8 rsegs (mrestrict (w_H W2) mem5) (e_F (x_e cx) + 0xf0) (hd_zbytes (zeros 104)).
Proof.
intros cx sh np ps cnt es rest rr r r3 ly2 S2 W2 regs2 mem2 md2 regs5 mem5 md5
  Hpre Hb Hat0 Hfsh Hpp He HJ5 Hio5 Hk5 Hm5 Z1 Z2 V5 R20 Hsuf.
destruct (hd_cut_facts cx _ ly2 S2 W2 regs2 mem2 md2 Hpre (proj1 Hb)) as (Hctx & HFapp & Hppapp).
destruct (hd_frame B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hctx)
  as (HF32 & HF0 & HFc & HRc & HR0 & HR1 & Has & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (hd_sF (e_F (x_e cx)) ltac:(lia) ltac:(lia)) as [SF0 SF1].
pose proof Hb as (Hcore & Hin & _ & _ & Hwf & _ & _ & _ & _ & _ & _ & _ & _ & Hps2 & _ & Hesw & Hes32 & _).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp, Hppapp.
assert (Hl3 : 0 <= Z.of_nat (length r3) < 2 ^ 64).
{ destruct Hsuf as (j & Hj & ->). rewrite length_skipn.
  destruct Hin as (Hel & _ & _ & _ & _ & Hs0 & Hs63 & _).
  pose proof (Nat.le_sub_l (length rest) j) as Hle. apply Nat2Z.inj_le in Hle.
  set (m := Z.of_nat (length rest - j)) in *. set (m0 := Z.of_nat (length rest)) in *.
  split; [apply Zle_0_nat | lia]. }
assert (Hcore5 : hs_core rsegs B MT cx (hs_E1 rsegs cx) ly2 S2 W2 regs5 mem5 md5).
{ apply (hd_core_step cx (hd_wTCN (e_R (x_e cx)) (e_F (x_e cx))) ly2 S2 W2 regs2 mem2 md2 regs5 mem5 md5 Hcore HJ5).
  - intros q [->|[->| ->]]; (apply Hk5; [cbv; discriminate | hd_notin]).
  - exact Hio5.
  - exact Hm5.
  - apply hd_E1. }
split; [exact (hd_base_move cx sh np ps cnt es rest rr r r3 ly2 S2 W2 regs2 mem2 md2 ly2 S2 W2 regs5 mem5 md5
  Hb Hcore5 Hsuf)|].
split.
{ unfold hs_at_cx, hs_at. apply Forall_app. split.
  - apply (hd_at_move _ _ _ mem5 regs5 _ _ Hat0).
    cbn [hs_L_Dc0 hs_Rc0 hs_Kc app]; repeat apply Forall_cons; try apply Forall_nil; cbn [fst hd_kept_loc hd_xv].
    all: first [ apply Hk5; [cbv; discriminate | hd_notin]
               | let j := fresh "j" in let Hj := fresh "Hj" in
                 intros j Hj; apply Hm5; [lia | cbv [hd_wTCN hd_wT hd_wCh hd_wN]; lia] ].
  - repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd hd_at hd_xv].
    + rewrite Z.mod_small by lia. exact V5.
    + exact R20. }
split.
{ unfold hs_fsh_at in *. rewrite r7_PG_sh. rewrite r7_PJ_sh in Hfsh.
  replace (hm_sh true true false true false false) with (hm_setn (hm_setn (hm_sh false false false true false false) 4 12 0) 20 3 0)
    by (vm_compute; reflexivity).
  apply (hd_fsh_two _ _ _ _ _ _ 4 12 20 3 0 Hfsh).
  - intros i Hi. simpl in Hi. apply Z1. lia.
  - intros i Hi. simpl in Hi. apply Z2. lia.
  - intros i Hi N1 N2. rewrite hm_sh_len in Hi. simpl in Hi, N1, N2.
    apply Hm5; [lia | cbv [hd_wTCN hd_wT hd_wCh hd_wN]; lia]. }
split.
{ unfold hs_pp_at in *. eapply (hm_bytes_kept rsegs); [exact Hpp|]. intros x Hx.
  rewrite (eb_pc_len sh ps es Hwf Hesw Hes32 Hps2) in Hx. unfold Layout.PP_SIZE in *.
  apply Hm5; [lia | cbv [hd_wTCN hd_wT hd_wCh hd_wN]; lia]. }
{ intros j Hj. destruct (He j Hj) as [V B8]. split; [|exact B8].
  unfold hd_zbytes, zeros in Hj. rewrite length_map, hm_length_repeat in Hj.
  eapply val_mem_kept; [|exact V]. intros q Hq.
  apply Hm5; [lia | cbv [hd_wTCN hd_wT hd_wCh hd_wN]; lia]. }
Qed.

Lemma hd_build_DIG : forall cx sh np ps cnt es rest rr r r3 c pb ly2 S2 W2 regs2 mem2 md2 regs5 mem5 md5,
hs_pre rsegs B cx (hi_shA headamp_himg_A) ->
hs_pod_base rsegs B MT cx sh np ps cnt es rest rr r ly2 S2 W2 regs2 mem2 md2 ->
hs_at_cx rsegs cx W2 mem2 regs2 (hs_L_Dc0 rsegs cx sh np ps cnt es) ->
hs_fsh_at rsegs cx W2 mem2 hs_PJ ->
hs_pp_at rsegs cx W2 mem2 (pc_image (PbCut sh ps (Some es))) ->
garr8 rsegs (mrestrict (w_H W2) mem2) (e_F (x_e cx) + 0xf0) (hd_zbytes (zeros 104)) ->
ajournal rsegs B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx) (x_own cx)
  ly2 S2 W2 mem5 md5 (x_k cx) ->
same_io md2 md5 ->
(forall q : bv 5, bv_unsigned q <> 0 -> ~ In q hd_clob -> getr regs5 q = getr regs2 q) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ hd_wTCN (e_R (x_e cx)) (e_F (x_e cx)) a ->
 aview rsegs (w_H W2) mem5 a = aview rsegs (w_H W2) mem2 a) ->
hd_zero W2 mem5 (e_F (x_e cx)) 4 12 -> hd_zero W2 mem5 (e_F (x_e cx)) 20 3 ->
val_mem rsegs (mrestrict (w_H W2) mem5) (e_R (x_e cx) + 0x118) 8 (Z.of_nat (length r3)) ->
getr regs5 5 = w64 9 -> getr regs5 10 = w64 c -> getr regs5 17 = w64 10 ->
getr regs5 20 = w64 (e_F (x_e cx) + 0xa0) -> getr regs5 25 = w64 (hs_cur rsegs cx rest r3) ->
getr regs5 27 = w64 pb ->
hs_suffix rest r3 -> fst (Cursor.fuzz_u8 rr) mod 10 = 0 -> (c, pb, r3) = r7_cp_of rr ->
0 <= c < 200 -> 0 <= pb < 256 ->
r7_cut_DIG rsegs B MT cx sh np ps cnt es rest rr r3 c pb ly2 S2 W2 regs5 mem5 md5.
Proof.
intros cx sh np ps cnt es rest rr r r3 c pb ly2 S2 W2 regs2 mem2 md2 regs5 mem5 md5
  Hpre Hb Hat0 Hfsh Hpp He HJ5 Hio5 Hk5 Hm5 Z1 Z2 V5 R5 R10 R17 R20 R25 R27 Hsuf Hkd Hcp Hc Hpb.
destruct (hd_build_common cx sh np ps cnt es rest rr r r3 ly2 S2 W2 regs2 mem2 md2 regs5 mem5 md5
  Hpre Hb Hat0 Hfsh Hpp He HJ5 Hio5 Hk5 Hm5 Z1 Z2 V5 R20 Hsuf) as (Hb5 & Hat5 & Hfsh5 & Hpp5 & He5).
unfold r7_cut_DIG.
split; [exact Hb5|].
split.
{ unfold r7_L_arm. unfold hs_at_cx, hs_at in *.
  apply Forall_app in Hat5 as [HatA HatB].
  apply Forall_cons_iff in HatB as [F8 HatB]. apply Forall_cons_iff in HatB as [F20 _].
  rewrite <- app_assoc. apply Forall_app. split; [exact HatA|].
  cbn [app]. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd hd_at].
  - exact F8. - exact F20. - exact R27. - exact R25. - exact R10. - exact R17. - exact R5. }
split; [exact Hfsh5|]. split; [exact Hpp5|]. split; [exact He5|].
split; [exact Hkd|]. split; [exact Hcp|]. split; [exact Hc | exact Hpb].
Qed.

Lemma hd_build_ODD : forall cx sh np ps cnt es rest rr r r3 c pb ly2 S2 W2 regs2 mem2 md2 regs5 mem5 md5,
hs_pre rsegs B cx (hi_shA headamp_himg_A) ->
hs_pod_base rsegs B MT cx sh np ps cnt es rest rr r ly2 S2 W2 regs2 mem2 md2 ->
hs_at_cx rsegs cx W2 mem2 regs2 (hs_L_Dc0 rsegs cx sh np ps cnt es) ->
hs_fsh_at rsegs cx W2 mem2 hs_PJ ->
hs_pp_at rsegs cx W2 mem2 (pc_image (PbCut sh ps (Some es))) ->
garr8 rsegs (mrestrict (w_H W2) mem2) (e_F (x_e cx) + 0xf0) (hd_zbytes (zeros 104)) ->
ajournal rsegs B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx) (x_own cx)
  ly2 S2 W2 mem5 md5 (x_k cx) ->
same_io md2 md5 ->
(forall q : bv 5, bv_unsigned q <> 0 -> ~ In q hd_clob -> getr regs5 q = getr regs2 q) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ hd_wTCN (e_R (x_e cx)) (e_F (x_e cx)) a ->
 aview rsegs (w_H W2) mem5 a = aview rsegs (w_H W2) mem2 a) ->
hd_zero W2 mem5 (e_F (x_e cx)) 4 12 -> hd_zero W2 mem5 (e_F (x_e cx)) 20 3 ->
val_mem rsegs (mrestrict (w_H W2) mem5) (e_R (x_e cx) + 0x118) 8 (Z.of_nat (length r3)) ->
getr regs5 10 = w64 c -> getr regs5 20 = w64 (e_F (x_e cx) + 0xa0) ->
getr regs5 24 = w64 (hs_cur rsegs cx rest r3) -> getr regs5 27 = w64 pb ->
hs_suffix rest r3 -> fst (Cursor.fuzz_u8 rr) mod 10 = 0 -> (c, pb, r3) = r7_cp_of rr ->
200 <= c < 256 -> 0 <= pb < 256 ->
r7_cut_ODD rsegs B MT cx sh np ps cnt es rest rr r3 c pb ly2 S2 W2 regs5 mem5 md5.
Proof.
intros cx sh np ps cnt es rest rr r r3 c pb ly2 S2 W2 regs2 mem2 md2 regs5 mem5 md5
  Hpre Hb Hat0 Hfsh Hpp He HJ5 Hio5 Hk5 Hm5 Z1 Z2 V5 R10 R20 R24 R27 Hsuf Hkd Hcp Hc Hpb.
destruct (hd_build_common cx sh np ps cnt es rest rr r r3 ly2 S2 W2 regs2 mem2 md2 regs5 mem5 md5
  Hpre Hb Hat0 Hfsh Hpp He HJ5 Hio5 Hk5 Hm5 Z1 Z2 V5 R20 Hsuf) as (Hb5 & Hat5 & Hfsh5 & Hpp5 & He5).
unfold r7_cut_ODD.
split; [exact Hb5|].
split.
{ unfold r7_L_arm. unfold hs_at_cx, hs_at in *.
  apply Forall_app in Hat5 as [HatA HatB].
  apply Forall_cons_iff in HatB as [F8 HatB]. apply Forall_cons_iff in HatB as [F20 _].
  rewrite <- app_assoc. apply Forall_app. split; [exact HatA|].
  cbn [app]. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd hd_at].
  - exact F8. - exact F20. - exact R27. - exact R24. - exact R10. }
split; [exact Hfsh5|]. split; [exact Hpp5|]. split; [exact He5|].
split; [exact Hkd|]. split; [exact Hcp|]. split; [exact Hc | exact Hpb].
Qed.

(* ===================== after the reads: the ch stores, the arm test and the arm's cut =====================
   The state at 0x820ac (hd_K1 / hd_K2's post, after hd_T1) with everything it changed since the case entry. *)
Lemma hd_after_K : forall cx POST rest i k sh np ps cnt es rr r r3 c pb cur' ly2 S2 W2 regs2 mem2 md2 regs4 mem4 md4,
hs_start_M01 rsegs B cx rest ->
r7_from_DIG rsegs B MT cx POST rest i k -> r7_from_ODD rsegs B MT cx POST rest i k ->
(length ps = i)%nat -> (length es = k)%nat ->
hs_pod_base rsegs B MT cx sh np ps cnt es rest rr r ly2 S2 W2 regs2 mem2 md2 ->
hs_at_cx rsegs cx W2 mem2 regs2 (hs_L_Dc0 rsegs cx sh np ps cnt es) ->
hs_fsh_at rsegs cx W2 mem2 hs_PJ ->
hs_pp_at rsegs cx W2 mem2 (pc_image (PbCut sh ps (Some es))) ->
garr8 rsegs (mrestrict (w_H W2) mem2) (e_F (x_e cx) + 0xf0) (hd_zbytes (zeros 104)) ->
hd_ctx B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx) (x_own cx) (x_k cx)
  ly2 S2 W2 mem4 md4 (e_R (x_e cx)) (e_F (x_e cx)) (x_pos cx) ->
same_io md2 md4 ->
(forall q : bv 5, bv_unsigned q <> 0 -> ~ In q hd_clob -> getr regs4 q = getr regs2 q) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ hd_wTCN (e_R (x_e cx)) (e_F (x_e cx)) a ->
 aview rsegs (w_H W2) mem4 a = aview rsegs (w_H W2) mem2 a) ->
hd_zero W2 mem4 (e_F (x_e cx)) 4 12 ->
val_mem rsegs (mrestrict (w_H W2) mem4) (e_R (x_e cx) + 0x118) 8 (Z.of_nat (length r3)) ->
getr regs4 5 = w64 9 -> getr regs4 10 = w64 c -> getr regs4 17 = w64 10 ->
getr regs4 19 = w64 (shadow_addr (e_F (x_e cx))) -> getr regs4 20 = w64 (e_F (x_e cx) + 0xa0) ->
getr regs4 24 = w64 cur' -> getr regs4 27 = w64 pb ->
cur' = hs_cur rsegs cx rest r3 -> 0 <= cur' < 2 ^ 64 ->
hs_suffix rest r3 -> fst (Cursor.fuzz_u8 rr) mod 10 = 0 -> (c, pb, r3) = r7_cp_of rr ->
0 <= c < 256 -> 0 <= pb < 256 ->
SRr rsegs W2 (cfg_at rsegs HD_CH regs4 mem4 md4) POST.
Proof.
intros cx POST rest i k sh np ps cnt es rr r r3 c pb cur' ly2 S2 W2 regs2 mem2 md2 regs4 mem4 md4
  Hst HDIG HODD Hlps Hles Hb Hat0 Hfsh Hpp He Hctx4 Hio4 Hk4 Hm4 Z4 V4 R5 R10 R17 R19 R20 R24 R27 Ecur Hcur
  Hsuf Hkd Hcp Hc Hpb.
pose proof Hst as (Hpre & _).
pose proof Hctx4 as (HJ4 & _).
destruct (hd_frame B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hctx4)
  as (HF32 & HF0 & HFc & HRc & HR0 & HR1 & Has & _).
pose proof asan_consts as (C1 & _).
destruct (hd_sF (e_F (x_e cx)) ltac:(lia) ltac:(lia)) as [SF0 SF1].
assert (Hsub : forall q, In q hd_clob \/ In q [11; 25]%bv -> In q hd_clob) by hd_sub.
assert (Hwsub : forall a, hd_wTCN (e_R (x_e cx)) (e_F (x_e cx)) a \/ hd_wCh (e_F (x_e cx)) a ->
  hd_wTCN (e_R (x_e cx)) (e_F (x_e cx)) a) by (cbv [hd_wTCN]; tauto).
destruct (Z_lt_le_dec c 200) as [Hlt|Hge].
- eapply SRr_bind.
  { exact (hd_C B LAWS false _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs4 _ _ _ c cur' Hctx4 R19 R10 (conj (proj1 Hc) Hlt) R24 Hcur). }
  intros W5 c5 _ (-> & regs5 & mem5 & md5 & -> & HJ5 & Hio5 & Hk5 & Hm5 & Hp5 & (Z5 & S25)).
  change (mkCfg (mkst regs5 (Z_to_bv 64 (if false then R7_ODD else R7_DIG)) mem5 (seg_rom rsegs)) md5)
    with (cfg_at rsegs R7_DIG regs5 mem5 md5).
  apply (HDIG ly2 S2 W2 regs5 mem5 md5 sh np ps cnt es rr r3 c pb Hlps Hles).
  apply (hd_build_DIG cx sh np ps cnt es rest rr r r3 c pb ly2 S2 W2 regs2 mem2 md2 regs5 mem5 md5
    Hpre Hb Hat0 Hfsh Hpp He HJ5 (same_io_trans _ _ _ Hio4 Hio5)
    (hd_keep2 regs2 regs4 regs5 hd_clob [11; 25]%bv hd_clob Hk4 Hk5 Hsub)
    (hd_mem2 _ mem2 mem4 mem5 _ _ _ Hm4 Hm5 Hwsub)).
  + apply (hd_zero_kept W2 mem4 mem5 _ 4 12 Z4). intros q Hq.
    apply Hm5; [lia | cbv [hd_wCh]; lia].
  + exact Z5.
  + eapply val_mem_kept; [|exact V4]. intros q Hq. apply Hm5; [lia | cbv [hd_wCh]; lia].
  + hd_kr Hk5 R5.
  + hd_kr Hk5 R10.
  + hd_kr Hk5 R17.
  + hd_kr Hk5 R20.
  + cbv iota in S25. rewrite S25, Ecur. reflexivity.
  + hd_kr Hk5 R27.
  + exact Hsuf.
  + exact Hkd.
  + exact Hcp.
  + lia.
  + exact Hpb.
- eapply SRr_bind.
  { exact (hd_C B LAWS true _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs4 _ _ _ c cur' Hctx4 R19 R10 (conj Hge (proj2 Hc)) R24 Hcur). }
  intros W5 c5 _ (-> & regs5 & mem5 & md5 & -> & HJ5 & Hio5 & Hk5 & Hm5 & Hp5 & (Z5 & _)).
  change (mkCfg (mkst regs5 (Z_to_bv 64 (if true then R7_ODD else R7_DIG)) mem5 (seg_rom rsegs)) md5)
    with (cfg_at rsegs R7_ODD regs5 mem5 md5).
  apply (HODD ly2 S2 W2 regs5 mem5 md5 sh np ps cnt es rr r3 c pb Hlps Hles).
  apply (hd_build_ODD cx sh np ps cnt es rest rr r r3 c pb ly2 S2 W2 regs2 mem2 md2 regs5 mem5 md5
    Hpre Hb Hat0 Hfsh Hpp He HJ5 (same_io_trans _ _ _ Hio4 Hio5)
    (hd_keep2 regs2 regs4 regs5 hd_clob [11; 25]%bv hd_clob Hk4 Hk5 Hsub)
    (hd_mem2 _ mem2 mem4 mem5 _ _ _ Hm4 Hm5 Hwsub)).
  + apply (hd_zero_kept W2 mem4 mem5 _ 4 12 Z4). intros q Hq.
    apply Hm5; [lia | cbv [hd_wCh]; lia].
  + exact Z5.
  + eapply val_mem_kept; [|exact V4]. intros q Hq. apply Hm5; [lia | cbv [hd_wCh]; lia].
  + hd_kr Hk5 R10.
  + hd_kr Hk5 R20.
  + rewrite <- Ecur. hd_kr Hk5 R24.
  + hd_kr Hk5 R27.
  + exact Hsuf.
  + exact Hkd.
  + exact Hcp.
  + lia.
  + exact Hpb.
Qed.

(* ======================================== D0E: no input left ======================================== *)
Lemma hd_piece_D0E : forall cx POST rest i k,
hs_start_M01 rsegs B cx rest -> r7_from_DIG rsegs B MT cx POST rest i k -> hs_from_D0E rsegs B MT cx POST rest i k.
Proof.
intros cx POST rest i k Hst HDIG.
unfold hs_from_D0E. intros ly2 S2 W2 regs2 mem2 md2 sh np ps cnt es Hlps Hles Hcut.
destruct Hcut as (Hb & Hat & Hfsh & Hppat & He).
pose proof Hst as (Hpre & _).
destruct (hd_cut_facts cx _ ly2 S2 W2 regs2 mem2 md2 Hpre (proj1 Hb)) as (Hctx & HFapp & Hppapp).
destruct (hd_frame B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hctx)
  as (HF32 & HF0 & HFc & HRc & HR0 & HR1 & Has & _).
pose proof asan_consts as (C1 & _).
assert (Hat0 : hs_at_cx rsegs cx W2 mem2 regs2 (hs_L_Dc0 rsegs cx sh np ps cnt es)).
{ pose proof Hat as Hat'. unfold hs_at_cx, hs_at, hs_L_Dc in Hat' |- *.
  apply Forall_app in Hat' as [Hat' _]. apply Forall_app in Hat' as [Hat' _]. exact Hat'. }
pose proof (hd_at_get _ _ _ _ _ (LReg 9) _ Hat ltac:(eb_in)) as R9. cbn [hd_at] in R9.
pose proof (hd_at_get _ _ _ _ _ (LReg 19) _ Hat ltac:(eb_in)) as R19. cbn [hd_at] in R19.
pose proof (hd_at_get _ _ _ _ _ (LReg 25) _ Hat ltac:(eb_in)) as R25. cbn [hd_at] in R25.
pose proof (hd_at_get _ _ _ _ _ (LCell XR 0x80) _ Hat ltac:(eb_in)) as V58. cbn [hd_at hd_xv] in V58.
rewrite Z.mod_small in V58 by lia.
eapply SRr_bind.
{ exact (hd_TE B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs2 _ _ _ Hctx R9 R19 V58). }
intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & Hio3 & Hk3 & Hm3 & Hp3 &
  ((R5 & R10 & R20 & R27) & R17 & (Z1 & Z2 & V3))).
change (mkCfg (mkst regs3 (Z_to_bv 64 R7_DIG) mem3 (seg_rom rsegs)) md3) with (cfg_at rsegs R7_DIG regs3 mem3 md3).
apply (HDIG ly2 S2 W2 regs3 mem3 md3 sh np ps cnt es [] [] 0 0 Hlps Hles).
apply (hd_build_DIG cx sh np ps cnt es rest [] [] [] 0 0 ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3
  Hpre Hb Hat0 Hfsh Hppat He HJ3 Hio3).
- apply (hd_keep1 regs2 regs3 [5; 10; 17; 20; 27]%bv Hk3). hd_sub.
- exact Hm3.
- exact Z1.
- exact Z2.
- exact V3.
- exact R5.
- exact R10.
- exact R17.
- exact R20.
- hd_kr Hk3 R25.
- exact R27.
- exact (proj1 (proj2 (proj2 Hb))).
- reflexivity.
- reflexivity.
- lia.
- lia.
Qed.

(* ======================================== D: the kind byte read ======================================== *)
Lemma hd_piece_D : forall cx POST rest i k kd,
hs_start_M01 rsegs B cx rest -> kd mod 10 = 0 ->
r7_from_DIG rsegs B MT cx POST rest i k -> r7_from_ODD rsegs B MT cx POST rest i k ->
hs_from_D rsegs B MT cx POST rest i k kd.
Proof.
intros cx POST rest i k kd Hst Hkd HDIG HODD.
unfold hs_from_D. intros ly2 S2 W2 regs2 mem2 md2 sh np ps cnt es rr r Hlps Hles Hcut.
replace (hs_pc_D kd) with HD_D by (unfold hs_pc_D; rewrite Hkd; reflexivity).
pose proof (eb_D_facts B MT cx rest sh np ps cnt es rr r kd ly2 S2 W2 regs2 mem2 md2 Hst Hcut) as
  (HJ & R2 & R3 & R4 & R9 & R23 & R24 & R14 & R25 & R21 & R27 & V20 & V70 & V80 & Vb0 & Vc0 & Vf0 & Vf8
   & BR1 & BR2 & BR3 & BR4 & BR5 & Hown & HinF & EF2 & HF1 & HF2 & HF32 & HFapp & Hpp & Hpp1 & Hpp2 & Hsep
   & Hc1 & Hc2 & Ez & HFp & HraE & Hpres & HFSHD & HromD).
pose proof (eb_D_input B MT cx rest sh np ps cnt es rr r kd ly2 S2 W2 regs2 mem2 md2 Hst Hcut) as
  (Hg & Hra & _ & Ham & Hdis).
pose proof Hst as (Hpre & _).
destruct Hcut as (Hb & Hat & Hfsh & Hppat & He & _ & Hkdr & Hkd8 & Hrr).
destruct (hd_cut_facts cx _ ly2 S2 W2 regs2 mem2 md2 Hpre (proj1 Hb)) as (Hctx & _ & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HTS : T_SEG_STK = 16384) by reflexivity.
destruct (hd_sF (e_F (x_e cx)) ltac:(lia) ltac:(lia)) as [SF0 SF1].
assert (HF8 : e_F (x_e cx) mod 8 = 0).
{ apply (proj2 (Z.mod_divide (e_F (x_e cx)) 8 ltac:(lia))). apply (proj1 (Z.mod_divide _ 32 ltac:(lia))) in HF32.
  destruct HF32 as [q Hq]. exists (4 * q). lia. }
assert (Hat0 : hs_at_cx rsegs cx W2 mem2 regs2 (hs_L_Dc0 rsegs cx sh np ps cnt es)).
{ pose proof Hat as Hat'. unfold hs_at_cx, hs_at, hs_L_D, hs_L_Dc in Hat' |- *.
  apply Forall_app in Hat' as [Hat' _]. apply Forall_app in Hat' as [Hat' _]. exact Hat'. }
pose proof (hd_at_get _ _ _ _ _ (LReg 19) _ Hat ltac:(eb_in)) as R19. cbn [hd_at] in R19.
pose proof (hd_at_get _ _ _ _ _ (LReg 17) _ Hat ltac:(eb_in)) as R17. cbn [hd_at] in R17.
pose proof (hd_at_get _ _ _ _ _ (LCell XR 0x80) _ Hat ltac:(eb_in)) as V58. cbn [hd_at hd_xv] in V58.
rewrite Z.mod_small in V58 by lia.
pose proof Hb as (_ & _ & Hsufr & _).
unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Ham.
destruct rr as [|kb rr0]; [contradiction|].
cbn [Cursor.fuzz_u8] in Hkdr. injection Hkdr as Ekd Er. subst rr0.
assert (Hkd' : fst (Cursor.fuzz_u8 (kb :: r)) mod 10 = 0) by (cbn [Cursor.fuzz_u8 fst]; rewrite <- Ekd; exact Hkd).
(* the input bytes and their shadow keep their values across a block that writes only the frame's shadow row *)
assert (Hin_keep : forall (m : word -> option byte),
  (forall a, 0 <= a < 2 ^ 64 -> ~ hd_wT (e_F (x_e cx)) a -> aview rsegs (w_H W2) m a = aview rsegs (w_H W2) mem2 a) ->
  forall a, hs_cur rsegs cx rest r <= a < hs_cur rsegs cx rest r + Z.of_nat (length r) ->
  aview rsegs (w_H W2) m a = aview rsegs (w_H W2) mem2 a /\
  aview rsegs (w_H W2) m (shadow_of_addr SHADOW_OFF a) = aview rsegs (w_H W2) mem2 (shadow_of_addr SHADOW_OFF a)).
{ intros m Hm a Ha.
  pose proof (hm_shadow_band a ltac:(unfold kHighMemEnd; lia)) as Hsb. unfold kLowMemEnd, kHighMemBeg in Hsb.
  pose proof (hd_sh_not_row _ a HF8 (proj1 (proj2 (Hdis a Ha)))) as Hnr.
  split; apply Hm; try lia; cbv [hd_wT]; lia. }
destruct r as [|cb [|pb r3]].
- (* r = []: c = p = 0, the cursor does not move *)
  eapply SRr_bind.
  { exact (hd_T0 B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs2 _ _ _ (hs_cur rsegs cx rest []) Hctx R9 R19 R25 R24
      ltac:(cbn [length Z.of_nat] in Hc2; lia) V58). }
  intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & Hio3 & Hk3 & Hm3 & Hp3 &
    ((R5' & R10' & R20' & R27') & R25' & (Z1 & Z2 & V3))).
  change (mkCfg (mkst regs3 (Z_to_bv 64 R7_DIG) mem3 (seg_rom rsegs)) md3) with (cfg_at rsegs R7_DIG regs3 mem3 md3).
  apply (HDIG ly2 S2 W2 regs3 mem3 md3 sh np ps cnt es [kb] [] 0 0 Hlps Hles).
  apply (hd_build_DIG cx sh np ps cnt es rest [kb] [] [] 0 0 ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3
    Hpre Hb Hat0 Hfsh Hppat He HJ3 Hio3).
  + apply (hd_keep1 regs2 regs3 [5; 10; 20; 25; 27]%bv Hk3). hd_sub.
  + exact Hm3.
  + exact Z1.
  + exact Z2.
  + exact V3.
  + exact R5'.
  + exact R10'.
  + hd_kr Hk3 R17.
  + exact R20'.
  + exact R25'.
  + exact R27'.
  + exact Hsufr.
  + exact Hkd'.
  + reflexivity.
  + lia.
  + lia.
- (* r = [c]: c read, p = 0 *)
  change (Z.of_nat (length [cb])) with 1 in Hc2, Vf8, R25, Hra, Hdis, Hin_keep.
  destruct (Hg 0%nat ltac:(cbn; lia)) as [Vc _]. cbn [nth hd_zbytes map Z.of_nat] in Vc. rewrite Z.add_0_r in Vc.
  pose proof (Cursor.byte_range cb) as Bc.
  eapply SRr_bind.
  { exact (hd_T1 B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs2 _ _ _ 1 Hctx R19 R25 ltac:(lia)). }
  intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & Hio3 & Hk3 & Hm3 & Hp3 & Z3).
  change (mkCfg (mkst regs3 (Z_to_bv 64 HD_K) mem3 (seg_rom rsegs)) md3) with (cfg_at rsegs HD_K regs3 mem3 md3).
  assert (Hctx3 : hd_ctx B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx)
    (x_own cx) (x_k cx) ly2 S2 W2 mem3 md3 (e_R (x_e cx)) (e_F (x_e cx)) (x_pos cx))
    by (destruct Hctx as (_ & Hc); exact (conj HJ3 Hc)).
  eapply SRr_bind.
  { refine (hd_K1 B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs3 _ _ _ (hs_cur rsegs cx rest [cb]) (bv_unsigned cb) Hctx3
      _ _ _ _ Hc1 ltac:(lia) _ _ _ Bc _ _).
    - hd_kr Hk3 R9.
    - hd_kr Hk3 R23.
    - hd_kr Hk3 R14.
    - hd_kr Hk3 R24.
    - eapply val_mem_kept; [|exact V58]. intros q Hq. apply Hm3; [lia | cbv [hd_wT]; lia].
    - eapply val_mem_kept; [|exact Vf8]. intros q Hq. apply Hm3; [lia | cbv [hd_wT]; lia].
    - eapply val_mem_kept; [|exact Vc]. intros q Hq. cbn in Hq.
      exact (proj1 (Hin_keep mem3 Hm3 (hs_cur rsegs cx rest [cb] + q) ltac:(lia))).
    - apply (hm_ra_kept rsegs _ _ _ _ _ _ _ Hra). intros x Hx. exact (proj2 (Hin_keep mem3 Hm3 x Hx)).
    - intros X. apply (proj1 (Hdis (hs_cur rsegs cx rest [cb]) ltac:(lia))). lia. }
  intros W4 c4 _ (-> & regs4 & mem4 & md4 & -> & HJ4 & Hio4 & Hk4 & Hm4 & Hp4 & ((K5 & K10 & K20 & K24 & K27) & V4)).
  change (mkCfg (mkst regs4 (Z_to_bv 64 HD_CH) mem4 (seg_rom rsegs)) md4) with (cfg_at rsegs HD_CH regs4 mem4 md4).
  apply (hd_after_K cx POST rest i k sh np ps cnt es (kb :: [cb]) [cb] [] (bv_unsigned cb) 0 (hs_cur rsegs cx rest [cb] + 1)
    ly2 S2 W2 regs2 mem2 md2 regs4 mem4 md4 Hst HDIG HODD Hlps Hles Hb Hat0 Hfsh Hppat He).
  + destruct Hctx as (_ & Hc). exact (conj HJ4 Hc).
  + exact (same_io_trans _ _ _ Hio3 Hio4).
  + apply (hd_keep2 regs2 regs3 regs4 [] [5; 10; 11; 12; 20; 24; 27]%bv hd_clob Hk3 Hk4). hd_sub.
  + apply (hd_mem2 _ mem2 mem3 mem4 _ _ _ Hm3 Hm4). cbv [hd_wTCN]. tauto.
  + apply (hd_zero_kept W2 mem3 mem4 _ 4 12 Z3). intros q Hq. apply Hm4; [lia | cbv [hd_wN]; lia].
  + exact V4.
  + exact K5.
  + exact K10.
  + rewrite Hk4; [|cbv; discriminate | hd_notin]. hd_kr Hk3 R17.
  + rewrite Hk4; [|cbv; discriminate | hd_notin]. hd_kr Hk3 R19.
  + exact K20.
  + exact K24.
  + exact K27.
  + unfold hs_cur. cbn [length Z.of_nat]. lia.
  + lia.
  + exact (hd_suffix_tl rest [] cb Hsufr).
  + exact Hkd'.
  + reflexivity.
  + exact Bc.
  + lia.
- (* r = c :: p :: r3: both read *)
  set (n := Z.of_nat (length (cb :: pb :: r3))) in *.
  assert (Hn2 : 2 <= n) by (subst n; cbn [length]; lia).
  destruct (Hg 0%nat ltac:(cbn; lia)) as [Vc _]. cbn [nth hd_zbytes map Z.of_nat] in Vc. rewrite Z.add_0_r in Vc.
  destruct (Hg 1%nat ltac:(cbn; lia)) as [Vp _]. cbn [nth hd_zbytes map Z.of_nat] in Vp.
  pose proof (Cursor.byte_range cb) as Bc. pose proof (Cursor.byte_range pb) as Bp.
  eapply SRr_bind.
  { exact (hd_T1 B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs2 _ _ _ n Hctx R19 R25 ltac:(lia)). }
  intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & Hio3 & Hk3 & Hm3 & Hp3 & Z3).
  change (mkCfg (mkst regs3 (Z_to_bv 64 HD_K) mem3 (seg_rom rsegs)) md3) with (cfg_at rsegs HD_K regs3 mem3 md3).
  assert (Hctx3 : hd_ctx B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx)
    (x_own cx) (x_k cx) ly2 S2 W2 mem3 md3 (e_R (x_e cx)) (e_F (x_e cx)) (x_pos cx))
    by (destruct Hctx as (_ & Hc); exact (conj HJ3 Hc)).
  eapply SRr_bind.
  { refine (hd_K2 B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs3 _ _ _ (hs_cur rsegs cx rest (cb :: pb :: r3)) n
      (bv_unsigned cb) (bv_unsigned pb) Hctx3 _ _ _ _ _ ltac:(lia) Hc1 ltac:(lia) _ _ _ Bc _ Bp _ _).
    - hd_kr Hk3 R9.
    - hd_kr Hk3 R23.
    - hd_kr Hk3 R14.
    - hd_kr Hk3 R24.
    - hd_kr Hk3 R25.
    - eapply val_mem_kept; [|exact V58]. intros q Hq. apply Hm3; [lia | cbv [hd_wT]; lia].
    - eapply val_mem_kept; [|exact Vf8]. intros q Hq. apply Hm3; [lia | cbv [hd_wT]; lia].
    - eapply val_mem_kept; [|exact Vc]. intros q Hq. cbn in Hq.
      exact (proj1 (Hin_keep mem3 Hm3 (hs_cur rsegs cx rest (cb :: pb :: r3) + q) ltac:(lia))).
    - eapply val_mem_kept; [|exact Vp]. intros q Hq. cbn in Hq.
      exact (proj1 (Hin_keep mem3 Hm3 (hs_cur rsegs cx rest (cb :: pb :: r3) + 1 + q) ltac:(lia))).
    - apply (hm_ra_kept rsegs _ _ _ _ _ _ _ (range_addressable_sub _ _ _ _ (hs_cur rsegs cx rest (cb :: pb :: r3)) 2
        Hra ltac:(lia) ltac:(lia))).
      intros x Hx. exact (proj2 (Hin_keep mem3 Hm3 x ltac:(lia))).
    - intros a Ha X. apply (proj1 (Hdis a ltac:(lia))). lia. }
  intros W4 c4 _ (-> & regs4 & mem4 & md4 & -> & HJ4 & Hio4 & Hk4 & Hm4 & Hp4 & ((K5 & K10 & K20 & K24 & K27) & V4)).
  change (mkCfg (mkst regs4 (Z_to_bv 64 HD_CH) mem4 (seg_rom rsegs)) md4) with (cfg_at rsegs HD_CH regs4 mem4 md4).
  apply (hd_after_K cx POST rest i k sh np ps cnt es (kb :: cb :: pb :: r3) (cb :: pb :: r3) r3
    (bv_unsigned cb) (bv_unsigned pb) (hs_cur rsegs cx rest (cb :: pb :: r3) + 2)
    ly2 S2 W2 regs2 mem2 md2 regs4 mem4 md4 Hst HDIG HODD Hlps Hles Hb Hat0 Hfsh Hppat He).
  + destruct Hctx as (_ & Hc). exact (conj HJ4 Hc).
  + exact (same_io_trans _ _ _ Hio3 Hio4).
  + apply (hd_keep2 regs2 regs3 regs4 [] [5; 10; 11; 12; 20; 24; 27]%bv hd_clob Hk3 Hk4). hd_sub.
  + apply (hd_mem2 _ mem2 mem3 mem4 _ _ _ Hm3 Hm4). cbv [hd_wTCN]. tauto.
  + apply (hd_zero_kept W2 mem3 mem4 _ 4 12 Z3). intros q Hq. apply Hm4; [lia | cbv [hd_wN]; lia].
  + replace (Z.of_nat (length r3)) with (n - 2) by (subst n; cbn [length]; lia). exact V4.
  + exact K5.
  + exact K10.
  + rewrite Hk4; [|cbv; discriminate | hd_notin]. hd_kr Hk3 R17.
  + rewrite Hk4; [|cbv; discriminate | hd_notin]. hd_kr Hk3 R19.
  + exact K20.
  + exact K24.
  + exact K27.
  + unfold hs_cur. cbn [length]. lia.
  + lia.
  + exact (hd_suffix_tl rest r3 pb (hd_suffix_tl rest (pb :: r3) cb Hsufr)).
  + exact Hkd'.
  + reflexivity.
  + exact Bc.
  + exact Bp.
Qed.

(* ======================================== the head ======================================== *)
Lemma r7_head : r7_head_stmt rsegs B MT.
Proof.
unfold r7_head_stmt. intros cx POST rest i k kd Hst Hkd HDIG HODD.
split; [exact (hd_piece_D cx POST rest i k kd Hst Hkd HDIG HODD) | exact (hd_piece_D0E cx POST rest i k Hst HDIG)].
Qed.

End g.

Print Assumptions r7_head.

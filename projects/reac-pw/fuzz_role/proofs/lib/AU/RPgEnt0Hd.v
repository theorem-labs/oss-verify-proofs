(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of proofs/reac-pw/fuzz_role/lib/A/RPgX01.v at 9bffaa83ff88
   [Apache-2.0] (rx_reg_atom / rx_reg_ext / rx_ew_reg / rx_st_region / rx_chunk_zero / rx_flag0_of, the saved-slot
   chunk list rx_sv_chunks, the numeral tactics z5 / z5g and the flag-store tactic rx_run_flag, which passes
   aj_flag_store its sixteen journal arguments) and of proofs/reac-pw/fuzz_role/lib/A/RPgCheck.v at 77f59d02b018
   [Apache-2.0] (the shape of a `ret` leaf into a callee post), for reac-pw/fuzz_rate's image A: the walk is
   check_csv's release and epilogue, the side-stack class is 2 instead of 3, and the post is RtPgCSpec.rt_cpost_o,
   whose owned-set conjunct is discharged from the cut's layout, chunk and frame equalities. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgCcsvS3.v, with its module paths and module names changed; 623 of its 664 lines of code are new or changed and 285 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgEnt0Hd.v at 21da95a5fcd3 for image B (fuzz_rate.asan-ubsan): the walk is lib/AU/RtPgEnt0HdBB.v's seven blocks (the reads' trap tests inside the token runs, the cursor cell R+0x128 written by the head, the ch stores after the reads), chained by what is left after the kind byte; the facts come from lib/AU/RtPgSegB.v's cuts (rsb_L_D, rsb_start_M01, rsb_in) and RtPgImgB's hi_w1; the arm cut is RtPgEnt0DefB's (rt7b_L_arm over rsb_L_Dc, t1 / s2 / s9 and the cell R+0x128, the frame's shadow row from rsb_PJ to rsb_PG, e62 at F+0x210); the top lemma takes B and MT; names hd_ -> hdb_, rt7_ -> rt7b_, rs_ -> rsb_, rtm_ -> rtmb_. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/AU/RtPgEnt0HdB.v, with its module paths and module names changed; 196 of its 664 lines of code are new or changed and 196 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgEnt0Hd.v at 21da95a5fcd3 for image B (fuzz_rate.asan-ubsan): the walk is lib/AU/RtPgEnt0HdBB.v's seven blocks (the reads' trap tests inside the token runs, the cursor cell R+0x128 written by the head, the ch stores after the reads), chained by what is left after the kind byte; the facts come from lib/AU/RtPgSegB.v's cuts (rsb_L_D, rsb_start_M01, rsb_in) and RtPgImgB's hi_w1; the arm cut is RtPgEnt0DefB's (rt7b_L_arm over rsb_L_Dc, t1 / s2 / s9 and the cell R+0x128, the frame's shadow row from rsb_PJ to rsb_PG, e62 at F+0x210); the top lemma takes B and MT; names hd_ -> hdb_, rt7_ -> rt7b_, rs_ -> rsb_, rtm_ -> rtmb_. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/AU/RtPgEnt0HdB.v at cc5ce244897b for reac-pw/fuzz_role's image B (fuzz_role.asan-ubsan): module paths fuzz_rate -> fuzz_role, the segments lib/AU/Img0.v rsegs; the blocks are lib/AU/RPgEnt0HdB.v's (role B's registers: the shadow offset s11, the kind byte's address a6, s4 = 1, p in s8, the cursor cell R+0x118, &ch from R+0xd0; t2 = 10 is the dispatch's on D0's paths and t3 = 9 comes from the p read on the two-byte path, both carried by the blocks' keep clauses); the cuts are lib/AU/RPgSeg.v's (rs_L_D with s4 = 1 and s10 = -8 in rs_L_Dc, no header cells), rl_seg_pre is lib/A/RPgCSpec.v's (the prologue's shadow row in it), role_himg_B's hi_w1 and hi_rsz = 0x200; names rsb_ -> rs_, rtmb_ -> rm_, rt7b_ -> r7b_. *)
(* reac-pw/fuzz_role image B (fuzz_role.asan-ubsan, pinned sha256
   b255d4935da5af137a3967dbe33380ea43be8e78bfe05d1e356e0a2be8a69ff0; every address measured on the unstripped twin
   dc791783f32962615e18a5f5cffae758ba56eb5dc87f70913c3579b101b4406a, same loaded bytes): RPgEnt0Def.r7b_head_stmt,
   the head of ent_build's case 0 from both its entries (D0 = 0x80c14 with the kind byte read, D0E = 0x80c88 with no
   input left) to the two arms DIG = 0x80ce8 and ODD = 0x815e0. Proves no function (kind: segment lemma).

   HOW. The walk is the seven blocks of lib/AU/RPgEnt0HdB.v, chained with SRr_bind, by what is left of the input
   after the kind byte (r):
     r = []          hdb_T0                     to DIG with c = p = 0, nothing more read, R+0x118 := the cursor
     r = [c]         hdb_T1, hdb_K1, hdb_C1     c read, p = 0, R+0x118 := the cursor after c
     r = c :: p :: _ hdb_T1, hdb_K2, hdb_C2     c and p read, R+0x118 := the cursor after p
     D0E             hdb_TE                     to DIG with c = p = 0
   and hdb_C1 / hdb_C2 go to DIG when c < 200, to ODD otherwise. The facts each block asks are read off rs_cut_D
   (the registers of RPgSeg.rs_L_D and the real frame's cell [R+0xd0] = &ch of rs_Kc) and off rs_start_M01
   (hdb_D_input: the input bytes at the cursor and their shadow, carried from the segment's start memory to the cut's
   by rs_core's keep clause; rs_in puts the input outside the callees' stack, role_himg_B's hi_w1 and pp, and its
   shadow lies outside the frame's shadow row because every byte of the prologue's row is 8 or more,
   RPgMem.rm_ra_not_fsh); they are carried across the earlier blocks by their frame conditions. The cut at the
   arm (hdb_to_arm) is the cut at the entry with the blocks' writes: the frame's shadow row from rs_PJ to rs_PG
   (t's twelve and ch's three granules in scope), the cursor cell R+0x118 (in hi_w1's (XR, 0x48, 0x118), so in
   rs_E1) and the registers of the arm (t1 = what is left, s2 = &ch, s8 = p, a3 = c and, at DIG, t0 = 4, t2 = 10,
   t3 = 9); every other location of rs_L_Dc is kept (the blocks write no register of it and no cell of it). *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG0v YI00 YI0m.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YI16 YM05 YO09 YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Import Cursor Model Layout Accessors Spa Tables.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import RPgBase RPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import RPgImgA RPgMem RPgSeg RPgSteps.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import RPgEnt0Def RPgEnt0HdB.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import Img0.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the cut record's projections, with the segments implicit *)
Local Arguments x_STK {segs} _. Local Arguments x_sp0 {segs} _. Local Arguments x_FP {segs} _.
Local Arguments x_ly {segs} _. Local Arguments x_S {segs} _. Local Arguments x_W0 {segs} _.
Local Arguments x_mem0 {segs} _. Local Arguments x_md0 {segs} _. Local Arguments x_own {segs} _.
Local Arguments x_k {segs} _. Local Arguments x_regs {segs} _. Local Arguments x_lyc {segs} _.
Local Arguments x_Sc {segs} _. Local Arguments x_W {segs} _. Local Arguments x_memc {segs} _.
Local Arguments x_mdc {segs} _. Local Arguments x_RLO {segs} _. Local Arguments x_RHI {segs} _.
Local Arguments x_e {segs} _. Local Arguments x_pos {segs} _.

(* every register any block of the head writes or pins *)
Definition hdb_clob : list (bv 5) := [5; 6; 7; 10; 11; 12; 13; 18; 22; 24; 28]%bv.

(* a register outside a concrete clobber list *)
Ltac hdb_notin :=
let H := fresh "H" in intros H;
cbv [hdb_clob hdb_clobT0 hdb_clobTE hdb_clobK hdb_clobC1 hdb_clobC2] in H; cbn [In] in H;
repeat (destruct H as [H|H]; [apply (f_equal (@bv_unsigned 5)) in H; vm_compute in H; discriminate H|]); exact H.
(* a register a block kept: rewrite with its keep clause Hk, then close with R *)
Ltac hdb_kr Hk R := rewrite Hk; [exact R | cbv; discriminate | hdb_notin].
(* one clobber list inside another *)
Ltac hdb_sub := let q := fresh "q" in let X := fresh "X" in
intros q X; cbv [hdb_clob hdb_clobT0 hdb_clobTE hdb_clobK hdb_clobC1 hdb_clobC2] in X |- *; cbn [In app] in X |- *;
tauto.
(* membership in a concrete location list of a cut *)
Ltac eb_in := cbn [rs_L_D rs_L_Dc rs_L_Dc0 rs_Rc0 rs_Kc rs_podc app];
repeat (first [left; reflexivity | right]).

(* an input byte outside the frame's objects F + 0x20 .. F + 0x278 (role_himg_B hi_w1) has its shadow outside the
   head's granules 4 .. 22 of the frame's shadow row *)
Lemma hdb_sh_not_row : forall F x, F mod 8 = 0 -> ~ (F + 0x20 <= x < F + 0x278) ->
~ (shadow_addr F + 4 <= shadow_of_addr SHADOW_OFF x < shadow_addr F + 23).
Proof.
intros F x HF Hx Hin. unfold shadow_addr, shadow_of_addr in Hin.
pose proof (Z.div_mod x 8 ltac:(lia)) as Dx. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Mx.
pose proof (Z.div_mod F 8 ltac:(lia)) as DF. rewrite HF in DF. lia.
Qed.
Lemma hdb_suffix_tl : forall (rest r : list byte) x, rs_suffix rest (x :: r) -> rs_suffix rest r.
Proof.
intros rest r x (j & Hj & E). exists (S j). split.
- destruct (Nat.le_gt_cases (length rest) j) as [Hle|Hlt]; [|lia].
  rewrite skipn_all2 in E by exact Hle. discriminate E.
- change (S j) with (1 + j)%nat. rewrite <- skipn_skipn, <- E. reflexivity.
Qed.
Lemma hdb_frame_addr_le : forall n ly ly' cid pos, layout_le n ly ly' -> frame_addr ly' cid pos = frame_addr ly cid pos.
Proof. intros n ly ly' cid pos Hle. unfold frame_addr. destruct Hle as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. Qed.
(* the first block's image at a pod-loop cut has the block's size [proofs/reac-pw/fuzz_role/lib/A/RPgEntBCut.v eb_pc_len] *)
Lemma hdb_pc_len : forall sh ps es, rs_wf sh ps -> Forall ent_wf es -> (length es < 32)%nat -> (length ps <= 2)%nat ->
Z.of_nat (length (pc_image (PbCut sh ps (Some es)))) = Layout.PP_SIZE.
Proof.
intros sh ps es (Hsh & Hkv & Hall & Hps3) Hes Hes32 Hps2.
assert (Hpv : Forall (fun kv => pval_wf (snd kv)) ps) by (eapply Forall_impl; [| exact Hkv]; intros kv [_ H]; exact H).
unfold pc_image. apply length_pp_image.
- destruct (pc_buf_len_open sh ps es Hpv Hall Hes) as [L _]. cbn [pc_shape pc_props pc_open]. unfold POD_BUF_MAX. lia.
- unfold pc_ents. cbn [pc_props pc_open]. destruct (first_params ps) as [[iv|es']|] eqn:E; [cbn; lia | | lia].
  unfold first_params in E. destruct (find _ _) as [kv|] eqn:Fd; [|discriminate]. cbn in E. injection E as E.
  apply find_some in Fd as [Hin _]. rewrite Forall_forall in Hpv. specialize (Hpv kv Hin). rewrite E in Hpv. exact Hpv.
- unfold pc_ents. cbn [pc_props pc_open]. destruct (first_params ps) as [[iv|es']|] eqn:E; [constructor | |].
  + unfold first_params in E. destruct (find _ _) as [kv|] eqn:Fd; [|discriminate]. cbn in E. injection E as E.
    apply find_some in Fd as [Hin _]. apply all_ents_Forall in Hall. rewrite Forall_forall in Hall.
    specialize (Hall kv Hin). rewrite E in Hall. cbn beta iota in Hall.
    eapply Forall_impl; [| exact Hall]. intros e' (_ & Hb & Hs). lia.
  + eapply Forall_impl; [| exact Hes]. intros e' (_ & Hb & Hs). lia.
Qed.

Section g0. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section g.
Variable B : asyms.
Variable MT : ameter_ops.

(* ======================================== moving facts across blocks ======================================== *)
Lemma hdb_at_get : forall H mem regs e (L : list (rl_loc * Z)) l v,
rs_at rsegs H mem regs e L -> In (l, v) L -> rl_at rsegs H mem regs e l v.
Proof. intros H mem regs e L l v HL Hin. exact (proj1 (Forall_forall _ _) HL (l, v) Hin). Qed.
(* what a location needs to keep its value between two states [proofs/reac-pw/fuzz_role/lib/A/RPgEnt0Hd.v] *)
Definition hdb_kept_loc (e : rl_env) (regs regs' : bvmap 5 word) (H : word -> bool)
(mem mem' : word -> option byte) (l : rl_loc) : Prop :=
match l with
| LReg r => getr regs' (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)
| LCell b o => forall j, 0 <= j < 8 -> aview rsegs H mem' (rl_xv e b + o + j) = aview rsegs H mem (rl_xv e b + o + j)
end.
Lemma hdb_at_move : forall H mem regs mem' regs' e L,
rs_at rsegs H mem regs e L -> Forall (fun f => hdb_kept_loc e regs regs' H mem mem' (fst f)) L ->
rs_at rsegs H mem' regs' e L.
Proof.
intros H mem regs mem' regs' e L HL HK. unfold rs_at in *.
induction L as [|[l v] L IH]; [constructor|].
inversion HL as [|? ? H1 H2]; subst. inversion HK as [|? ? K1 K2]; subst.
constructor; [|apply IH; assumption].
cbn [fst snd] in *. destruct l as [r|b o]; cbn [rl_at hdb_kept_loc] in *.
- rewrite K1. exact H1.
- eapply val_mem_kept; [|exact H1]. intros j Hj. apply K1. lia.
Qed.
Lemma hdb_keep1 : forall (r2 r3 : bvmap 5 word) (c1 : list (bv 5)),
(forall q : bv 5, bv_unsigned q <> 0 -> ~ In q c1 -> getr r3 q = getr r2 q) ->
(forall q, In q c1 -> In q hdb_clob) ->
forall q : bv 5, bv_unsigned q <> 0 -> ~ In q hdb_clob -> getr r3 q = getr r2 q.
Proof. intros r2 r3 c1 K1 Hs q Hq Hn. exact (K1 q Hq (fun X => Hn (Hs q X))). Qed.
Lemma hdb_keep3 : forall (r2 r3 r4 r5 : bvmap 5 word) (c1 c2 c3 : list (bv 5)),
(forall q : bv 5, bv_unsigned q <> 0 -> ~ In q c1 -> getr r3 q = getr r2 q) ->
(forall q : bv 5, bv_unsigned q <> 0 -> ~ In q c2 -> getr r4 q = getr r3 q) ->
(forall q : bv 5, bv_unsigned q <> 0 -> ~ In q c3 -> getr r5 q = getr r4 q) ->
(forall q, In q (c1 ++ c2 ++ c3) -> In q hdb_clob) ->
forall q : bv 5, bv_unsigned q <> 0 -> ~ In q hdb_clob -> getr r5 q = getr r2 q.
Proof.
intros r2 r3 r4 r5 c1 c2 c3 K1 K2 K3 Hs q Hq Hn.
assert (N : ~ In q (c1 ++ c2 ++ c3)) by (intros X; exact (Hn (Hs q X))).
rewrite (K3 q Hq ltac:(intros X; apply N; apply in_or_app; right; apply in_or_app; right; exact X)),
  (K2 q Hq ltac:(intros X; apply N; apply in_or_app; right; apply in_or_app; left; exact X)),
  (K1 q Hq ltac:(intros X; apply N; apply in_or_app; left; exact X)).
reflexivity.
Qed.
Lemma hdb_mem2 : forall H m2 m3 m4 (W1 W2 Wt : Z -> Prop),
(forall a, 0 <= a < 2 ^ 64 -> ~ W1 a -> aview rsegs H m3 a = aview rsegs H m2 a) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ W2 a -> aview rsegs H m4 a = aview rsegs H m3 a) ->
(forall a, W1 a \/ W2 a -> Wt a) ->
forall a, 0 <= a < 2 ^ 64 -> ~ Wt a -> aview rsegs H m4 a = aview rsegs H m2 a.
Proof.
intros H m2 m3 m4 W1 W2 Wt K1 K2 Hs a Ha Hn.
rewrite (K2 a Ha ltac:(intros X; apply Hn, Hs; right; exact X)),
  (K1 a Ha ltac:(intros X; apply Hn, Hs; left; exact X)). reflexivity.
Qed.
Lemma hdb_mem3 : forall H m2 m3 m4 m5 (W1 W2 W3 Wt : Z -> Prop),
(forall a, 0 <= a < 2 ^ 64 -> ~ W1 a -> aview rsegs H m3 a = aview rsegs H m2 a) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ W2 a -> aview rsegs H m4 a = aview rsegs H m3 a) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ W3 a -> aview rsegs H m5 a = aview rsegs H m4 a) ->
(forall a, W1 a \/ W2 a \/ W3 a -> Wt a) ->
forall a, 0 <= a < 2 ^ 64 -> ~ Wt a -> aview rsegs H m5 a = aview rsegs H m2 a.
Proof.
intros H m2 m3 m4 m5 W1 W2 W3 Wt K1 K2 K3 Hs a Ha Hn.
rewrite (K3 a Ha ltac:(intros X; apply Hn, Hs; right; right; exact X)),
  (K2 a Ha ltac:(intros X; apply Hn, Hs; right; left; exact X)),
  (K1 a Ha ltac:(intros X; apply Hn, Hs; left; exact X)). reflexivity.
Qed.
Lemma hdb_zero_kept : forall W m m' F j n,
hdb_zero W m F j n ->
(forall i, j <= i < j + n -> aview rsegs (w_H W) m' (shadow_addr F + i) = aview rsegs (w_H W) m (shadow_addr F + i)) ->
hdb_zero W m' F j n.
Proof. intros W m m' F j n Z0 K i Hi. rewrite K by exact Hi. exact (Z0 i Hi). Qed.

(* the frame's shadow row after two scope stores of v *)
Lemma hdb_fsh_two : forall H mem H' mem' F pat (j1 k1 j2 k2 : nat) v,
rl_fsh rsegs H mem F pat ->
(forall i, Z.of_nat j1 <= i < Z.of_nat (j1 + k1) -> aview rsegs H' mem' (shadow_addr F + i) = Some v) ->
(forall i, Z.of_nat j2 <= i < Z.of_nat (j2 + k2) -> aview rsegs H' mem' (shadow_addr F + i) = Some v) ->
(forall i, 0 <= i < Z.of_nat (length pat) -> ~ (Z.of_nat j1 <= i < Z.of_nat (j1 + k1)) ->
 ~ (Z.of_nat j2 <= i < Z.of_nat (j2 + k2)) ->
 aview rsegs H' mem' (shadow_addr F + i) = aview rsegs H mem (shadow_addr F + i)) ->
rl_fsh rsegs H' mem' F (rm_setn (rm_setn pat j1 k1 v) j2 k2 v).
Proof.
intros H mem H' mem' F pat j1 k1 j2 k2 v P S1 S2 K i Hi.
rewrite !rm_setn_len in Hi.
rewrite rm_nth_setn by (rewrite rm_setn_len; lia).
destruct ((j2 <=? Z.to_nat i)%nat && (Z.to_nat i <? j2 + k2)%nat) eqn:E2.
- apply andb_prop in E2 as [A1 A2]. apply Nat.leb_le in A1. apply Nat.ltb_lt in A2. apply S2. lia.
- rewrite rm_nth_setn by lia.
  destruct ((j1 <=? Z.to_nat i)%nat && (Z.to_nat i <? j1 + k1)%nat) eqn:E1.
  + apply andb_prop in E1 as [A1 A2]. apply Nat.leb_le in A1. apply Nat.ltb_lt in A2. apply S1. lia.
  + rewrite K; [exact (P i ltac:(lia)) | lia | |].
    * intros [A1 A2]. apply andb_false_iff in E1 as [E|E]; [apply Nat.leb_gt in E | apply Nat.ltb_ge in E]; lia.
    * intros [A1 A2]. apply andb_false_iff in E2 as [E|E]; [apply Nat.leb_gt in E | apply Nat.ltb_ge in E]; lia.
Qed.

(* ======================================== the cut's journal part ======================================== *)
Lemma hdb_core_step : forall cx (Ew : Z -> Prop) ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3,
rs_core rsegs B MT cx (rs_E1 rsegs cx) ly2 S2 W2 regs2 mem2 md2 ->
ajournal rsegs B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx) (x_own cx)
  ly2 S2 W2 mem3 md3 (x_k cx) ->
(forall r : Z, r = 2 \/ r = 3 \/ r = 4 -> getr regs3 (Z_to_bv 5 r) = getr regs2 (Z_to_bv 5 r)) ->
same_io md2 md3 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ Ew a -> aview rsegs (w_H W2) mem3 a = aview rsegs (w_H W2) mem2 a) ->
(forall a, Ew a -> rs_E1 rsegs cx a) ->
rs_core rsegs B MT cx (rs_E1 rsegs cx) ly2 S2 W2 regs3 mem3 md3.
Proof.
intros cx Ew ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 Hc HJ3 Hr3 Hio3 Hm3 HEw.
unfold rs_core, rs_mid in *. destruct Hc as (HJ & Hr & Hf & Hp & Hio & Hmo & Hm).
split; [exact HJ3|].
split; [intros r Hr'; rewrite (Hr3 r Hr'); exact (Hr r Hr')|].
split; [exact Hf|]. split; [exact Hp|].
split; [eapply same_io_trans; [exact Hio | exact Hio3]|].
split; [exact Hmo|].
intros a Ha Hs HE. rewrite <- (Hm a Ha Hs HE). apply Hm3; [exact Ha|]. intros HW. exact (HE (HEw a HW)).
Qed.
(* the head's writes (the frame's shadow granules 4 .. 22 and the cursor cell R+0x118) lie in role_himg_B hi_w1's
   (XShF, 4, 75) and (XR, 0x48, 0x118) *)
Lemma hdb_E1 : forall cx a, hdb_wTC (e_F (x_e cx)) (e_R (x_e cx)) a -> rs_E1 rsegs cx a.
Proof.
intros cx a Ha. left. unfold rl_inw. cbn [hi_w1 role_himg_B].
destruct Ha as [Ha|[Ha|Ha]]; cbv [hdb_wT hdb_wCh hdb_wCell] in Ha.
- apply Exists_cons_tl. apply Exists_cons_hd. cbn [rl_xv fst snd]. lia.
- apply Exists_cons_tl. apply Exists_cons_hd. cbn [rl_xv fst snd]. lia.
- do 3 apply Exists_cons_tl. apply Exists_cons_hd. cbn [rl_xv fst snd]. lia.
Qed.
Lemma hdb_base_move : forall cx sh np ps cnt es rest rr r r' ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3,
rs_pod_base rsegs B MT cx sh np ps cnt es rest rr r ly2 S2 W2 regs2 mem2 md2 ->
rs_core rsegs B MT cx (rs_E1 rsegs cx) ly3 S3 W3 regs3 mem3 md3 -> rs_suffix rest r' ->
rs_pod_base rsegs B MT cx sh np ps cnt es rest rr r' ly3 S3 W3 regs3 mem3 md3.
Proof.
intros cx sh np ps cnt es rest rr r r' ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3 (_ & Hin & _ & Hr) Hc Hs.
exact (conj Hc (conj Hin (conj Hs Hr))).
Qed.

(* a cut's context for the blocks, and where F and pp lie *)
Lemma hdb_cut_facts : forall cx E ly2 S2 W2 regs2 mem2 md2,
rs_pre rsegs B cx -> rs_core rsegs B MT cx E ly2 S2 W2 regs2 mem2 md2 ->
hdb_ctx B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx) (x_own cx) (x_k cx)
  ly2 S2 W2 mem2 md2 (e_R (x_e cx)) (e_F (x_e cx)) (x_pos cx) /\
in_app (e_F (x_e cx)) 1024 /\ in_app (e_pp (x_e cx)) Layout.PP_SIZE.
Proof.
intros cx E ly2 S2 W2 regs2 mem2 md2 Hpre Hcore.
pose proof (AR_laws_ok rsegs B) as LAWS.
destruct Hpre as (HJc & _ & _ & _ & _ & ES & ER16 & ERS & ESTK & Hown & EF & _ & _ & Hppb & _).
destruct Hcore as (HJ & _).
pose proof HJc as (HARc & Hlyc & _ & _ & _ & Hfrsc & _).
pose proof HJ as (_ & Hly & _).
cbn [hi_cid hi_rsz role_himg_B] in Hown, EF, ERS.
assert (Hin4 : In (4, x_pos cx) (frames (x_Sc cx))) by (rewrite Hfrsc; apply in_or_app; left; exact Hown).
destruct (al_frames _ _ LAWS _ _ _ _ _ 4 (x_pos cx) HARc Hin4) as (_ & HFapp & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HARc Hppb) as (_ & _ & _ & Happ & _).
split; [|split].
- split; [exact HJ|]. split; [exact ER16|]. split; [rewrite <- ES; exact ERS|]. split; [exact ESTK|].
  split; [exact Hown|]. rewrite EF.
  rewrite (hdb_frame_addr_le _ _ _ 4 (x_pos cx) Hly), (hdb_frame_addr_le _ _ _ 4 (x_pos cx) Hlyc). reflexivity.
- rewrite EF. exact HFapp.
- exact Happ.
Qed.

(* ===================== the input at the case entry [proofs/reac-pw/fuzz_role/lib/A/RPgEntBCut.v eb_D_input] =====================
   the bytes r at the cursor, their shadow, their place: outside the frame's objects [F+0x20, F+0x278) (in
   role_himg_B hi_w1) *)
Lemma hdb_D_input : forall cx rest sh np ps cnt es rr r kd ly2 S2 W2 regs2 mem2 md2,
rs_start_M01 rsegs B cx rest ->
rs_cut_D rsegs B MT cx sh np ps cnt es rest rr r kd ly2 S2 W2 regs2 mem2 md2 ->
garr8 rsegs (mrestrict (w_H W2) mem2) (rs_cur rsegs cx rest r) (rs_u8s r) /\
range_addressable (aview rsegs (w_H W2) mem2) SHADOW_OFF (rs_cur rsegs cx rest r) (Z.of_nat (length r)) /\
1 <= rs_cur rsegs cx rest r /\ rs_cur rsegs cx rest r + Z.of_nat (length r) <= 2 ^ 47 - 1 /\
amem_range (rs_cur rsegs cx rest r) (Z.of_nat (length r)) /\
(forall a, rs_cur rsegs cx rest r <= a < rs_cur rsegs cx rest r + Z.of_nat (length r) ->
 ~ (e_F (x_e cx) + 0x20 <= a < e_F (x_e cx) + 0x278)).
Proof.
intros cx rest sh np ps cnt es rr r kd ly2 S2 W2 regs2 mem2 md2 HST HD.
pose proof asan_consts as (Hceil & _ & HHB & HHE & HLE).
pose proof HST as (HPRE & Hfsh0 & _ & _ & HIN).
destruct HD as (HPB & _). pose proof HPB as (HCORE & _ & Hsr & _).
destruct (hdb_cut_facts cx _ _ _ _ _ _ _ HPRE HCORE) as (Hctx & HFapp & Hppapp).
destruct (hdb_frame B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hctx)
  as (HF32 & HF0 & HFc & HRc & HR0 & HR1 & Has & _ & _ & _).
destruct HPRE as (_ & _ & HR2 & _).
destruct HCORE as (_ & _ & _ & _ & _ & _ & Hkept).
destruct HIN as (Hel & Hgar & Hra & Hhull & Hamr & Hsrc0 & Hsrc63 & Hdis).
destruct Hsr as (j & Hj & Er).
assert (Hlr : length r = (length rest - j)%nat) by (rewrite Er, length_skipn; reflexivity).
assert (Hcur : rs_cur rsegs cx rest r = e_src (x_e cx) + Z.of_nat j) by (unfold rs_cur; rewrite Hlr; lia).
assert (Hhi : e_src (x_e cx) + e_left (x_e cx) <= 2 ^ 47 - 1).
{ unfold amem_range in Hamr. unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamr. lia. }
assert (HspR : spZ (x_regs cx) = e_R (x_e cx)).
{ unfold spZ. rewrite HR2. unfold w64. apply unsigned_lit_small. lia. }
(* the bytes the walk may have changed since the segment's start *)
set (Wr := fun a => ~ (0 <= a < 2 ^ 64) \/ (e_R (x_e cx) - T_SEG_STK <= a < e_R (x_e cx)) \/ rs_E1 rsegs cx a).
assert (KE : forall x, ~ Wr x -> aview rsegs (w_H W2) mem2 x = aview rsegs (w_H (x_W cx)) (x_memc cx) x).
{ intros x Hx. unfold Wr in Hx. apply Hkept; [tauto | rewrite HspR; tauto | tauto]. }
assert (HFE : in_app (e_F (x_e cx) + 0x20) 0x258)
  by (apply (in_app_sub (e_F (x_e cx)) 1024); [exact HFapp | lia | lia | lia]).
(* a shadow byte of an input byte avoids everything the segment may have written *)
assert (SHW : forall x, e_src (x_e cx) <= x < e_src (x_e cx) + e_left (x_e cx) -> ~ Wr (shadow_of_addr SHADOW_OFF x)).
{ intros x Hx. pose proof (rm_shadow_band x ltac:(unfold kHighMemEnd; lia)) as Hb.
  unfold kLowMemEnd, kHighMemBeg in Hb.
  intros [Hw | [Hw | Hw]]; [lia | lia |].
  destruct Hw as [Hw | Hw].
  - unfold rl_inw in Hw. cbn [hi_w1 role_himg_B] in Hw.
    apply Exists_cons in Hw. destruct Hw as [Hw | Hw]; cbn [fst snd rl_xv] in Hw.
    { exact (rm_shadow_not_app x _ _ ltac:(unfold kHighMemEnd; lia) HFE ltac:(lia)). }
    apply Exists_cons in Hw. destruct Hw as [Hw | Hw]; cbn [fst snd rl_xv] in Hw.
    { exact (rm_ra_not_fsh rsegs _ _ _ _ _ _ Hra Hfsh0 rm_sh_P0_big x Hx
        ltac:(rewrite <- rm_sh_P0, rm_sh_len; cbn [Z.of_nat]; lia)). }
    repeat (apply Exists_cons in Hw; destruct Hw as [Hw | Hw]; cbn [fst snd rl_xv] in Hw; [lia|]).
    apply Exists_nil in Hw. exact Hw.
  - exact (rm_shadow_not_app x _ _ ltac:(unfold kHighMemEnd; lia) Hppapp Hw). }
split.
{ (* the bytes *)
  assert (B0 : rm_bytes rsegs (w_H (x_W cx)) (x_memc cx) (e_src (x_e cx)) rest) by exact Hgar.
  pose proof (rm_bytes_slice rsegs _ _ _ rest j (length rest - j) B0 ltac:(lia)) as B1.
  unfold rm_slice in B1. rewrite firstn_all2 in B1 by (rewrite length_skipn; lia). rewrite <- Er, <- Hcur in B1.
  refine (rm_bytes_kept_wr rsegs Wr _ _ _ _ _ r B1 KE _).
  intros x Hx. rewrite Hlr in Hx. destruct (Hdis x ltac:(lia)) as (D1 & D2 & D3).
  unfold Wr, rs_E1. intros [Hw | [Hw | [Hw | Hw]]]; [lia | exact (D1 Hw) | exact (D2 Hw) | exact (D3 Hw)]. }
split.
{ (* the shadow *)
  apply (rm_ra_kept_wr rsegs Wr (w_H (x_W cx)) (x_memc cx)); [| exact KE |].
  + apply (range_addressable_sub _ _ _ _ _ _ Hra); lia.
  + intros x Hx. apply SHW. lia. }
split; [lia|]. split; [lia|].
split; [unfold amem_range in *; lia|].
intros a Ha. destruct (Hdis a ltac:(lia)) as (D1 & D2 & D3).
intros Hx. apply D2. unfold rl_inw. cbn [hi_w1 role_himg_B]. apply Exists_cons_hd. cbn [fst snd rl_xv]. lia.
Qed.

(* ======================================== the cut at the two arms ======================================== *)
Lemma hdb_to_arm : forall (odd : bool) cx POST rest i k sh np ps cnt es rr r r3 c pb ly2 S2 W2 regs2 mem2 md2
  regs5 mem5 md5,
rs_start_M01 rsegs B cx rest ->
r7b_from_DIG rsegs B MT cx POST rest i k -> r7b_from_ODD rsegs B MT cx POST rest i k ->
(length ps = i)%nat -> (length es = k)%nat ->
rs_pod_base rsegs B MT cx sh np ps cnt es rest rr r ly2 S2 W2 regs2 mem2 md2 ->
rs_at_cx rsegs cx W2 mem2 regs2 (rs_L_Dc rsegs cx sh np ps cnt es) ->
rs_fsh_at rsegs cx W2 mem2 rs_PJ ->
rs_pp_at rsegs cx W2 mem2 (pc_image (PbCut sh ps (Some es))) ->
garr8 rsegs (mrestrict (w_H W2) mem2) (e_F (x_e cx) + 0x210) (rs_u8s (zeros 104)) ->
ajournal rsegs B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx) (x_own cx)
  ly2 S2 W2 mem5 md5 (x_k cx) ->
same_io md2 md5 ->
(forall q : bv 5, bv_unsigned q <> 0 -> ~ In q hdb_clob -> getr regs5 q = getr regs2 q) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ hdb_wTC (e_F (x_e cx)) (e_R (x_e cx)) a ->
 aview rsegs (w_H W2) mem5 a = aview rsegs (w_H W2) mem2 a) ->
hdb_zero W2 mem5 (e_F (x_e cx)) 4 12 -> hdb_zero W2 mem5 (e_F (x_e cx)) 20 3 ->
getr regs5 5 = w64 4 -> getr regs5 7 = w64 10 -> getr regs5 28 = w64 9 -> getr regs5 13 = w64 c ->
getr regs5 6 = w64 (Z.of_nat (length r3)) -> getr regs5 18 = w64 (e_F (x_e cx) + 0xa0) -> getr regs5 24 = w64 pb ->
val_mem rsegs (mrestrict (w_H W2) mem5) (e_R (x_e cx) + 0x118) 8 (rs_cur rsegs cx rest r3) ->
0 <= rs_cur rsegs cx rest r3 < 2 ^ 64 ->
rs_suffix rest r3 -> fst (Cursor.fuzz_u8 rr) mod 10 = 0 -> (c, pb, r3) = r7b_cp_of rr ->
(if odd then 200 <= c < 256 else 0 <= c < 200) -> 0 <= pb < 256 ->
SRr rsegs W2 (cfg_at rsegs (if odd then R7B_ODD else R7B_DIG) regs5 mem5 md5) POST.
Proof.
intros odd cx POST rest i k sh np ps cnt es rr r r3 c pb ly2 S2 W2 regs2 mem2 md2 regs5 mem5 md5
  Hst HDIG HODD Hlps Hles Hb Hat0 Hfsh Hpp He HJ5 Hio5 Hk5 Hm5 Z1 Z2 R5 R7 R28 R13 R6 R18 R24 V118 Hcur
  Hsuf Hkd Hcp Hc Hpb.
pose proof Hst as (Hpre & _).
destruct (hdb_cut_facts cx _ ly2 S2 W2 regs2 mem2 md2 Hpre (proj1 Hb)) as (Hctx & HFapp & Hppapp).
destruct (hdb_frame B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hctx)
  as (HF32 & HF0 & HFc & HRc & HR0 & HR1 & Has & _ & _ & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (hdb_sF (e_F (x_e cx)) ltac:(lia) ltac:(lia)) as [SF0 SF1].
pose proof Hb as (Hcore & Hin & _ & _ & Hwf & _ & _ & _ & _ & _ & _ & _ & _ & Hps2 & _ & Hesw & Hes32 & _).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp, Hppapp.
assert (Hcore5 : rs_core rsegs B MT cx (rs_E1 rsegs cx) ly2 S2 W2 regs5 mem5 md5).
{ apply (hdb_core_step cx (hdb_wTC (e_F (x_e cx)) (e_R (x_e cx))) ly2 S2 W2 regs2 mem2 md2 regs5 mem5 md5 Hcore HJ5).
  - intros q [->|[->| ->]]; (apply Hk5; [cbv; discriminate | hdb_notin]).
  - exact Hio5.
  - exact Hm5.
  - apply hdb_E1. }
pose proof (hdb_base_move cx sh np ps cnt es rest rr r r3 ly2 S2 W2 regs2 mem2 md2 ly2 S2 W2 regs5 mem5 md5
  Hb Hcore5 Hsuf) as Hb5.
assert (Hat5 : rs_at_cx rsegs cx W2 mem5 regs5 (rs_L_Dc rsegs cx sh np ps cnt es)).
{ unfold rs_at_cx in *. apply (hdb_at_move _ _ _ mem5 regs5 _ _ Hat0).
  cbn [rs_L_Dc rs_L_Dc0 rs_Rc0 rs_Kc rs_podc app]; repeat apply Forall_cons; try apply Forall_nil;
    cbn [fst hdb_kept_loc rl_xv].
  all: first [ apply Hk5; [cbv; discriminate | hdb_notin]
             | let j := fresh "j" in let Hj := fresh "Hj" in
               intros j Hj; apply Hm5; [lia | cbv [hdb_wTC hdb_wT hdb_wCh hdb_wCell]; lia] ]. }
assert (Hfsh5 : rs_fsh_at rsegs cx W2 mem5 rs_PG).
{ unfold rs_fsh_at, rs_PG, rs_PJ in *.
  replace (rm_sh true true false false false true false)
    with (rm_setn (rm_setn (rm_sh false false false false false true false) 4 12 0) 20 3 0)
    by (rewrite rm_sh_t_in, rm_sh_ch_in; reflexivity).
  apply (hdb_fsh_two _ _ _ _ _ _ 4 12 20 3 0 Hfsh).
  - intros i0 Hi0. simpl in Hi0. apply Z1. lia.
  - intros i0 Hi0. simpl in Hi0. apply Z2. lia.
  - intros i0 Hi0 N1 N2. rewrite rm_sh_len in Hi0. simpl in Hi0, N1, N2.
    apply Hm5; [lia | cbv [hdb_wTC hdb_wT hdb_wCh hdb_wCell]; lia]. }
assert (Hpp5 : rs_pp_at rsegs cx W2 mem5 (pc_image (PbCut sh ps (Some es)))).
{ unfold rs_pp_at in *. eapply (rm_bytes_kept rsegs); [exact Hpp|]. intros x Hx.
  rewrite (hdb_pc_len sh ps es Hwf Hesw Hes32 Hps2) in Hx. unfold Layout.PP_SIZE in *.
  apply Hm5; [lia | cbv [hdb_wTC hdb_wT hdb_wCh hdb_wCell]; lia]. }
assert (He5 : garr8 rsegs (mrestrict (w_H W2) mem5) (e_F (x_e cx) + 0x210) (rs_u8s (zeros 104))).
{ intros j Hj. destruct (He j Hj) as [V B8]. split; [|exact B8].
  unfold rs_u8s, zeros in Hj. rewrite length_map, rm_length_repeat in Hj.
  eapply val_mem_kept; [|exact V]. intros q Hq.
  apply Hm5; [lia | cbv [hdb_wTC hdb_wT hdb_wCh hdb_wCell]; lia]. }
assert (Harm : rs_at_cx rsegs cx W2 mem5 regs5 (r7b_L_arm rsegs cx sh np ps cnt es rest r3 pb)).
{ unfold r7b_L_arm. unfold rs_at_cx, rs_at in *.
  apply Forall_app. split; [exact Hat5|].
  repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd rl_at rl_xv].
  - exact R6.
  - exact R18.
  - exact R24.
  - rewrite Z.mod_small by lia. exact V118. }
destruct odd; cbv iota in Hc |- *.
- apply (HODD ly2 S2 W2 regs5 mem5 md5 sh np ps cnt es rr r3 c pb Hlps Hles).
  unfold r7b_cut_ODD.
  split; [exact Hb5|].
  split.
  { unfold rs_at_cx, rs_at in *. apply Forall_app. split; [exact Harm|].
    repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd rl_at]. exact R13. }
  split; [exact Hfsh5|]. split; [exact Hpp5|]. split; [exact He5|].
  split; [exact Hkd|]. split; [exact Hcp|]. split; [exact Hc | exact Hpb].
- apply (HDIG ly2 S2 W2 regs5 mem5 md5 sh np ps cnt es rr r3 c pb Hlps Hles).
  unfold r7b_cut_DIG.
  split; [exact Hb5|].
  split.
  { unfold rs_at_cx, rs_at in *. apply Forall_app. split; [exact Harm|].
    repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd rl_at].
    - exact R13. - exact R5. - exact R7. - exact R28. }
  split; [exact Hfsh5|]. split; [exact Hpp5|]. split; [exact He5|].
  split; [exact Hkd|]. split; [exact Hcp|]. split; [exact Hc | exact Hpb].
Qed.

(* ======================================== D0E: no input left ======================================== *)
Lemma hdb_piece_D0E : forall cx POST rest i k,
rs_start_M01 rsegs B cx rest -> r7b_from_DIG rsegs B MT cx POST rest i k ->
r7b_from_ODD rsegs B MT cx POST rest i k -> rs_from_D0E rsegs B MT cx POST rest i k.
Proof.
intros cx POST rest i k Hst HDIG HODD.
unfold rs_from_D0E. intros ly2 S2 W2 regs2 mem2 md2 sh np ps cnt es Hlps Hles Hcut.
destruct Hcut as (Hb & Hat & Hfsh & Hppat & He).
pose proof Hst as (Hpre & _).
destruct (hdb_cut_facts cx _ ly2 S2 W2 regs2 mem2 md2 Hpre (proj1 Hb)) as (Hctx & HFapp & Hppapp).
destruct (hdb_frame B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hctx)
  as (HF32 & HF0 & HFc & HRc & HR0 & HR1 & Has & _ & _ & _).
pose proof asan_consts as (C1 & _).
pose proof Hb as (_ & Hin & Hsuf0 & _).
pose proof Hin as (Hel & _ & _ & _ & _ & Hsrc0 & Hsrc63 & _).
assert (Hcur : 0 <= rs_cur rsegs cx rest [] < 2 ^ 64) by (unfold rs_cur; cbn [length Z.of_nat]; lia).
assert (Hat0 : rs_at_cx rsegs cx W2 mem2 regs2 (rs_L_Dc rsegs cx sh np ps cnt es)).
{ pose proof Hat as Hat'. unfold rs_at_cx, rs_at in Hat' |- *.
  apply Forall_app in Hat' as [Hat' _]. exact Hat'. }
pose proof (hdb_at_get _ _ _ _ _ (LReg 9) _ Hat ltac:(eb_in)) as R9. cbn [rl_at] in R9.
pose proof (hdb_at_get _ _ _ _ _ (LReg 19) _ Hat ltac:(eb_in)) as R19. cbn [rl_at] in R19.
pose proof (hdb_at_get _ _ _ _ _ (LReg 24) _ Hat ltac:(eb_in)) as R24c. cbn [rl_at] in R24c.
pose proof (hdb_at_get _ _ _ _ _ (LCell XR 0xd0) _ Hat ltac:(eb_in)) as VE0. cbn [rl_at rl_xv] in VE0.
rewrite Z.mod_small in VE0 by lia.
eapply SRr_bind.
{ exact (hdb_TE B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs2 _ _ _ _ Hctx R9 R19 R24c Hcur VE0). }
intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & Hio3 & Hk3 & Hm3 & Hp3 &
  ((R5 & R28 & R6 & R24 & R13 & R18) & R7 & (Z1 & Z2 & V118))).
change (mkCfg (mkst regs3 (Z_to_bv 64 R7B_DIG) mem3 (seg_rom rsegs)) md3)
  with (cfg_at rsegs (if false then R7B_ODD else R7B_DIG) regs3 mem3 md3).
apply (hdb_to_arm false cx POST rest i k sh np ps cnt es [] [] [] 0 0 ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3
  Hst HDIG HODD Hlps Hles Hb Hat0 Hfsh Hppat He HJ3 Hio3).
- apply (hdb_keep1 regs2 regs3 hdb_clobTE Hk3). hdb_sub.
- exact Hm3.
- exact Z1.
- exact Z2.
- exact R5.
- exact R7.
- exact R28.
- exact R13.
- exact R6.
- exact R18.
- exact R24.
- exact V118.
- exact Hcur.
- exact Hsuf0.
- reflexivity.
- reflexivity.
- cbv iota. lia.
- lia.
Qed.

(* ======================================== D0: the kind byte read ======================================== *)
Lemma hdb_piece_D : forall cx POST rest i k kd,
rs_start_M01 rsegs B cx rest -> kd mod 10 = 0 ->
r7b_from_DIG rsegs B MT cx POST rest i k -> r7b_from_ODD rsegs B MT cx POST rest i k ->
rs_from_D rsegs B MT cx POST rest i k kd.
Proof.
intros cx POST rest i k kd Hst Hkd HDIG HODD.
unfold rs_from_D. intros ly2 S2 W2 regs2 mem2 md2 sh np ps cnt es rr r Hlps Hles Hcut.
replace (rs_pc_D kd) with HDB_D by (unfold rs_pc_D; rewrite Hkd; reflexivity).
pose proof (hdb_D_input cx rest sh np ps cnt es rr r kd ly2 S2 W2 regs2 mem2 md2 Hst Hcut) as
  (Hg & Hra & Hc1 & Hc2 & Ham & Hdis).
pose proof Hst as (Hpre & _).
destruct Hcut as (Hb & Hat & Hfsh & Hppat & He & _ & Hkdr & Hkd8 & Hrr).
destruct (hdb_cut_facts cx _ ly2 S2 W2 regs2 mem2 md2 Hpre (proj1 Hb)) as (Hctx & HFapp & Hppapp).
destruct (hdb_frame B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hctx)
  as (HF32 & HF0 & HFc & HRc & HR0 & HR1 & Has & _ & _ & _).
pose proof asan_consts as (AC1 & AC2 & AC3 & AC4 & AC5).
destruct (hdb_sF (e_F (x_e cx)) ltac:(lia) ltac:(lia)) as [SF0 SF1].
assert (HF8 : e_F (x_e cx) mod 8 = 0).
{ apply (proj2 (Z.mod_divide (e_F (x_e cx)) 8 ltac:(lia))). apply (proj1 (Z.mod_divide _ 32 ltac:(lia))) in HF32.
  destruct HF32 as [q Hq]. exists (4 * q). lia. }
assert (Hat0 : rs_at_cx rsegs cx W2 mem2 regs2 (rs_L_Dc rsegs cx sh np ps cnt es)).
{ pose proof Hat as Hat'. unfold rs_at_cx, rs_at, rs_L_D in Hat' |- *.
  apply Forall_app in Hat' as [Hat' _]. exact Hat'. }
pose proof (hdb_at_get _ _ _ _ _ (LReg 9) _ Hat ltac:(eb_in)) as R9. cbn [rl_at] in R9.
pose proof (hdb_at_get _ _ _ _ _ (LReg 19) _ Hat ltac:(eb_in)) as R19. cbn [rl_at] in R19.
pose proof (hdb_at_get _ _ _ _ _ (LReg 27) _ Hat ltac:(eb_in)) as R27. cbn [rl_at] in R27.
pose proof (hdb_at_get _ _ _ _ _ (LReg 20) _ Hat ltac:(eb_in)) as R20. cbn [rl_at] in R20.
pose proof (hdb_at_get _ _ _ _ _ (LReg 6) _ Hat ltac:(eb_in)) as R6. cbn [rl_at] in R6.
pose proof (hdb_at_get _ _ _ _ _ (LReg 16) _ Hat ltac:(eb_in)) as R16. cbn [rl_at] in R16.
pose proof (hdb_at_get _ _ _ _ _ (LReg 18) _ Hat ltac:(eb_in)) as R18. cbn [rl_at] in R18.
pose proof (hdb_at_get _ _ _ _ _ (LReg 22) _ Hat ltac:(eb_in)) as R22. cbn [rl_at] in R22.
pose proof (hdb_at_get _ _ _ _ _ (LReg 7) _ Hat ltac:(eb_in)) as R7. cbn [rl_at] in R7.
pose proof (hdb_at_get _ _ _ _ _ (LCell XR 0xd0) _ Hat ltac:(eb_in)) as VE0. cbn [rl_at rl_xv] in VE0.
rewrite Z.mod_small in VE0 by lia.
pose proof Hb as (_ & _ & Hsufr & _).
unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Ham.
destruct rr as [|kb rr0]; [contradiction|].
cbn [Cursor.fuzz_u8] in Hkdr. injection Hkdr as Ekd Er. subst rr0.
assert (Hkd' : fst (Cursor.fuzz_u8 (kb :: r)) mod 10 = 0) by (cbn [Cursor.fuzz_u8 fst]; rewrite <- Ekd; exact Hkd).
(* the input bytes and their shadow keep their values across a block that writes only t's granules *)
assert (Hin_keep : forall (m : word -> option byte),
  (forall a, 0 <= a < 2 ^ 64 -> ~ hdb_wT (e_F (x_e cx)) a -> aview rsegs (w_H W2) m a = aview rsegs (w_H W2) mem2 a) ->
  forall a, rs_cur rsegs cx rest r <= a < rs_cur rsegs cx rest r + Z.of_nat (length r) ->
  aview rsegs (w_H W2) m a = aview rsegs (w_H W2) mem2 a /\
  aview rsegs (w_H W2) m (shadow_of_addr SHADOW_OFF a) = aview rsegs (w_H W2) mem2 (shadow_of_addr SHADOW_OFF a)).
{ intros m Hm a Ha.
  pose proof (rm_shadow_band a ltac:(unfold kHighMemEnd; lia)) as Hsb. unfold kLowMemEnd, kHighMemBeg in Hsb.
  pose proof (hdb_sh_not_row _ a HF8 (Hdis a Ha)) as Hnr.
  split; apply Hm; try lia; cbv [hdb_wT]; lia. }
(* the real frame's cell [R+0xd0] across the reads and t's stores *)
assert (VE_keep : forall (m3 m4 : word -> option byte),
  (forall a, 0 <= a < 2 ^ 64 -> ~ hdb_wT (e_F (x_e cx)) a -> aview rsegs (w_H W2) m3 a = aview rsegs (w_H W2) mem2 a) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ hdb_wNone a -> aview rsegs (w_H W2) m4 a = aview rsegs (w_H W2) m3 a) ->
  val_mem rsegs (mrestrict (w_H W2) m4) (e_R (x_e cx) + 0xd0) 8 (e_F (x_e cx) + 0xa0)).
{ intros m3 m4 Hm3 Hm4. eapply val_mem_kept; [|exact VE0]. intros q Hq.
  apply (hdb_mem2 _ mem2 m3 m4 _ _ (hdb_wT (e_F (x_e cx))) Hm3 Hm4);
    [intros a [X|X]; [exact X | destruct X] | lia | cbv [hdb_wT]; lia]. }
destruct r as [|cb [|pb r3]].
- (* r = []: c = p = 0, the cursor does not move *)
  eapply SRr_bind.
  { exact (hdb_T0 B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs2 _ _ _ _ Hctx R9 R19 R22 R18 ltac:(cbn [length Z.of_nat] in Hc2; lia) VE0). }
  intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & Hio3 & Hk3 & Hm3 & Hp3 &
    ((R5' & R28' & R6' & R24' & R13' & R18') & (Z1 & Z2 & V118))).
  change (mkCfg (mkst regs3 (Z_to_bv 64 R7B_DIG) mem3 (seg_rom rsegs)) md3)
    with (cfg_at rsegs (if false then R7B_ODD else R7B_DIG) regs3 mem3 md3).
  apply (hdb_to_arm false cx POST rest i k sh np ps cnt es [kb] [] [] 0 0 ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3
    Hst HDIG HODD Hlps Hles Hb Hat0 Hfsh Hppat He HJ3 Hio3).
  + apply (hdb_keep1 regs2 regs3 hdb_clobT0 Hk3). hdb_sub.
  + exact Hm3.
  + exact Z1.
  + exact Z2.
  + exact R5'.
  + hdb_kr Hk3 R7.
  + exact R28'.
  + exact R13'.
  + exact R6'.
  + exact R18'.
  + exact R24'.
  + exact V118.
  + cbn [length Z.of_nat] in Hc2. lia.
  + exact Hsufr.
  + exact Hkd'.
  + reflexivity.
  + cbv iota. lia.
  + lia.
- (* r = [c]: c read, p = 0 *)
  change (Z.of_nat (length [cb])) with 1 in Hc2, R6, R22, Hra, Hdis, Hin_keep.
  destruct (Hg 0%nat ltac:(cbn; lia)) as [Vc _]. cbn [nth rs_u8s map Z.of_nat] in Vc. rewrite Z.add_0_r in Vc.
  pose proof (Cursor.byte_range cb) as Bc.
  set (cur := rs_cur rsegs cx rest [cb]) in *.
  eapply SRr_bind.
  { exact (hdb_T1 B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs2 _ _ _ 1 Hctx R19 R22 ltac:(lia)). }
  intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & Hio3 & Hk3 & Hm3 & Hp3 & Z3).
  change (mkCfg (mkst regs3 (Z_to_bv 64 HDB_K) mem3 (seg_rom rsegs)) md3) with (cfg_at rsegs HDB_K regs3 mem3 md3).
  assert (Hctx3 : hdb_ctx B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx)
    (x_own cx) (x_k cx) ly2 S2 W2 mem3 md3 (e_R (x_e cx)) (e_F (x_e cx)) (x_pos cx))
    by (destruct Hctx as (_ & Hc); exact (conj HJ3 Hc)).
  eapply SRr_bind.
  { refine (hdb_K1 B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs3 _ _ _ cur (bv_unsigned cb) Hctx3
      _ _ _ _ _ Hc1 ltac:(lia) _ Bc _).
    - hdb_kr Hk3 R27.
    - hdb_kr Hk3 R16.
    - hdb_kr Hk3 R18.
    - hdb_kr Hk3 R6.
    - hdb_kr Hk3 R20.
    - eapply val_mem_kept; [|exact Vc]. intros q Hq. cbn in Hq.
      exact (proj1 (Hin_keep mem3 Hm3 (cur + q) ltac:(lia))).
    - apply (rm_ra_kept rsegs _ _ _ _ _ _ _ Hra). intros x Hx. exact (proj2 (Hin_keep mem3 Hm3 x Hx)). }
  intros W4 c4 _ (-> & regs4 & mem4 & md4 & -> & HJ4 & Hio4 & Hk4 & Hm4 & Hp4 & (K13 & K10)).
  change (mkCfg (mkst regs4 (Z_to_bv 64 HDB_C1) mem4 (seg_rom rsegs)) md4) with (cfg_at rsegs HDB_C1 regs4 mem4 md4).
  assert (Hctx4 : hdb_ctx B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx)
    (x_own cx) (x_k cx) ly2 S2 W2 mem4 md4 (e_R (x_e cx)) (e_F (x_e cx)) (x_pos cx))
    by (destruct Hctx as (_ & Hc); exact (conj HJ4 Hc)).
  set (odd := 200 <=? bv_unsigned cb).
  assert (Hodd : if odd then 200 <= bv_unsigned cb < 256 else 0 <= bv_unsigned cb < 200)
    by (unfold odd; destruct (Z.leb_spec 200 (bv_unsigned cb)); lia).
  eapply SRr_bind.
  { refine (hdb_C1 B odd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs4 _ _ _ (bv_unsigned cb) (cur + 1) Hctx4
      _ _ K10 K13 Hodd ltac:(lia) (VE_keep mem3 mem4 Hm3 Hm4)).
    - rewrite Hk4; [|cbv; discriminate | hdb_notin]. hdb_kr Hk3 R9.
    - rewrite Hk4; [|cbv; discriminate | hdb_notin]. hdb_kr Hk3 R19. }
  intros W5 c5 _ (-> & regs5 & mem5 & md5 & -> & HJ5 & Hio5 & Hk5 & Hm5 & Hp5 &
    ((C18 & C5) & C28 & C6 & C24 & Z5 & V5)).
  change (mkCfg (mkst regs5 (Z_to_bv 64 (if odd then R7B_ODD else R7B_DIG)) mem5 (seg_rom rsegs)) md5)
    with (cfg_at rsegs (if odd then R7B_ODD else R7B_DIG) regs5 mem5 md5).
  assert (Ecur : rs_cur rsegs cx rest [] = cur + 1) by (unfold cur, rs_cur; cbn [length Z.of_nat]; lia).
  apply (hdb_to_arm odd cx POST rest i k sh np ps cnt es (kb :: [cb]) [cb] [] (bv_unsigned cb) 0
    ly2 S2 W2 regs2 mem2 md2 regs5 mem5 md5 Hst HDIG HODD Hlps Hles Hb Hat0 Hfsh Hppat He HJ5
    (same_io_trans _ _ _ Hio3 (same_io_trans _ _ _ Hio4 Hio5))).
  + apply (hdb_keep3 regs2 regs3 regs4 regs5 [] hdb_clobK hdb_clobC1 Hk3 Hk4 Hk5). hdb_sub.
  + apply (hdb_mem3 _ mem2 mem3 mem4 mem5 _ _ _ _ Hm3 Hm4 Hm5).
    intros a [X|[X|X]]; [left; exact X | destruct X | right; exact X].
  + apply (hdb_zero_kept W2 mem3 mem5 _ 4 12 Z3). intros q Hq.
    apply (hdb_mem2 _ mem3 mem4 mem5 _ _ (hdb_wChC (e_F (x_e cx)) (e_R (x_e cx))) Hm4 Hm5);
      [intros a [X|X]; [destruct X | exact X] | lia | cbv [hdb_wChC hdb_wCh hdb_wCell]; lia].
  + exact Z5.
  + exact C5.
  + rewrite Hk5; [|cbv; discriminate | hdb_notin]. rewrite Hk4; [|cbv; discriminate | hdb_notin]. hdb_kr Hk3 R7.
  + exact C28.
  + rewrite Hk5; [exact K13 | cbv; discriminate | hdb_notin].
  + exact C6.
  + exact C18.
  + exact C24.
  + rewrite Ecur. exact V5.
  + rewrite Ecur. lia.
  + exact (hdb_suffix_tl rest [] cb Hsufr).
  + exact Hkd'.
  + reflexivity.
  + exact Hodd.
  + lia.
- (* r = c :: p :: r3: both read *)
  set (n := Z.of_nat (length (cb :: pb :: r3))) in *.
  assert (Hn2 : 2 <= n) by (subst n; cbn [length]; lia).
  destruct (Hg 0%nat ltac:(cbn; lia)) as [Vc _]. cbn [nth rs_u8s map Z.of_nat] in Vc. rewrite Z.add_0_r in Vc.
  destruct (Hg 1%nat ltac:(cbn; lia)) as [Vp _]. cbn [nth rs_u8s map Z.of_nat] in Vp.
  pose proof (Cursor.byte_range cb) as Bc. pose proof (Cursor.byte_range pb) as Bp.
  set (cur := rs_cur rsegs cx rest (cb :: pb :: r3)) in *.
  eapply SRr_bind.
  { exact (hdb_T1 B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs2 _ _ _ n Hctx R19 R22 ltac:(lia)). }
  intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & Hio3 & Hk3 & Hm3 & Hp3 & Z3).
  change (mkCfg (mkst regs3 (Z_to_bv 64 HDB_K) mem3 (seg_rom rsegs)) md3) with (cfg_at rsegs HDB_K regs3 mem3 md3).
  assert (Hctx3 : hdb_ctx B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx)
    (x_own cx) (x_k cx) ly2 S2 W2 mem3 md3 (e_R (x_e cx)) (e_F (x_e cx)) (x_pos cx))
    by (destruct Hctx as (_ & Hc); exact (conj HJ3 Hc)).
  eapply SRr_bind.
  { refine (hdb_K2 B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs3 _ _ _ cur n (bv_unsigned cb) (bv_unsigned pb) Hctx3
      _ _ _ _ _ Hn2 ltac:(lia) Hc1 ltac:(lia) _ Bc _ Bp _).
    - hdb_kr Hk3 R27.
    - hdb_kr Hk3 R16.
    - hdb_kr Hk3 R18.
    - hdb_kr Hk3 R6.
    - hdb_kr Hk3 R20.
    - eapply val_mem_kept; [|exact Vc]. intros q Hq. cbn in Hq.
      exact (proj1 (Hin_keep mem3 Hm3 (cur + q) ltac:(lia))).
    - eapply val_mem_kept; [|exact Vp]. intros q Hq. cbn in Hq.
      exact (proj1 (Hin_keep mem3 Hm3 (cur + 1 + q) ltac:(lia))).
    - apply (rm_ra_kept rsegs _ _ _ _ _ _ _ (range_addressable_sub _ _ _ _ cur 2 Hra ltac:(lia) ltac:(lia))).
      intros x Hx. exact (proj2 (Hin_keep mem3 Hm3 x ltac:(lia))). }
  intros W4 c4 _ (-> & regs4 & mem4 & md4 & -> & HJ4 & Hio4 & Hk4 & Hm4 & Hp4 & (K13 & K24 & K11 & K6 & K28)).
  change (mkCfg (mkst regs4 (Z_to_bv 64 HDB_C2) mem4 (seg_rom rsegs)) md4) with (cfg_at rsegs HDB_C2 regs4 mem4 md4).
  assert (Hctx4 : hdb_ctx B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx)
    (x_own cx) (x_k cx) ly2 S2 W2 mem4 md4 (e_R (x_e cx)) (e_F (x_e cx)) (x_pos cx))
    by (destruct Hctx as (_ & Hc); exact (conj HJ4 Hc)).
  set (odd := 200 <=? bv_unsigned cb).
  assert (Hodd : if odd then 200 <= bv_unsigned cb < 256 else 0 <= bv_unsigned cb < 200)
    by (unfold odd; destruct (Z.leb_spec 200 (bv_unsigned cb)); lia).
  eapply SRr_bind.
  { refine (hdb_C2 B odd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs4 _ _ _ (bv_unsigned cb) (cur + 2) Hctx4
      _ _ K11 K13 Hodd ltac:(lia) (VE_keep mem3 mem4 Hm3 Hm4)).
    - rewrite Hk4; [|cbv; discriminate | hdb_notin]. hdb_kr Hk3 R9.
    - rewrite Hk4; [|cbv; discriminate | hdb_notin]. hdb_kr Hk3 R19. }
  intros W5 c5 _ (-> & regs5 & mem5 & md5 & -> & HJ5 & Hio5 & Hk5 & Hm5 & Hp5 &
    ((C18 & C5) & Z5 & V5)).
  change (mkCfg (mkst regs5 (Z_to_bv 64 (if odd then R7B_ODD else R7B_DIG)) mem5 (seg_rom rsegs)) md5)
    with (cfg_at rsegs (if odd then R7B_ODD else R7B_DIG) regs5 mem5 md5).
  assert (Ecur : rs_cur rsegs cx rest r3 = cur + 2) by (unfold cur, rs_cur; cbn [length]; lia).
  apply (hdb_to_arm odd cx POST rest i k sh np ps cnt es (kb :: cb :: pb :: r3) (cb :: pb :: r3) r3
    (bv_unsigned cb) (bv_unsigned pb) ly2 S2 W2 regs2 mem2 md2 regs5 mem5 md5 Hst HDIG HODD Hlps Hles Hb Hat0
    Hfsh Hppat He HJ5 (same_io_trans _ _ _ Hio3 (same_io_trans _ _ _ Hio4 Hio5))).
  + apply (hdb_keep3 regs2 regs3 regs4 regs5 [] hdb_clobK hdb_clobC2 Hk3 Hk4 Hk5). hdb_sub.
  + apply (hdb_mem3 _ mem2 mem3 mem4 mem5 _ _ _ _ Hm3 Hm4 Hm5).
    intros a [X|[X|X]]; [left; exact X | destruct X | right; exact X].
  + apply (hdb_zero_kept W2 mem3 mem5 _ 4 12 Z3). intros q Hq.
    apply (hdb_mem2 _ mem3 mem4 mem5 _ _ (hdb_wChC (e_F (x_e cx)) (e_R (x_e cx))) Hm4 Hm5);
      [intros a [X|X]; [destruct X | exact X] | lia | cbv [hdb_wChC hdb_wCh hdb_wCell]; lia].
  + exact Z5.
  + exact C5.
  + rewrite Hk5; [|cbv; discriminate | hdb_notin]. rewrite Hk4; [|cbv; discriminate | hdb_notin]. hdb_kr Hk3 R7.
  + rewrite Hk5; [exact K28 | cbv; discriminate | hdb_notin].
  + rewrite Hk5; [exact K13 | cbv; discriminate | hdb_notin].
  + rewrite Hk5; [|cbv; discriminate | hdb_notin]. rewrite K6. unfold w64. f_equal. subst n. cbn [length]. lia.
  + exact C18.
  + rewrite Hk5; [exact K24 | cbv; discriminate | hdb_notin].
  + rewrite Ecur. exact V5.
  + rewrite Ecur. lia.
  + exact (hdb_suffix_tl rest r3 pb (hdb_suffix_tl rest (pb :: r3) cb Hsufr)).
  + exact Hkd'.
  + reflexivity.
  + exact Hodd.
  + exact Bp.
Qed.

End g.

(* ======================================== the head ======================================== *)
Lemma r7b_head : forall B MT, r7b_head_stmt rsegs B MT.
Proof.
intros B MT. unfold r7b_head_stmt. intros cx POST rest i k kd Hst Hkd HDIG HODD.
split; [exact (hdb_piece_D B MT cx POST rest i k kd Hst Hkd HDIG HODD)
       | exact (hdb_piece_D0E B MT cx POST rest i k Hst HDIG HODD)].
Qed.

End g0.

Print Assumptions r7b_head.

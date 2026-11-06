(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: adapted from cgif's lib/A/ACgq.v and lib/A/ACk8.v (file header, walk tactic forms) for reac_ctrl_parse of libreac's fuzz_grant. *)
(* Modified by Theorem Labs, 2026-10: the short walk (n < 50) of fuzz_disco.asan-ubsan (lib_both3_0_listing, entry 0x874a4), which fuzz_grant has no file for: its run steps are fuzz_grant image B's (a working branch edc3e948664; the same code, Y pc = image B pc + 0x4d30) in three pieces - lib/B/Prog/CtrlParse.v pb_ctrl_parse steps 1-4b (entry to cut A), lib/B/Prog/CtrlParseMid.v (cut A to the memset's return) and the len < 50 branch of lib/B/Prog/CtrlParseNone.v (to cut J) - stated on fuzz_disco's statement layer (lib/Y/Prog/CtrlParseLib.v pz_entry0, lib/Y/Prog/CtrlParseCut.v; disco A's walk a working branch a6498221fa6 lib/A/Prog/CtrlParseWalk.v pz_segA, a working branch f0661c67ffd lib/A/Prog/CtrlParseMid.v and a working branch eafd64be243 lib/A/Prog/CtrlParseNone.v), with no region, atom fact or shadow entry for the frame f, which fuzz_disco's contract describes only under 50 <= n. *)
(* reac_ctrl_parse (0x874a4 of fuzz_disco's asan-ubsan image, AF_both3_reac_ctrl_parse 0x64e8 of the listing),
   the whole short path n < 50 from the entry to cut J (0x878c4), the join before the epilogue:
   - the prologue, sp realigned to 32 bytes, the side-stack frame of class 1 (frame_alloc_1 =
     __asan_stack_malloc_1, called at 0x87514; the `beqz a2` at 0x8750c on the side-stack flag cell, which
     holds 1, decided) - cut A0 (0x87518), cut A without the frame f;
   - the frame's header and shadow, the `beqz s4` at 0x875cc on o (decided: o >= 4096), the memset of the out
     struct (checked_memset = __asan_memset, called at 0x875e0);
   - 0x875e4 li a0,50; 0x875e8 bltu s6,a0 -> 0x878bc, taken since n < 50; 0x878bc andi a0,s3,3 and its
     bnez to the trap 0x87ca0, decided from atom 12's alignment fact (o is 8-aligned); a0 = 0 at the join.
   No byte of f is read on this path and the contract says nothing about f when n < 50: the walk carries no
   region and no fact for atom 10, and its shadow entries are the out struct's alone (PZ_SH0). *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YG0s YM05 YI16 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC1f YC44 YC8g YC8i.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC1g YC1h YC81 YC4b YC45 YC85 YC88.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import RcKind RcParse.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YRo YCkd YCjr YCj1 YCja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import CtrlParse CtrlParseLib KindOfLink1.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import CtrlParseCut.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
#[local] Ltac Zify.zify_pre_hook ::= try unfold YImgTop.IMG_TOP, YImgTop.IMG_LO in *.
(* The windows of a run lie in the stack below the entry sp, the out struct or the own frame. *)
Local Ltac pzs_win :=
let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a := fresh "a" in
let Hin := fresh "Hin" in let Ha := fresh "Ha" in let Hq := fresh "Hq" in
intros b wlo whi a Hin Ha;
lazymatch type of Hin with In _ ?l => let l' := eval vm_compute in l in change (In (b, wlo, whi) l') in Hin end; cbn [In] in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Ha; revert Ha; pz_bases; intro Ha; cbv beta;
unfold pz_nf, SHADOW_OFF, SB in *; lia |]); destruct Hin.
(* The presence of a window byte at the memory of the journal HJx: the own frame, its shadow, or the
   journal's stack window. *)
Local Ltac pzs_pres HJx :=
first [ lia
| lazymatch goal with HFp : forall m md', AR _ _ _ _ _ m md' -> forall a, _ <= a < _ + 128 -> _ |- _ => apply (HFp _ _ (proj1 HJx)); lia end
| lazymatch goal with HFSp : forall m md', AR _ _ _ _ _ m md' -> forall a, _ <= a < _ + 16 -> _ |- _ => apply (HFSp _ _ (proj1 HJx)); lia end
| let HP := fresh "HP" in pose proof HJx as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HP & _); apply HP; lia ].
(* pzs_pres without its leading lia, for a goal that is a presence fact (never arithmetic): that lia can only succeed
   by a contradiction in the context, and on a post-call context it fails after a full search. *)
Local Ltac pzs_pres_nl HJx :=
first [ lazymatch goal with HFp : forall m md', AR _ _ _ _ _ m md' -> forall a, _ <= a < _ + 128 -> _ |- _ => apply (HFp _ _ (proj1 HJx)); lia end
| lazymatch goal with HFSp : forall m md', AR _ _ _ _ _ m md' -> forall a, _ <= a < _ + 16 -> _ |- _ => apply (HFSp _ _ (proj1 HJx)); lia end
| let HP := fresh "HP" in pose proof HJx as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HP & _); apply HP; lia ].
(* lia over the walk's context: the disjunctive facts are boxed (lia would split on every one of them); a goal
   that needs one of them gets it destructed, one at a time. *)
Local Ltac pzs_lia :=
first [ lia
| match goal with H : boxed (_ \/ _) |- _ => let X := fresh in pose proof H as X; unfold boxed in X; destruct X; lia end
| match goal with H : boxed (_ /\ (_ \/ _)) |- _ => let X := fresh in pose proof H as X; unfold boxed in X; destruct X as [? [?|?]]; lia end
| match goal with H : boxed (off_img _ _) |- _ => let X := fresh in pose proof H as X; unfold boxed, off_img in X; destruct X; lia end
| match goal with H : boxed (in_app _ _) |- _ => let X := fresh in pose proof H as X; unfold boxed, in_app in X; destruct X as [? [?|?]]; lia end
| unbox; lia ].
(* lia's cost here is the post-call context: raw disjunctions and mod facts it splits / divides on.
   rs_hold hides a hypothesis from lia; a goal then gets exactly the disjunctions it needs. *)
Local Definition rs_hold (A : Prop) : Prop := A.
Local Lemma rs_hide : forall A : Prop, A -> rs_hold A. Proof. intros A H. exact H. Qed.
(* Cut A0, at AF_CUTA (after __asan_stack_malloc_1 returns, the frame (1, fpos) seated) on the short path: cut A
   (lib/Y/Prog/CtrlParseCut.v ss_cutA) without the frame f's region and atom 10's fact. *)
Definition ss_cutA0 : sstate := Eval vm_compute in
mkSS (ss_pc ss_cutA) (ss_regs ss_cutA)
  (List.filter (fun r => match YP09.r_base r with Some 10%nat => false | _ => true end) (ss_mem ss_cutA))
  None
  (mkFacts (List.filter (fun x => negb (Nat.eqb (fst x) 10)) (f_atoms (ss_facts ss_cutA)))
     (f_conds (ss_facts ss_cutA)) (f_alias (ss_facts ss_cutA))).
Section b. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Context {PI : PAImg lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
(* A range none of whose bytes is the own frame lies below or above it. *)
Lemma pzs_sep : forall F FL p n, 0 < n -> (forall a, p <= a < p + n -> ~ pz_nf F FL a) -> p + n <= F \/ F + 128 <= p.
Proof.
intros F FL p n Hn H. destruct (Z_le_gt_dec (p + n) F) as [H1|H1]; [left; exact H1|].
destruct (Z_le_gt_dec (F + 128) p) as [H2|H2]; [right; exact H2|].
exfalso. apply (H (Z.max p F)); [lia|]. left. lia.
Qed.
(* The shadow hull of a range is the union of the hulls of its bytes. *)
Lemma pzs_hull_bytes : forall (rd : reader) p n, 0 <= p -> 0 < n ->
(forall x, p <= x < p + n -> shadow_hull_vis rd x 1) -> shadow_hull_vis rd p n.
Proof.
intros rd p n Hp Hn H s Hs. unfold shadow_addr, SHADOW_OFF in Hs.
set (x := Z.max p (64 * (s / 8) - 8 * 2147450880)).
assert (Hx : p <= x < p + n) by (unfold x; lia).
apply (H x Hx s). unfold x, shadow_addr, SHADOW_OFF. lia.
Qed.
Section m.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
(* The shadow byte of a byte of a caller frame is no byte of the out struct (an application range). *)
Lemma pzs_frame_sh : forall lyc Sc W memc mdc cid pos o x,
AR SEGS B lyc Sc W memc mdc -> In (cid, pos) (frames Sc) ->
frame_addr lyc cid pos <= x < frame_addr lyc cid pos + fs_frame_bytes cid ->
(o + 36 <= kLowShadowBeg \/ kHighMemBeg <= o) -> ~ (o <= shadow_addr x < o + 36).
Proof.
intros lyc Sc W memc mdc cid pos o x HAR Hin Hx Hoap.
destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (G4 & Gce & _).
pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as HCE. unfold ASAN_CEIL in HCE.
unfold shadow_addr, SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *. lia.
Qed.
(* Where each byte of the out struct lies: a caller block or a caller frame (the machine stack is above
   the allocation ceiling, and the shadow of a caller frame holds no application byte). *)
Lemma pzs_out_loc : forall STK sp0 FP ly S lyc Sc own W memc mdc o x,
AR SEGS B lyc Sc W memc mdc ->
(forall cid pos, In (cid, pos) own -> In (cid, pos) (frames Sc)) ->
alloc_ceiling <= sp0 - STK -> o + 36 <= alloc_ceiling ->
(o + 36 <= kLowShadowBeg \/ kHighMemBeg <= o) -> o <= x < o + 36 ->
awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own x ->
(exists b m, In (b, m) (ablocks B lyc Sc) /\ b <= x < b + req_size m) \/
(exists cid pos, In (cid, pos) (frames Sc) /\ frame_addr lyc cid pos <= x < frame_addr lyc cid pos + fs_frame_bytes cid).
Proof.
intros STK sp0 FP ly S lyc Sc own W memc mdc o x HAR Hown Hstk Hoce Hoap Hx Hw.
destruct Hw as [Hs|[(_ & b & m & Hb & Hr)|[(b & m & Hb & _ & Hr)|(cid & pos & Hin & [Hr|Hr])]]].
- lia.
- left. exists b, m. split; [exact Hb | lia].
- left. exists b, m. split; [exact Hb | lia].
- right. exists cid, pos. split; [exact (Hown cid pos Hin)|]. unfold in_zr in Hr. cbn [fst snd] in Hr. lia.
- exfalso. destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc cid pos HAR (Hown cid pos Hin)) as (G4 & Gce & _).
pose proof (fs_frame_bytes_nonneg cid) as Hfs.
pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as HCE. unfold ASAN_CEIL in HCE.
unfold in_zr in Hr. cbn [fst snd] in Hr.
unfold shadow_addr, SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *. lia.
Qed.
(* The out struct stays addressable and its shadow hull readable: a byte in a caller block has them from
   the state, a byte in a caller frame keeps its shadow byte (pz_kept) and has its hull from the state. *)
Lemma pzs_out_shadow : forall STK sp0 FP ly S lyc Sc own W memc mdc S2 mem2 md2 slo shi o,
AR SEGS B lyc Sc W memc mdc -> AR SEGS B lyc S2 W mem2 md2 ->
(forall cid pos, In (cid, pos) own -> In (cid, pos) (frames Sc)) ->
(forall c p, In (c, p) (frames Sc) -> In (c, p) (frames S2)) -> ablocks B lyc S2 = ablocks B lyc Sc ->
alloc_ceiling <= sp0 - STK -> o + 36 <= alloc_ceiling -> 4096 <= o ->
(o + 36 <= kLowShadowBeg \/ kHighMemBeg <= o) ->
pz_kept B lyc Sc W memc mem2 slo shi o ->
(forall a, o <= a < o + 36 -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a) ->
range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF o 36 ->
range_addressable (aview SEGS (w_H W) mem2) SHADOW_OFF o 36 /\ shadow_hull_vis (aview SEGS (w_H W) mem2) o 36.
Proof.
intros STK sp0 FP ly S lyc Sc own W memc mdc S2 mem2 md2 slo shi o HAR HAR2 Hown HfinS2 Eab Hstk Hoce Ho4 Hoap KP HOW HRo.
assert (L : forall x, o <= x < o + 36 ->
(exists b m, In (b, m) (ablocks B lyc Sc) /\ b <= x < b + req_size m) \/
(exists cid pos, In (cid, pos) (frames Sc) /\ frame_addr lyc cid pos <= x < frame_addr lyc cid pos + fs_frame_bytes cid))
by (intros x Hx; exact (pzs_out_loc STK sp0 FP ly S lyc Sc own W memc mdc o x HAR Hown Hstk Hoce Hoap Hx (HOW x Hx))).
split.
- intros x Hx. destruct (L x Hx) as [(b & m & Hb & Hr)|(cid & pos & Hin & Hr)].
+ rewrite <- Eab in Hb. exact (range_addressable_of_block SEGS B LAWS lyc S2 W mem2 md2 b m x 1 HAR2 Hb ltac:(lia) ltac:(lia) x ltac:(lia)).
+ refine (pz_kept_ra B LAWS lyc Sc W memc mdc mem2 slo shi o cid pos x 1 HAR KP Hin ltac:(lia) ltac:(lia) _ _ x ltac:(lia)).
* intros y Hy. exact (pzs_frame_sh lyc Sc W memc mdc cid pos o y HAR Hin ltac:(lia) Hoap).
* intros y Hy. apply HRo. lia.
- apply pzs_hull_bytes; [lia | lia |]. intros x Hx. destruct (L x Hx) as [(b & m & Hb & Hr)|(cid & pos & Hin & Hr)].
+ rewrite <- Eab in Hb. exact (shadow_hull_vis_of_block SEGS B LAWS lyc S2 W mem2 md2 b m x 1 HAR2 Hb ltac:(lia) ltac:(lia) ltac:(lia)).
+ exact (shadow_hull_vis_of_frame SEGS B LAWS lyc S2 W mem2 md2 cid pos x 1 HAR2 (HfinS2 _ _ Hin) ltac:(lia) ltac:(lia) ltac:(lia)).
Qed.
End m.
(* The shadow entry of the out struct (PZ_SH0), from its shadow bytes at the current memory: the short walk's
   shadow entries, which name no byte of the frame f. *)
Lemma pzs_shok : forall E H mem o,
ew E 12 = Z_to_bv 64 o -> ew E 32 = Z_to_bv 64 SB ->
0 < o -> o + 36 <= 2 ^ 47 -> (o + 36 <= kLowShadowBeg \/ kHighMemBeg <= o) ->
range_addressable (aview SEGS H mem) SHADOW_OFF o 36 ->
sh_ok SEGS PZx PZ_SH0 E (mrestrict H mem).
Proof.
intros E H mem o E12 E32 Ho0 Ho47 Hosh HRo.
unfold sh_ok, PZ_SH0. constructor; [|constructor].
apply (shent_ok_of_range SEGS H mem E PZx 12 o 36 o 0 36 HRo).
- unfold U, PZx. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
- unfold U. cbn [sv_denot]. rewrite E12, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
- lia. - lia.
- intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *. lia.
Qed.
(* The rest of the short walk from cut A0: n < 50, the frame (1, fpos) seated. *)
Definition pzs_cutA0_spec (B : asyms) (c : pz_ctx) : Prop :=
cx_n c < 50 ->
forall E ms md, pz_cur B c E ms md ->
st_ok_pi (fx := cx_fq c) SEGS VAL E ss_cutA0 (restrict (w_H (cx_W c)) ms) ->
SRr SEGS (cx_W c) (mkCfg ms md) (pz_post B c).
(* The caller's memory after a run: the run wrote only its windows (the stack below sp, the out struct, the
   own frame), so what the call keeps of the caller's memory (pz_kept) carries over it. *)
Local Ltac pzs_kp :=
lazymatch goal with
| HFr : frame_of ?Ef ?rsf (mrestrict _ ?mA) (mrestrict _ ?mB), HG : mem_grows _ _,
  KP : pz_kept ?B ?lyc ?Sc ?W ?memc _ ?slo ?sp ?o,
  HAR : AR _ ?B ?lyc ?Sc ?W ?memc ?mdc,
  Hfrs2 : frames ?S2 = (1, ?fpos) :: frames ?Sc,
  HARc : AR _ ?B ?lyc ?S2 ?W _ _,
  Eab : ablocks ?B ?lyc ?S2 = ablocks ?B ?lyc ?Sc,
  EF : ?F = frame_addr ?lyc 1 ?fpos, EFL : ?FL = flag_addr ?lyc 1 ?fpos,
  FFL : frame_flag_lawP _ ?B, LAWS : AR_laws _ ?B, Hoimg : off_img ?o 36,
  B33 : bv_unsigned (ew _ 33) = ?sp1 |- _ =>
  let Hw := fresh "Hw" in let KP' := fresh "KP" in
  assert (Hw : forall b wlo whi a, In (b, wlo, whi) (windows rsf) -> base_val Ef b + wlo <= a < base_val Ef b + whi ->
  (fun a => (sp1 <= a < sp) \/ (o <= a < o + 36) \/ pz_nf F FL a) a) by pzs_win;
  pose proof (pz_kept_own B LAWS lyc Sc S2 W memc mdc _ _ mA mB slo sp o fpos F FL
  (fun a => (sp1 <= a < sp) \/ (o <= a < o + 36) \/ pz_nf F FL a) HAR HARc Hfrs2 Eab EF EFL FFL
  ltac:(lia) ltac:(lia) Hoimg
  ltac:(intros a [Ha|[Ha|Ha]]; [left; lia | right; left; exact Ha | right; right; exact Ha])
  KP (kept_of_frame _ _ _ _ _ _ HFr Hw) (fun a Ha => apresent_grows _ _ _ a HG Ha)) as KP';
  clear KP Hw HFr HG; rename KP' into KP;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H end
| _ => fail 1 "pzs_kp: the run's frame_of / mem_grows and the cut's pz_kept, AR, frames, ablocks, F, FL and B33 must all be in context"
end.
(* One shadow-checked run to the next branch or to cut J, and the caller's memory after it. *)
Local Ltac pzs_run :=
lazymatch goal with
| RUNTO : context [sym_run_toN_pi_tok _ _ _ _ _ _ _ _ _], HS : st_ok_pi _ _ _ _ _,
  HJ2 : ajournal _ _ _ _ _ _ _ _ _ _ ((1, ?fpos) :: _) _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _,
  AG : forall n0, (n0 < 33)%nat -> _, EF : ?F = frame_addr _ 1 ?fpos |- _ =>
  paj_run_to_tok RUNTO HS HJ2 SHOK PZspan AF_JOIN; [ awrFL_with ltac:(idtac; pz_awr_hd) AG fpos F I | pzs_kp ]
| _ => fail 1 "pzs_run: RUNTO, HS, the journal of the own frame, SHOK, AG and EF must all be in context"
end.
(* The 36 bytes of the out struct are zero: region 12 still holds the memset's zero chunk. *)
Local Ltac pzs_zero HZ :=
lazymatch goal with
| HS : st_ok_pi _ _ ?Ex ?ssx (restrict (w_H ?W) ?msv),
  KP : pz_kept _ _ _ _ _ _ _ _ ?o |- _ =>
  let rs := eval vm_compute in (ss_mem ssx) in
  let ix := idx_of_base rs 12%nat in let ix := eval vm_compute in ix in
  let r := eval vm_compute in (nth ix rs got_regionP) in
  let R12 := fresh "R12" in
  pose proof (st_ok_pi_region_nth Ex ssx (restrict (w_H W) msv) ix r HS ltac:(vm_compute; reflexivity)) as R12;
  cbn [ms_mem restrict] in R12;
  assert (HZ : forall j, (j < 36)%nat -> aview SEGS (w_H W) (ms_mem msv) (o + Z.of_nat j) = Some (bv_unsigned cp_z));
  [ let j := fresh "j" in let Hj := fresh "Hj" in let Hb := fresh "Hb" in let Hv := fresh "Hv" in
    intros j Hj;
    assert (Hb : pz_chunk_at Ex (base_val Ex (Some 12%nat)) [YP09.mkChunk 0 (CZero 36)] (Z.of_nat j) = Some (Z_to_bv 8 0))
    by (cbn [pz_chunk_at YP09.c_off YP09.c_len YP09.cv_len YP09.c_val];
        replace ((0 <=? Z.of_nat j) && (Z.of_nat j <? 0 + 36)) with true
        by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia);
        reflexivity);
    pose proof (pz_region_byte Ex (w_H W) (ms_mem msv) _ (Z.of_nat j) _ R12 Hb) as Hv;
    revert Hv; cbn [YP09.r_base base_val]; pz_bases; intros Hv; exact Hv
  | clear R12 ]
end.
(* The frame (516) and its shadow (529) become writable again (cut J's windows). *)
Local Ltac pzs_rw :=
lazymatch goal with
| HS : st_ok_pi _ _ ?Ex ?ssx ?msx, E529 : ew ?Ex 529 = _, HJ2 : ajournal _ _ _ _ _ _ _ _ _ _ ((1, _) :: _) _ _ _ _ _ _,
  HFSp : forall m md', AR _ _ _ _ _ m md' -> forall a, _ <= a < _ + 16 -> apresent _ m a |- _ =>
  let rs := eval vm_compute in (ss_mem ssx) in
  let ix := idx_of_base rs 529%nat in let ix := eval vm_compute in ix in
  let r := eval vm_compute in (nth ix rs got_regionP) in
  let HS' := fresh "HS" in
  pose proof (ast_ok_pi_set_region Ex ssx msx ix r (set_window r 0 16) HS ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
  (region_ok_rewindow _ Ex _ r 0 16 (st_ok_pi_region_nth Ex ssx msx ix r HS ltac:(vm_compute; reflexivity))
  ltac:(cbn [YP09.r_base base_val ms_mem restrict mkst]; rewrite E529, unsigned_lit_small by (unfold SB; lia);
  let o0 := fresh "o0" in let Ho0 := fresh "Ho0" in
  intros o0 Ho0; apply (apresent_writable _); apply (HFSp _ _ (proj1 HJ2)); lia))) as HS';
  clear HS; rename HS' into HS; pz_norm HS
end;
lazymatch goal with
| HS : st_ok_pi _ _ ?Ex ?ssx ?msx, RF : ew ?Ex 516 = _, HJ2 : ajournal _ _ _ _ _ _ _ _ _ _ ((1, _) :: _) _ _ _ _ _ _,
  HFp : forall m md', AR _ _ _ _ _ m md' -> forall a, _ <= a < _ + 128 -> apresent _ m a |- _ =>
  let rs := eval vm_compute in (ss_mem ssx) in
  let ix := idx_of_base rs 516%nat in let ix := eval vm_compute in ix in
  let r := eval vm_compute in (nth ix rs got_regionP) in
  let HS' := fresh "HS" in
  pose proof (ast_ok_pi_set_region Ex ssx msx ix r (set_window r 0 128) HS ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
  (region_ok_rewindow _ Ex _ r 0 128 (st_ok_pi_region_nth Ex ssx msx ix r HS ltac:(vm_compute; reflexivity))
  ltac:(cbn [YP09.r_base base_val ms_mem restrict mkst]; rewrite RF, unsigned_lit_small by lia;
  let o0 := fresh "o0" in let Ho0 := fresh "Ho0" in
  intros o0 Ho0; apply (apresent_writable _); apply (HFp _ _ (proj1 HJ2)); lia))) as HS';
  clear HS; rename HS' into HS; pz_norm HS
end.
(* At cut J (0x878c4) with a0 = 0: the state is joined to ss_cutJ and the cut J hypothesis applies; n < 50
   makes the model's header check fail, so its return code is 0 and its 36 bytes are zero. *)
Local Ltac pzs_join :=
let HZ := fresh "HZ" in let R0 := fresh "R0" in let E700 := fresh "E700" in
pzs_zero HZ; pzs_rw;
lazymatch goal with HS : st_ok_pi _ _ _ _ _ |- _ =>
  prreg HS (10%bv : bv 5) R0;
  ra_join HS ss_cutJ 700%nat pz_deadJ ltac:(idtac);
  ra_join_val HS 700%nat 0%nat R0 E700;
  lazymatch goal with AGX : forall n0, (n0 < 512)%nat -> _ |- _ => pz_rebase HS AGX end
end;
lazymatch goal with
| HS : st_ok_pi _ _ ?Ev _ (restrict _ ?msv), Hh : cp_hdr ?n ?fr = false,
  HJc : forall (E : env) (ms : machine_state) (md : Model), _ -> st_ok_pi _ _ E ss_cutJ _ -> _,
  AGX : forall n0, (n0 < 512)%nat -> ew ?Ev n0 = _, RF : ew ?Ev 516 = _, E528 : ew ?Ev 528 = _, E529 : ew ?Ev 529 = _,
  HJ2 : ajournal _ _ _ _ _ _ _ _ _ _ ((1, _) :: _) _ _ _ (ms_mem ?msv) _ _,
  KP : pz_kept _ _ _ _ _ (ms_mem ?msv) _ _ _ |- _ =>
  apply (HJc Ev msv);
  [ split; [assumption|]; split; [exact AGX|]; split; [exact RF|]; split; [exact E528|]; split; [exact E529|];
    split; [exact HJ2 | exact KP]
  | exact HS
  | unfold ctrlparse; rewrite Hh; cbn [fst]; exact E700
  | let j := fresh "j" in let Hj := fresh "Hj" in
    intros j Hj; rewrite (ctrlparse_bytes_none n fr Hh), nth_repeat; exact (HZ j Hj) ]
end.
(* ---- Cut A0 to cut J: the frame's header and shadow, the memset of the out struct, the n < 50 branch. ---- *)
Lemma pzs_segAJ : forall B G, pz_rt B G -> forall c, pz_ok B c -> pz_cutJ_spec B c -> pzs_cutA0_spec B c.
Proof.
intros B G RT c Hok HJc Hlt E ms md Hcur HS.
pz_open c Hok. pz_open_rt RT. pz_open_cur Hcur.
(* The short walk has no premise about the frame f (pz_open_f cannot run) and reads no byte of it. pz_std's
   only use of f is the bound of atom 10: give it the register's own value, a 64-bit word. *)
assert (H10' : getr regs 10 = w64 (bv_unsigned (getr regs 10)))
by (unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity).
assert (Hf'b : 0 <= bv_unsigned (getr regs 10) < 2 ^ 64)
by (pose proof (bv_unsigned_in_range 64 (getr regs 10)) as Hr; change (bv_modulus 64) with (2 ^ 64) in Hr; exact Hr).
clear H10.
pz_std.
lazymatch type of AGX with forall n0, _ -> ew _ n0 = ew ?E0 n0 =>
assert (AG : forall n0, (n0 < 33)%nat -> ew E n0 = ew E0 n0) by (intros; apply AGX; lia) end.
assert (HFp : forall m md', AR SEGS B lyc S2 W m md' -> forall a, F <= a < F + 128 -> apresent (w_H W) m a).
{ intros m md' HA a Ha. destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HA Hfin2) as (_ & _ & Hp & _).
rewrite <- EF in Hp. change (fs_frame_bytes 1) with 128 in Hp. exact (proj1 (Hp a Ha)). }
assert (HFSp : forall m md', AR SEGS B lyc S2 W m md' -> forall a, SB + F / 8 <= a < SB + F / 8 + 16 -> apresent (w_H W) m a).
{ intros m md' HA a Ha. destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HA Hfin2) as (_ & _ & _ & Hp).
rewrite <- EF in Hp. unfold shadow_addr in Hp. change (fs_frame_bytes 1 / 8) with 16 in Hp.
replace a with (SHADOW_OFF + F / 8 + (a - (SB + F / 8))) by (unfold SHADOW_OFF, SB; lia).
assert (Hi : 0 <= a - (SB + F / 8) < 16) by (unfold SB in *; lia).
apply (proj1 (Hp (a - (SB + F / 8)) Hi)). }
(* The out struct is present at every memory of the journal: each of its bytes is one the caller may write. *)
assert (HOp : forall m md', ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 ((1, fpos) :: own) lyc S2 W m md' k ->
forall a, o <= a < o + 36 -> apresent (w_H W) m a).
{ intros m md' HJx a Ha.
assert (Hw : awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc S2) lyc ((1, fpos) :: own) a)
by (rewrite Eab; apply pz_awr_cons; exact (proj1 (HOW a Ha))).
exact (proj1 (awr_byte_present SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJx Hw)). }
(* Where o lies relative to the own frame and the stack window: below the allocation ceiling, where the
   caller may write, so apart from the own frame. *)
pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as HCE. unfold ASAN_CEIL in HCE.
assert (Hstk : alloc_ceiling <= sp0 - STK) by (clear - Hceil Hslo; lia).
assert (Hslo2 : alloc_ceiling <= sp - REAC_CTRL_PARSE_STK) by (clear - Hstk Hwin; lia).
assert (Hshi2 : sp <= 2 ^ 64) by (clear - Hsp0 Hshi H47; lia).
repeat match goal with H : _ \/ _ |- _ => box H | H : off_img _ _ |- _ => box H | H : in_app _ _ |- _ => box H end.
assert (HsepO : o + 36 <= F \/ F + 128 <= o).
{ apply (pzs_sep F FL o 36 ltac:(lia)). intros a Ha.
exact (pz_awr_nf B STK sp0 FP ly S lyc Sc own W memc mdc a F FL HAR Hownf N1 N3 N4 Hstk (proj1 (HOW a Ha))). }
(* 1. The frame's header (0x41b58ab3, its description, the function), its shadow (f1 f1 f1 f1, 00 x 4, 04,
   f3 f3 f3, f3 x 4), the frame address at sp1 + 24, the `beqz s4` on o (0x875cc, decided: o >= 4096), to
   the memset of the out struct (0x875e0). *)
pose proof (SRr_run_pi_AJ_call (fx := fq) B LAWS) as RUNC.
lazymatch type of RUNC with forall W n E ss ss' s ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k Q, _ -> _ -> sym_runN_pi ?tpi n ss = _ -> _ =>
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict (w_H ?Wx) ?msx) =>
let r := eval vm_compute in (sym_runN_pi tpi FUEL ssx) in
lazymatch r with (?ss', PRS_call ?sym) =>
assert (Hrun : sym_runN_pi tpi FUEL ssx = (ss', PRS_call sym)) by (vm_compute; reflexivity);
eapply (RUNC Wx FUEL Ex ssx ss' sym msx _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEI HS Hrun HJ2);
[ clear Hrun | clear Hrun HS HJ2; intros ms1 mat1 HS HJ2 HF HFr HG ] end end end.
{ awrFL_with ltac:(idtac; pz_awr_hd) AG fpos F I. }
lazymatch type of HFr with frame_of ?Ef ?rsf (mrestrict _ ?mA) (mrestrict _ ?mB) =>
assert (Hw : forall b wlo whi a, In (b, wlo, whi) (windows rsf) -> base_val Ef b + wlo <= a < base_val Ef b + whi ->
(fun a => (sp1 <= a < sp) \/ (o <= a < o + 36) \/ pz_nf F FL a) a) by pzs_win;
pose proof (pz_kept_own B LAWS lyc Sc S2 W memc mdc _ _ mA mB (sp - REAC_CTRL_PARSE_STK) sp o fpos F FL
(fun a => (sp1 <= a < sp) \/ (o <= a < o + 36) \/ pz_nf F FL a) HAR HARc Hfrs2 Eab EF EFL FFL Hslo2 Hshi2 Hoimg
ltac:(intros a [Ha|[Ha|Ha]]; [left; lia | right; left; exact Ha | right; right; exact Ha]) KP
(kept_of_frame _ _ _ _ _ _ HFr Hw) (fun a Ha => apresent_grows _ _ _ a HG Ha)) as KP' end.
clear KP Hw HF HFr HG; rename KP' into KP.
destruct (pzs_out_shadow B LAWS STK sp0 FP ly S lyc Sc own W memc mdc S2 _ _ (sp - REAC_CTRL_PARSE_STK) sp o
HAR (proj1 HJ2) Hownf HfinS2 Eab Hstk Howin Ho4096 Hosh KP (fun a Ha => proj1 (HOW a Ha)) HRo) as [HRo1 HHo1].
(* 2. memset(out, 0, 36). *)
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2.
prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
rewrite AGX, E12 in Ra0 by lia. rewrite AGX, E33 in R2 by lia.
rewrite AGX, (EE 3%nat 3%bv eq_refl) in R3 by lia. rewrite AGX, (EE 4%nat 4%bv eq_refl) in R4 by lia.
pmkst HS.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rT _ ?mT _) ?dT) _ =>
eapply (aj_intrin_at SEGS B LAWS Hsegs OSet (SIGMA AS___asan_memset) (AMEMSET fq) W rT mT STK sp0 FP ly S W0 mem0 md0 _ lyc S2 dT k o 0 36 (sp1 - sp0) _ HJ2) end.
- rewrite Ra0. reflexivity.
- rewrite Ra1. reflexivity.
- rewrite Ra2. reflexivity.
- lia. - lia. - lia.
- unfold spZ at 1. rewrite R2, unsigned_lit_small by lia. lia.
- rewrite Zminus_mod, Hsp1al16, Hsp0al. reflexivity.
- lia. - rewrite Hes; lia.
- rewrite R3. exact Hgp. - rewrite R4. exact Htp.
- exact R1. - apply ret_ok_codeptr_v; [lia | reflexivity].
- intros a Ha. split; [rewrite Eab; apply pz_awr_cons; exact (proj1 (HOW a ltac:(lia))) | pzs_lia].
- exact Hoam.
- exact HRo1.
- intros _. exact HHo1.
- exact I. }
cbv beta. clear R1 R2 R3 R4 Ra0 Ra1 Ra2.
intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Ha03 & Heff3 & Hfr3 & Hpres3).
lazymatch type of KP with pz_kept _ _ _ _ _ ?mA _ _ _ =>
pose proof (pz_kept_own B LAWS lyc Sc S2 W memc mdc _ _ mA mem3 (sp - REAC_CTRL_PARSE_STK) sp o fpos F FL
(fun a => (sp1 - ESTACK <= a < sp1) \/ (o <= a < o + 36)) HAR HARc Hfrs2 Eab EF EFL FFL Hslo2 Hshi2 Hoimg
ltac:(intros a [Ha|Ha]; [left; rewrite Hes in Ha; lia | right; left; exact Ha]) KP
ltac:(intros a Ha Hna; apply Hfr3; [exact Ha | intros Hx; apply Hna; right; exact Hx | intros Hx; apply Hna; left; lia])
Hpres3) as KP' end.
clear KP HRo1 HHo1; rename KP' into KP.
(* The memset wrote the out struct: every other region of cut A0 is kept (the frame f has none). *)
jafter_call_keep_hi HS 544%nat regs3 (mrestrict (w_H W) mem3) HP3 [0; 1; 2; 3; 4; 5; 6; 7]%nat HS3.
match type of HS3 with ?Q -> _ => assert (HQ : Q); [| specialize (HS3 HQ); clear HQ] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil;
(eapply pz_region_kept; [pz_bases; reflexivity
| let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; apply Hfr3; unfold ESTACK, off_img, SB, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *;
  (* each region's goal needs at most one of these three: HsepO (out struct vs frame), Hosh (vs shadow), Hoimg (vs image);
     HFapp is the context's only other raw disjunction *)
  apply rs_hide in HFapp; unfold boxed in Hosh, Hoimg; destruct HsepO; destruct Hosh; destruct Hoimg; lia
| let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
  first [ apply rs_hide in HFapp; apply rs_hide in HsepO; pzs_pres_nl HJ3 | pzs_pres_nl HJ3 ] ]). }
rewrite <- restrict_mkst_fx in HS3. clear HS; rename HS3 into HS.
pz_rebase HS AGX.
(* 3. The out struct is zero (memset); the frame and its shadow become read-only for the shadow-checked part. *)
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
assert (ROK : region_ok SEGS Ev (ms_mem msx) (YP09.mkRegion (Some 12%nat) 0 36 0 36 [YP09.mkChunk 0 (CZero 36)]));
[| assert (RDJ : all_disjoint Ev (YP09.mkRegion (Some 12%nat) 0 36 0 36 [YP09.mkChunk 0 (CZero 36)]) (ss_mem ssx))] end.
{ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst].
pz_bases. split; [lia|]. split; [lia|]. split.
- intros o0 Ho0. apply (apresent_writable SEGS). apply (HOp _ _ HJ3). lia.
- apply Forall_cons; [|apply Forall_nil]. apply pz_chunk_zero. intros i Hi.
replace (o + 0 + i) with (o + i) by lia. rewrite (Heff3 i Hi). reflexivity. }
{ lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end.
cbn [all_disjoint]. unfold extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
pz_bases.
revert Hslo Hshi H47 Hceil Hwin Hstk0 WS C1 Hsp1r Hob0 Hob1 Hob12 Hobu Ho4096 Ho47 HF4096 HFceil HFapp HFimg
HsepO Hosh Howin Hoimg Hsp0 HF8lo HF8hi.
unfold in_app, off_img, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SB. clear. intros. repeat split; pzs_lia. }
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
pose proof (st_ok_pi_add_region Ev ssx msx (YP09.mkRegion (Some 12%nat) 0 36 0 36 [YP09.mkChunk 0 (CZero 36)]) HS eq_refl ROK RDJ) as HS' end.
clear HS ROK RDJ; rename HS' into HS. pz_norm HS.
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs 529%nat in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_regionP) in
pose proof (ast_ok_pi_set_region Ex ssx msx i r (set_window r 0 0) HS ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
(region_ok_rewindow _ Ex _ r 0 0 (st_ok_pi_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity)) ltac:(intros o0 Ho0; lia))) as HS' end.
clear HS; rename HS' into HS. pz_norm HS.
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs 516%nat in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_regionP) in
pose proof (ast_ok_pi_set_region Ex ssx msx i r (set_window r 0 0) HS ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
(region_ok_rewindow _ Ex _ r 0 0 (st_ok_pi_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity)) ltac:(intros o0 Ho0; lia))) as HS' end.
clear HS; rename HS' into HS. pz_norm HS.
(* The shadow entry of the out struct at the memset's memory (the walk's only one: it names no byte of f). *)
destruct (pzs_out_shadow B LAWS STK sp0 FP ly S lyc Sc own W memc mdc S2 _ _ (sp - REAC_CTRL_PARSE_STK) sp o
HAR (proj1 HJ3) Hownf HfinS2 Eab Hstk Howin Ho4096 Hosh KP (fun a Ha => proj1 (HOW a Ha)) HRo) as [HRo3 _].
unbox.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ (restrict _ ?msv) =>
assert (SHOK : sh_ok SEGS PZx PZ_SH0 Ev (mrestrict (w_H W) (ms_mem msv)))
by (apply (pzs_shok Ev _ _ o); [rewrite AGX by lia; exact E12 | rewrite AGX by lia; exact E32 | lia | exact Ho47 | exact Hosh | exact HRo3]) end.
pose proof (paj_run_to (fx := fq) B LAWS) as RUNTO. pose proof (paj_run (fx := fq) B LAWS) as RUN.
pose proof (paj_branch (fx := fq) (PI := PI)) as BR.
assert (Hh : cp_hdr n fr = false)
by (unfold cp_hdr; replace (50 <=? n) with false by (symmetry; apply Z.leb_gt; lia); reflexivity).
(* 4. 0x875e4 li a0,50; 0x875e8 bltu s6,a0 -> 0x878bc: len < 50. *)
pzs_run.
psrr_branch_tok RUN BR HS SHOK PZspan.
{ (* len < 50: 0x878bc andi a0,s3,3 (0: o is 8-aligned; its bnez to 0x87ca0 decided), to cut J. *)
clear Hc. pzs_run. pzs_join. }
(* 50 <= len: not this walk's path (n < 50). *)
exfalso. rewrite branch_ltu_U in Hc.
lazymatch type of Hc with context [U ?Ev (SOff 11 0)] =>
assert (A11 : ew Ev 11 = Z_to_bv 64 n) by (rewrite AGX by lia; exact E11);
rewrite (U_atom Ev 11 n A11 ltac:(lia)) in Hc end.
rewrite U_lit in Hc by lia. apply Z.ltb_ge in Hc. lia.
Qed.
(* ---- The short walk (n < 50): from the entry to cut A0, then pzs_segAJ to cut J; cut J onwards is the
   hypothesis (CtrlParseEpi.v). The statement is disco A's `Hypothesis pz_segShort`
   (a working branch 9052e8f424d lib/A/Prog/CtrlParseWalk.v:58-75) over the Y listing. ---- *)
Lemma pz_segShort : forall B G, pz_rt B G ->
  (forall c, pz_ok B c -> pz_cutJ_spec B c) ->
  forall (fq : YK11.FPState) STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
  (regs : bvmap 5 word) ch (f n o : Z) (fr : list byte),
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) memc) ->
  YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  getr regs 10 = w64 f -> getr regs 11 = w64 n -> getr regs 12 = w64 o ->
  achain lyc (aview SEGS (w_H W) memc) (spZ regs) (s0Z regs) ch ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - REAC_CTRL_PARSE_STK -> spZ regs <= sp0 ->
  spZ regs + 32 <= ly_top lyc ->
  Z.of_nat (length (frames Sc)) <= REAC_CTRL_PARSE_DEPTH ->
  0 <= n < 50 -> length fr = 50%nat ->
  pz_ook B STK sp0 FP ly S lyc Sc own W memc (spZ regs) o ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_both3_reac_ctrl_parse) regs memc mdc)
    (treac_ctrl_parse_post B fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs o n fr).
Proof.
intros B G RT HJc fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ch f n o fr
HJ HROD Hra Hra4 Hgp Htp H10 H11 H12 Hch Hal16 Hwin Hsp0 Htop32 Hroom Hn Hflen HOOK.
pose proof RT as RT0. pz_open_rt RT0.
pose proof HJ as HJe.
assert (Hn64 : 0 <= n < 2 ^ 64) by lia.
pose proof HOOK as (Ho32 & Ho4096 & Ho47 & Hoam & Hoimg & Hosh & Hoce & HRo & HHo & HOW).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_CTRL_PARSE_STK = 8336) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres &
(Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop) & _).
assert (Hownf : forall cid pos, In (cid, pos) own -> In (cid, pos) (frames Sc)).
{ intros cid pos Hin. pose proof HJ as (_ & _ & _ & _ & _ & Hfrs & _). rewrite Hfrs. apply in_or_app. left. exact Hin. }
assert (Hstk : alloc_ceiling <= sp0 - STK) by lia.
(* The entry state of the short walk: no region and no fact for the frame f, the out struct's shadow entry. *)
destruct (pz_entry0 B LAWS TL TLF fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs f n o fr
HJ H10 H11 H12 Hn64 Hal16 Hwin Hsp0 HOOK) as [HS SHOK].
destruct (pz_env (as_uar_cell B) regs fr f n o H10 H11 H12) as (EE & E10 & E11 & E12 & E32 & E33 & E34 & EFB & EOB).
set (E := Eimg (Ereg regs (pz_extra (as_uar_cell B) (spZ regs) fr))) in *.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
(* Atom 10 (f, held in s5) is only carried: its value is the register's own. *)
assert (B10 : bv_unsigned (ew E 10) = bv_unsigned (getr regs 10)) by (rewrite (EE 10%nat 10%bv eq_refl); reflexivity).
assert (B12 : bv_unsigned (ew E 12) = o) by (rewrite E12; apply unsigned_lit_small; lia).
assert (B241 : bv_unsigned (ew E 241) = VAL (A_OBJ 0))
by (change 241%nat with (A_OBJ 0); rewrite (EOB 0%nat ltac:(lia)); apply unsigned_lit_small; pose proof (pa_val_range (A_OBJ 0)); lia).
assert (B242 : bv_unsigned (ew E 242) = VAL (A_OBJ 1))
by (change 242%nat with (A_OBJ 1); rewrite (EOB 1%nat ltac:(lia)); apply unsigned_lit_small; pose proof (pa_val_range (A_OBJ 1)); lia).
assert (B253 : bv_unsigned (ew E 253) = VAL (A_OBJ 12))
by (change 253%nat with (A_OBJ 12); rewrite (EOB 12%nat ltac:(lia)); apply unsigned_lit_small; pose proof (pa_val_range (A_OBJ 12)); lia).
pose proof (pa_obj_img 0 ltac:(lia)) as Hob0. pose proof (pa_obj_img 1 ltac:(lia)) as Hob1.
pose proof (pa_obj_img 12 ltac:(lia)) as Hob12.
pose proof (palf_uar_img B TLF) as Hobu. pose proof (palf_uar_al B TLF) as Huar4.
assert (B34 : bv_unsigned (ew E 34) = as_uar_cell B)
by (rewrite E34; apply unsigned_lit_small; unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in Hobu; lia).
set (sp := spZ regs) in *. set (sp1 := pz_sp1 sp) in *.
destruct (sp1_facts (sp - 128) ltac:(lia) ltac:(rewrite <- Zminus_mod_idemp_l, Hal16; reflexivity)) as (Hsp1r & Hsp1al & Hsp1al16).
change (32 * ((sp - 128) / 32)) with sp1 in Hsp1r, Hsp1al, Hsp1al16.
assert (B33 : bv_unsigned (ew E 33) = sp1) by (rewrite E33; apply unsigned_lit_small; lia).
(* The walk's stack window lies above the allocation ceiling. *)
assert (Hce : alloc_ceiling <= sp - REAC_CTRL_PARSE_STK) by lia.
assert (Hshi64 : sp <= 2 ^ 64) by lia.
pose proof (paj_run (fx := fq) B LAWS) as RUN.
pose proof (paj_run_to (fx := fq) B LAWS) as RUNTO.
pose proof (pz_kept_refl B lyc Sc W memc (sp - REAC_CTRL_PARSE_STK) sp o ltac:(intros a Ha; apply Hpres; lia)) as KP.
unfold cfg_at. change (w64 (BASE + AF_both3_reac_ctrl_parse)) with (Z_to_bv 64 (BASE + AF_both3_reac_ctrl_parse)).
(* 1. The saved registers, to the instruction after the realignment of sp (+0x40). The regions: the machine
   stack, the four image words (read-only), the out struct. *)
paj_run_to_tok RUNTO HS HJ SHOK PZspan (AF_both3_reac_ctrl_parse + 0x40).
{ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?lyx ?own' =>
let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk spx fp b0 bc lyx own') end.
eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (spZ regs - sp0)); [reflexivity | rewrite Usp; lia | cbn; lia | cbn; lia |].
do 4 (apply awr_ok_cons_ro; [cbn; lia|]).
eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 12%nat o); [reflexivity | exact B12 | | apply awr_ok_nil].
intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. exact (proj1 (HOW a ltac:(lia))). }
lazymatch type of HFr with frame_of ?Ef ?rsf (mrestrict _ ?mA) (mrestrict _ ?mB) =>
assert (Hw1 : forall b wlo whi a, In (b, wlo, whi) (windows rsf) -> base_val Ef b + wlo <= a < base_val Ef b + whi ->
(fun a => (sp - 144 <= a < sp) \/ (o <= a < o + 36)) a) by (pz_win_tac ltac:(fun H => rewrite ?Usp, ?B12 in H));
pose proof (pz_kept_run B LAWS lyc Sc W memc mdc mA mB (sp - REAC_CTRL_PARSE_STK) sp o (fun _ => False)
(fun a => (sp - 144 <= a < sp) \/ (o <= a < o + 36)) HAR Hce Hshi64 Hoimg
ltac:(intros; contradiction) ltac:(intros; contradiction) ltac:(intros; contradiction) ltac:(intros; contradiction)
ltac:(intros a Ha; cbv beta in Ha; destruct Ha; [left | right; left]; lia) KP
(kept_of_frame _ _ _ _ _ _ HFr Hw1)
(fun a Ha => apresent_grows _ _ _ a HG Ha)) as KP' end.
clear KP Hw1 HF HFr HG; rename KP' into KP.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres1 & _).
(* 2. sp is realigned to 32 bytes: atom 33 names it; the stack region keeps the saved registers and a
   new region holds sp1 + [0, 32). *)
assert (E2' : ew E 2 = Z_to_bv 64 (spZ regs)) by (rewrite (EE 2%nat 2%bv eq_refl); unfold spZ; symmetry; apply Z_to_bv_bv_unsigned).
pose proof (st_ok_pi_restrict_reg (w_H W) E _ _ 2%bv HS) as R2.
lazymatch type of R2 with _ = sv_denot _ (sr_get (ss_regs ?ssx) _) =>
let e := eval vm_compute in (sr_get (ss_regs ssx) 2%bv) in change (sr_get (ss_regs ssx) 2%bv) with e in R2 end.
rewrite (denot_and_m32 E 2 sp (-128) E2') in R2 by lia.
lazymatch type of HS with st_ok_pi _ _ _ ?ssx ?msx =>
pose proof (ast_ok_pi_set_reg_fp E ssx msx 2%bv (SOff 33 0) HS eq_refl
ltac:(cbn [ms_regs restrict]; rewrite R2; cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)) as HS' end.
clear HS R2; rename HS' into HS; pz_norm HS.
lazymatch type of HS with st_ok_pi _ _ _ ?ssx ?msx =>
pose proof (st_ok_pi_add_fact E ssx msx 33%nat (mkAF (2 ^ 46 - 512) (2 ^ 47) 5) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E33, unsigned_lit_small by lia; change (2 ^ 5) with 32; lia)) as HS' end.
clear HS; rename HS' into HS; pz_norm HS.
lazymatch type of HS with st_ok_pi _ _ _ ?ssx ?msx =>
let rs' := eval vm_compute in (pz_trim (ss_mem ssx)) in
pose proof (st_ok_pi_submem E ssx msx rs' HS ltac:(cbn [ss_mem]; submem_to) ltac:(vm_compute; reflexivity)) as HS' end.
clear HS; rename HS' into HS; pz_norm HS.
lazymatch type of HS with st_ok_pi _ _ _ ?ssx ?msx =>
pose proof (st_ok_pi_add_region E ssx msx (YP09.mkRegion (Some 33%nat) 0 32 0 32 []) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
rewrite E33, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split; [|constructor];
intros o0 Ho0; apply (apresent_writable SEGS); apply Hpres1; lia)
ltac:(cbn [ss_mem]; cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite ?Usp, ?B12, ?B34, ?B241, ?B242, ?B253, E33, unsigned_lit_small by lia;
repeat split; lia)) as HS' end.
clear HS; rename HS' into HS; pz_norm HS.
(* 3. To the side-stack frame's allocation (+0x70): the use-after-return flag cell holds 1. *)
paj_run_tok RUN HS HJ SHOK PZspan.
{ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?lyx ?own' =>
let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk spx fp b0 bc lyx own') end.
eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 33%nat (sp1 - sp0)); [reflexivity | rewrite B33; lia | cbn; lia | cbn; lia |].
eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (sp - sp0)); [reflexivity | rewrite Usp; lia | cbn; lia | cbn; lia |].
do 4 (apply awr_ok_cons_ro; [cbn; lia|]).
eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 12%nat o); [reflexivity | exact B12 | | apply awr_ok_nil].
intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. exact (proj1 (HOW a ltac:(lia))). }
lazymatch type of HFr with frame_of ?Ef ?rsf (mrestrict _ ?mA) (mrestrict _ ?mB) =>
assert (Hw2 : forall b wlo whi a, In (b, wlo, whi) (windows rsf) -> base_val Ef b + wlo <= a < base_val Ef b + whi ->
(fun a => (sp1 <= a < sp) \/ (o <= a < o + 36)) a) by (pz_win_tac ltac:(fun H => rewrite ?Usp, ?B12, ?B33 in H));
pose proof (pz_kept_run B LAWS lyc Sc W memc mdc mA mB (sp - REAC_CTRL_PARSE_STK) sp o (fun _ => False)
(fun a => (sp1 <= a < sp) \/ (o <= a < o + 36)) HAR Hce Hshi64 Hoimg
ltac:(intros; contradiction) ltac:(intros; contradiction) ltac:(intros; contradiction) ltac:(intros; contradiction)
ltac:(intros a Ha; cbv beta in Ha; destruct Ha; [left | right; left]; lia) KP
(kept_of_frame _ _ _ _ _ _ HFr Hw2)
(fun a Ha => apresent_grows _ _ _ a HG Ha)) as KP' end.
clear KP Hw2 HF HFr HG; rename KP' into KP.
prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
rewrite E33 in R2. rewrite (EE 3%nat 3%bv eq_refl) in R3. rewrite (EE 4%nat 4%bv eq_refl) in R4.
pmkst HS. rewrite (palf_sm1 B TLF).
pose proof (count_cid_le_length 1 (frames Sc)) as Hcnt.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (aj_stack_malloc_atS SEGS B LAWS Hsegs (pal_env B TL) ML SMP 1 (ASM1 fq) ltac:(lia) W (ms_regs msX) (ms_mem msX)
STK sp0 FP ly S W0 mem0 md0 own lyc Sc _ k (sp1 - sp0) _ HJ) end.
- unfold spZ at 1. rewrite R2, unsigned_lit_small by lia. lia.
- rewrite Zminus_mod, Hsp1al16, Hsp0al. reflexivity.
- lia. - rewrite Hes; lia.
- rewrite R3. exact Hgp. - rewrite R4. exact Htp.
- exact R1. - apply ret_ok_codeptr_v; [lia | reflexivity].
- change (fs_frames 1) with 8192. unfold REAC_CTRL_PARSE_DEPTH in Hroom. lia. }
cbv beta. clear R1 R2 R3 R4 SHOK.
intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & fpos & -> & HJ2 & HP2 & Ha0 & Eab & Hfrs2 & Hnin & Hnev2 & Hbb2 & Hz & Hflag & HK & HJin & (fS2 & ES2)).
pose proof HK as (K1 & K2 & K3 & K4 & K5 & K6).
pose proof (pz_kept_trans B lyc Sc W memc _ mem2 (sp - REAC_CTRL_PARSE_STK) sp _ _ o _ Hce Hshi64 KP HK
  ltac:(rewrite Hes; lia) ltac:(lia) ltac:(intros ? [])) as KP'.
clear KP; rename KP' into KP.
(* 4. After the allocation: the registers it clobbers are havocked from atom 512 on, the regions kept (the
   frame f has none: the contract says nothing about it when n < 50). *)
destruct (al_const _ _ LAWS _ _ _ _ _ (proj1 HJ)) as (Kc0 & Ku0 & Kg0 & Kgu0).
destruct (al_const _ _ LAWS _ _ _ _ _ (proj1 HJ2)) as (Kc2 & Ku2 & Kg2 & Kgu2).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kg0, Kg2. rewrite (pal_cell B TL) in Kc0, Kc2.
rewrite (palf_got_uar B TLF) in Kgu0, Kgu2.
pose proof (proj1 HJ2) as HAR2.
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
assert (Hfin2 : In (1, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
assert (HfinS2 : forall c p, In (c, p) (frames Sc) -> In (c, p) (frames S2)) by (intros c p Hcp; rewrite Hfrs2; right; exact Hcp).
(* Each byte of the out struct lies in a caller block or a caller frame (pzs_out_loc). *)
assert (Loc_o : forall x, o <= x < o + 36 ->
(exists b m, In (b, m) (ablocks B lyc Sc) /\ b <= x < b + req_size m) \/
(exists cid pos, In (cid, pos) (frames Sc) /\ frame_addr lyc cid pos <= x < frame_addr lyc cid pos + fs_frame_bytes cid))
by (intros x Hx; exact (pzs_out_loc B LAWS STK sp0 FP ly S lyc Sc own W memc mdc o x HAR Hownf Hstk Hoce Hosh Hx (proj1 (HOW x Hx)))).
jafter_call_keep_hi HS 512%nat regs2 (mrestrict (w_H W) mem2) HP2 [0; 1; 2; 3; 4; 5; 6]%nat HS2.
match type of HS2 with ?Q -> _ => assert (HQ : Q); [| specialize (HS2 HQ); clear HQ] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
- apply (pz_region_kept E _ _ _ 33 sp1); [exact B33 | intros a Ha; apply K1; [lia | intros [? ?]; lia] | intros a Ha; apply Hpres2; lia].
- apply (pz_region_kept E _ _ _ 2 sp); [exact Usp | intros a Ha; apply K1; [lia | intros [? ?]; lia] | intros a Ha; apply Hpres2; lia].
- apply (region_kept_val_at E _ _ 242 (VAL (A_OBJ 1)) 8 (as_uar_cell B)); [exact B242 | exact (val_mem_of_rdword SEGS _ _ _ _ Kgu0) | exact (val_mem_of_rdword SEGS _ _ _ _ Kgu2) | lia].
- apply (region_kept_val_at E _ _ 34 (as_uar_cell B) 4 1); [exact B34 | exact (val_mem_of_rd32 SEGS _ _ _ _ Ku0) | exact (val_mem_of_rd32 SEGS _ _ _ _ Ku2) | lia].
- apply (region_kept_val_at E _ _ 241 (VAL (A_OBJ 0)) 8 (VAL (A_OBJ 12))); [exact B241 | exact (val_mem_of_rdword SEGS _ _ _ _ Kg0) | exact (val_mem_of_rdword SEGS _ _ _ _ Kg2) | lia].
- apply (region_kept_val_at E _ _ 253 (VAL (A_OBJ 12)) 8 SHADOW_OFF); [exact B253 | exact (val_mem_of_rdword SEGS _ _ _ _ Kc0) | exact (val_mem_of_rdword SEGS _ _ _ _ Kc2) | lia].
- (* the out struct: each byte in a caller block or a caller frame *)
  apply (pz_region_kept E _ _ _ 12 o); [exact B12 | |].
  + intros a Ha. destruct (Loc_o a ltac:(lia)) as [(b & m & Hb & Hr)|(cid & pos & Hin & Hr)].
    * replace a with (b + (a - b)) by lia. apply (K2 b m (a - b) Hb); [lia | intros []].
    * apply (K4 cid pos a Hin); [left; unfold in_zr, frame_rng; cbn [fst snd]; lia | intros []].
  + intros a Ha. refine (proj1 (awr_byte_present SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ2 _)).
    rewrite Eab. exact (pz_awr_cons _ _ _ _ _ _ _ _ a (proj1 (HOW a ltac:(lia)))). }
rewrite <- restrict_mkst_fx in HS2. clear HS; rename HS2 into HS.
(* 4b. The frame (1, fpos): atom 516 is its address, 528 its flag, 529 its shadow; a region for the
   frame and one for its 16 shadow bytes. *)
assert (AGX0 : forall n0, (n0 < 512)%nat -> ew E n0 = ew E n0) by reflexivity.
pz_rebase HS AGX0. rename AGX0 into AGX.
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HAR2 Hfin2) as (HFal & HFapp & HFpres & HFSpres).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 1 fpos HAR2 Hfin2) as (HF4096 & HFceil & _).
destruct (FFL _ _ _ _ _ 1 fpos HAR2 Hfin2) as (HFLpres & HFLown & (HFLapp & HFLimg) & (HFL4096 & _ & HFLce)).
pose proof (frm_off_imgP B _ _ _ _ _ 1 fpos HAR2 Hfin2) as HFimg.
change (fs_frame_bytes 1) with 128 in HFapp, HFceil, HFpres, HFSpres, Hz, Hflag, HFimg.
change (128 / 8) with 16 in HFSpres.
set (F := frame_addr lyc 1 fpos) in *. set (FL := flag_addr lyc 1 fpos) in *.
assert (EF : F = frame_addr lyc 1 fpos) by reflexivity. assert (EFL : FL = flag_addr lyc 1 fpos) by reflexivity.
destruct (pz_nf_sep B LAWS lyc Sc S2 W mem2 md2 fpos F FL HAR2 Hfrs2 Eab EF EFL FFL) as (N1 & N2 & N3 & N4).
(* The frame is apart from the out struct (awr_byte, pz_awr_nf). *)
assert (HsepO : o + 36 <= F \/ F + 128 <= o).
{ apply (pzs_sep F FL o 36); [lia|]. intros a Ha.
  exact (pz_awr_nf B STK sp0 FP ly S lyc Sc own W memc mdc a F FL HAR Hownf N1 N3 N4 Hstk (proj1 (HOW a Ha))). }
prreg HS (10%bv : bv 5) RF. rewrite Ha0 in RF. symmetry in RF. unfold w64 in RF.
assert (HFq : F = 32 * (F / 32)) by (pose proof (Z.div_mod F 32 ltac:(lia)); lia).
assert (HF8 : F / 8 = 4 * (F / 32)) by (rewrite HFq at 1; replace (32 * (F / 32)) with (4 * (F / 32) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
assert (HF8lo : 512 <= F / 8) by (apply Z.div_le_lower_bound; lia).
assert (HF8hi : F / 8 + 16 <= 17592184995840).
{ assert (Hd : (F + 16 * 8) / 8 <= 140737479966720 / 8) by (apply Z.div_le_mono; lia).
rewrite Z.div_add in Hd by lia. change (140737479966720 / 8) with 17592184995840 in Hd. lia. }
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp.
add_atom HS 528%nat (Z_to_bv 64 FL) E528. pz_rebase HS AGX.
add_atom HS 529%nat (Z_to_bv 64 (SB + F / 8)) E529. pz_rebase HS AGX.
pose proof E32 as E32'.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
pose proof (st_ok_pi_add_fact Ev ssx msx 516%nat (HPTR 5) HS
ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite RF, unsigned_lit_small by lia; change (2 ^ 5) with 32;
split; [lia|]; split; [rewrite HFq, Z.mul_comm; apply Z_mod_mult | lia])) as HS' end.
clear HS; rename HS' into HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
pose proof (st_ok_pi_add_fact Ev ssx msx 528%nat (HPTR 0) HS
ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite E528, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS' end.
clear HS; rename HS' into HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
pose proof (st_ok_pi_add_fact Ev ssx msx 529%nat (mkAF (SB + 512) (SB + 17592186044416) 2) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E529, unsigned_lit_small by (unfold SB; lia); change (2 ^ 2) with 4; unfold SB;
split; [lia|]; split; [rewrite HF8; replace (2147450880 + 4 * (F / 32)) with ((536862720 + F / 32) * 4) by lia; apply Z_mod_mult | lia])) as HS' end.
clear HS; rename HS' into HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
pose proof (st_ok_pi_add_alias Ev ssx msx _ _ HS (shadow_decl_ok Ev 516 32 529 F SB RF ltac:(lia) E32' E529)) as HS' end.
clear HS; rename HS' into HS. pz_norm HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
assert (ROK : region_ok SEGS Ev (ms_mem msx) (fframe_region 516 528 1 []));
[| assert (RDJ : all_disjoint Ev (fframe_region 516 528 1 []) (ss_mem ssx))] end.
{ unfold region_ok, fframe_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val app ms_mem restrict mkst].
change (fs_frame_bytes 1) with 128. rewrite RF, unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split.
- intros o0 Ho0. apply (apresent_writable SEGS). apply (proj1 (HFpres (F + o0) ltac:(lia))).
- apply Forall_cons; [|apply Forall_nil].
change (128 - 8) with 120.
eapply (chunk_ok_val SEGS _ _ F 120 8 _ FL).
+ cbn [sv_denot]. rewrite E528, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
+ pz_vside.
+ pz_vside.
+ replace (F + 120) with (F + 128 - 8) by lia. exact (val_mem_of_rdword SEGS _ _ _ _ Hflag). }
{ lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end.
cbn [all_disjoint]. unfold extent_disjoint, fframe_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
change (fs_frame_bytes 1) with 128. pz_bases.
revert Hslo Hshi H47 Hceil Hwin Hstk0 WS C1 Hsp1r Hob0 Hob1 Hob12 Hobu Ho4096 Ho47 Hoce HF4096 HFceil HFapp HFimg HsepO Hsp0.
unfold in_app, off_img, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. clear. intros. repeat split; first [lia | match goal with |- ?g => idtac "DISJ516" g; fail end]. }
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
pose proof (st_ok_pi_add_region Ev ssx msx (fframe_region 516 528 1 []) HS eq_refl ROK RDJ) as HS' end.
clear HS ROK RDJ; rename HS' into HS. pz_norm HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
assert (ROK : region_ok SEGS Ev (ms_mem msx) (fshadow_region 529 1 0 16 [YP09.mkChunk 0 (CVal 8 (SLit 0)); YP09.mkChunk 8 (CVal 8 (SLit 0))]));
[| assert (RDJ : all_disjoint Ev (fshadow_region 529 1 0 16 [YP09.mkChunk 0 (CVal 8 (SLit 0)); YP09.mkChunk 8 (CVal 8 (SLit 0))]) (ss_mem ssx))] end.
{ unfold region_ok, fshadow_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst].
change (fs_frame_bytes 1 / 8) with 16. rewrite E529, unsigned_lit_small by (unfold SB; lia).
split; [unfold SB; lia|]. split; [unfold SB; lia|]. split.
- intros o0 Ho0. apply (apresent_writable SEGS). unfold shadow_addr in HFSpres. rewrite <- SB_SHADOW_OFF in HFSpres.
apply (proj1 (HFSpres o0 ltac:(lia))).
- unfold zero_shadow, shadow_of_addr in Hz. rewrite <- SB_SHADOW_OFF in Hz.
apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
+ eapply (chunk_ok_val SEGS _ _ (SB + F / 8) 0 8 _ 0); [reflexivity | pz_vside | pz_vside |].
apply val_mem_zero8. intros ii Hii. replace (SB + F / 8 + 0 + ii) with (SB + F / 8 + ii) by lia. apply Hz. change (128 / 8) with 16. lia.
+ eapply (chunk_ok_val SEGS _ _ (SB + F / 8) 8 8 _ 0); [reflexivity | pz_vside | pz_vside |].
apply val_mem_zero8. intros ii Hii. replace (SB + F / 8 + 8 + ii) with (SB + F / 8 + (8 + ii)) by lia. apply Hz. change (128 / 8) with 16. lia. }
{ lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end.
cbn [all_disjoint]. unfold extent_disjoint, fshadow_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
change (fs_frame_bytes 1 / 8) with 16. change (fs_frame_bytes 1) with 128. pz_bases.
revert Hslo Hshi H47 Hceil Hwin Hstk0 WS C1 Hsp1r Hob0 Hob1 Hob12 Hobu Ho4096 Ho47 Hosh Hoce HF4096 HFceil HFapp HFimg Hsp0 HF8lo HF8hi.
unfold in_app, off_img, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SB. clear. intros. repeat split; first [lia | match goal with |- ?g => idtac "DISJ529" g; fail end]. }
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
pose proof (st_ok_pi_add_region Ev ssx msx (fshadow_region 529 1 0 16 [YP09.mkChunk 0 (CVal 8 (SLit 0)); YP09.mkChunk 8 (CVal 8 (SLit 0))]) HS eq_refl ROK RDJ) as HS' end.
clear HS ROK RDJ; rename HS' into HS. pz_norm HS.
(* Cut A0: the rest of the walk is pzs_segAJ. *)
lazymatch type of HS with st_ok_pi _ _ _ ?ssx _ => change ssx with ss_cutA0 in HS end.
set (c := mkPZ fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ch f n o fr S2 fpos).
assert (Hok : pz_ok B c).
{ unfold pz_ok, c. cbn [cx_fq cx_STK cx_sp0 cx_FP cx_ly cx_S cx_W0 cx_mem0 cx_md0 cx_own cx_lyc cx_Sc cx_W cx_memc
cx_mdc cx_k cx_regs cx_ch cx_f cx_n cx_o cx_fr cx_S2 cx_fpos].
(* The contract's premises about f hold under 50 <= n only, which n < 50 refutes. *)
exact (conj HJe (conj HROD (conj Hra (conj Hra4 (conj Hgp (conj Htp (conj H10 (conj H11 (conj H12 (conj Hn64
(conj Hch (conj Hal16 (conj Hwin (conj Hsp0 (conj Htop32 (conj Hroom (conj Hflen
(conj (fun Hbig => False_ind _ (proj1 (Z.lt_nge _ _) (proj2 Hn) Hbig)) (conj HOOK
(conj Hfrs2 (conj Eab (conj Hnin (ex_intro _ fS2 ES2))))))))))))))))))))))). }
lazymatch type of HS with st_ok_pi _ _ ?Ev _ (restrict _ ?msv) =>
assert (Hcur : pz_cur B c Ev msv md2);
[ unfold pz_cur, pz_E0, c; cbn [cx_fq cx_STK cx_sp0 cx_FP cx_ly cx_S cx_W0 cx_mem0 cx_md0 cx_own cx_lyc cx_Sc cx_W cx_memc
cx_mdc cx_k cx_regs cx_ch cx_f cx_n cx_o cx_fr cx_S2 cx_fpos ms_mem];
split; [assumption|]; split; [exact AGX|]; split; [exact RF|]; split; [exact E528|]; split; [exact E529|];
split; [exact HJ2 | exact KP]
| exact (pzs_segAJ B G RT c Hok (HJc c Hok) (proj2 Hn) Ev msv md2 Hcur HS) ] end.
Qed.
End d.
End b.

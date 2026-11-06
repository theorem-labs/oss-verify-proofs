(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: copied from lib/A/Prog/CPgWalkFrame.v and moved to image B (the ASan-UBSan build):
   the image-A core modules are image B's (lib/AU), YImgTop is YImgTopU, the CA_ constants are CB_ ones with
   image B's values; lemma and tactic names unchanged. *)
(* Modified by Theorem Labs, 2026-10: the proof of cpg_stack_malloc_keep_io is the text of lib/Reusable/YC85.v's
   aj_stack_malloc_atS (copied there from proofs/libreac/fuzz_knock/lib/Reusable/YC85.v, origin/ossv/recipes
   4b6f0df50aa7), with the runtime contract's kept-memory clause and the model clause carried to the post, for
   libdiginet/fuzz_codec's ASan build (image B); the rest of the file is new. *)
(* The side-stack frame plumbing of the image-B walks of codec's own functions.
   - The request: cpg_stack_malloc_keep is aj_stack_malloc_atS with the runtime contract's own kept-memory clause
     (every byte owned neither before nor after the call and off the call's window is kept); cpg_stack_malloc_keep_io
     adds same_io between the models before and after the call.
   - The kept invariant of a frame-owning walk (CPgWalkKept): cw_fresh_frame / cw_fresh_frame_j (a byte of the new
     frame, of its shadow, or its flag byte is fresh), cw_tcj_of_acall (a runtime call's acall_kept inside the walk's
     window is a tcj_kept).
   - After the request: cw_frame_afacts (the atom facts of F, of the flag address and of the frame's shadow address),
     the regions cw_frame_region / cw_fshadow_region (zero chunks) / cw_flag_region with their region_ok lemmas for
     ast_ok_add_region, cw_flag_apart (the flag region's disjointness), the write windows cw_awr_ok_cons_frame /
     cw_awr_ok_cons_fshadow.
   - The release: cw_awrf_flag_front (the write premise of aj_run_flag; AWalkFw1.flag0 proves the flag byte 0) and
     cw_fresh_frame_j for the kept invariant through it (CPgWalkKeptU.cw_kept_step); the leaf after it:
     cw_frames_back (frames back to the call state's, from the two journals), cw_perm_release / cw_mo_le_release
     (blocks and meter through stack_free_state), all three in cw_release_post, cw_frame_start / cw_frame_step (the
     blocks permutation and the meter the walk carries from the request to the release), and the tactics cw_io,
     cw_frame_clauses and cw_frame_leaf (cw_leaf with those clauses; the memory clause from the carried tcj_kept). *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YI16 YM05 YC85.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw0 YCef YF0l YCej YCeh YCem YCep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw1 AWalkFw2 YCfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgWalkU CPgWalkKeptU.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* The regions of a side-stack frame of class cid: the frame based at atom n with the flag address (atom nf) at its
   last 8 bytes, the frame's shadow based at atom s with the zero 8-byte chunks the request leaves, the flag byte. *)
Definition cw_frame_region (n nf : nat) (cid : Z) : YP09.region :=
YP09.mkRegion (Some n) 0 (fs_frame_bytes cid) 0 (fs_frame_bytes cid) [YP09.mkChunk (fs_frame_bytes cid - 8) (CVal 8 (SOff nf 0))].
Definition cw_zero_chunks (k : nat) : list YP09.chunk :=
map (fun j => YP09.mkChunk (8 * Z.of_nat j) (CVal 8 (SLit 0))) (seq 0 k).
Definition cw_fshadow_region (s : nat) (cid : Z) : YP09.region :=
YP09.mkRegion (Some s) 0 (fs_frame_bytes cid / 8) 0 (fs_frame_bytes cid / 8) (cw_zero_chunks (Z.to_nat (fs_frame_bytes cid / 64))).
Definition cw_flag_region (nf : nat) : YP09.region := YP09.mkRegion (Some nf) 0 1 0 1 [].

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

(* ================================ the request ================================ *)
(* A state with more frames and the same chunks owns no byte the smaller one does not. *)
Lemma cw_not_aowned_set_fs : forall B ly S f a, incl (frames S) (frames (set_fs f S)) ->
~ aowned B ly S a -> ~ aowned B ly (set_fs f S) a.
Proof.
intros B ly S f a Hfr Hno (Hown & Hnc). apply Hno. split; [exact Hown|].
intros [Hc | (cp & Hcp & Hr)]; apply Hnc; [left; exact Hc | right; exists cp; split; [apply Hfr; exact Hcp | exact Hr]].
Qed.
Section h.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Hypothesis errno_low : api_env segs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis stack_malloc_progress : stack_malloc_progressP B.
Lemma cpg_stack_malloc_keep_io : forall cid, astack_malloc_realizes segs B cid -> 0 <= cid <= 10 ->
forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k (o : Z) raw,
ajournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
count_cid cid (frames Sc) < fs_frames cid ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 (pc_stack_malloc (as_code B) cid)) memT (seg_rom segs)) mdc)
(fun W2 c2 => W2 = W /\ exists S2 regs2 mem2 md2 pos,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal segs B STK sp0 FP ly S W0 mem md ((cid, pos) :: own) lyc S2 W mem2 md2 k /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 (frame_addr lyc cid pos) /\
ablocks B lyc S2 = ablocks B lyc Sc /\ frames S2 = (cid, pos) :: frames Sc /\ ~ In (cid, pos) (frames Sc) /\
st_nev S2 = st_nev Sc /\ blocks_bytes S2 = blocks_bytes Sc /\
zero_shadow (aview segs (w_H W) mem2) SHADOW_OFF (frame_addr lyc cid pos) (fs_frame_bytes cid) /\
rdword (aview segs (w_H W) mem2) (frame_addr lyc cid pos + fs_frame_bytes cid - 8) = Some (flag_addr lyc cid pos) /\
acall_kept segs B lyc Sc W memT W mem2 (sp0 + o - ESTACK) (sp0 + o) (fun _ => False) /\
(exists f, S2 = set_fs f Sc) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ aowned B lyc Sc a -> ~ (sp0 + o - ESTACK <= a < sp0 + o) ->
 aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
same_io mdc md2).
Proof.
intros cid ASM Hcid W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k o raw
HJ Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hcnt.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres & Hstatic & F5 & HQT).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof (proj1 errno_low) as [He0 He1].
assert (ASTACK = 16384) as Has by reflexivity. assert (ESTACK = 4096) as Hes by reflexivity.
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
assert (HstkC : astk_ok ESTACK lyc (spZ regsT)).
{ unfold astk_ok, ly_bot in *. rewrite Hsp', Eslo, Eshi, Etop. repeat split; try zlia.
all: rewrite Z.add_mod, Hal16, Hal by zlia; reflexivity. }
assert (HPRE : ecall_pre segs B lyc Sc W regsT memT mdc).
{ split; [exact HAR|]. split; [rewrite Hra; exact Hraw|]. split; [destruct HstkC as (Q1 & _); exact Q1|].
split; [rewrite Eslo, Hsp'; zlia|]. split; [rewrite Eshi, Hsp'; zlia|].
split; [intros a Ha; apply Hpres; rewrite Hsp' in Ha; zlia|]. split; [exact Hgp | exact Htp]. }
pose proof (am_wf _ _ _ _ (proj1 HAR)) as HWF.
destruct (stack_malloc_progress Sc cid HWF Hcid Hcnt) as (pos & S2 & Hpath).
pose proof (ml_stack_malloc _ ML Sc cid HWF Hcid) as HTOK.
destruct (atok_apath _ _ _ [] (PFake cid pos, S2) HTOK Hpath) as (ns' & HQ). unfold stack_malloc_post in HQ.
destruct HQ as (HWF2 & (f & ES2) & _ & Hpos & Hfrs2 & Hfresh).
eapply SRr_mono; [exact (ASM lyc Sc W regsT memT mdc pos S2 HPRE Hcnt Hpath)|].
cbv beta. intros W2 c2 HwleW (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Hres & Hz & Hflag & Hfpres & Hfr & Hpres2).
assert (Hblk : blocks S2 = blocks Sc) by (rewrite ES2; reflexivity).
assert (Eab2 : ablocks B lyc S2 = ablocks B lyc Sc) by (unfold ablocks; rewrite Hblk; reflexivity).
assert (Hnev2 : st_nev S2 = st_nev Sc) by (rewrite ES2; reflexivity).
assert (Hbb : blocks_bytes S2 = blocks_bytes Sc) by (rewrite ES2; reflexivity).
assert (Hsecs2 : st_secs S2 = st_secs Sc) by (rewrite ES2; reflexivity).
assert (HJ1 : ajournal segs B ESTACK (spZ regsT) [] lyc Sc W memT mdc [(cid, pos)] lyc S2 W mem2 md2 0).
{ eapply (call_effect_journal segs B LAWS segs_low errno_low ESTACK lyc Sc W regsT memT mdc lyc S2 W mem2 md2 (fun _ => False) [] [(cid, pos)] 0);
[exact HAR2 | apply layout_le_refl | apply wle_refl | apply same_io_materialized; exact Hsame | | exact Hpres2 | exact HAR | exact HstkC
| cbn; exact Hfrs2 | zlia | zlia | rewrite Hsecs2; zlia | intros a [] | | ].
- intros a H0 H1 H2 H3 _. apply (Hfr a H0 H1 H2). intros H. apply H3. left. exact H.
- intros p n i Hp Hnp. exfalso. apply Hnp. rewrite Eab2. exact Hp.
- rewrite ES2. apply (qtight_ext Sc); [reflexivity | reflexivity | reflexivity | exact HQT]. }
split; [reflexivity|]. exists S2, regs2, mem2, md2, pos.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ rewrite Hsp' in HJ1. replace k with (k + 0) by zlia. change ((cid, pos) :: own) with ([(cid, pos)] ++ own).
eapply (ajournal_sub segs B LAWS segs_low); [exact HJ | exact HJ1 | zlia | zlia | intros a (rg & [] & _)]. }
split; [exact HP|]. split; [exact Hres|]. split; [exact Eab2|]. split; [exact Hfrs2|]. split; [exact Hfresh|].
split; [exact Hnev2|]. split; [exact Hbb|]. split; [exact Hz|]. split; [exact Hflag|].
rewrite Hsp' in HJ1.
split.
{ eapply (acall_kept_of_journal segs B segs_low); [exact HJ1 | exact HAR | intros a (rg & [] & _) | | exact sink_closed_nil].
  intros b m i Hb Hi _. rewrite Eab2. exact Hb. }
split; [exists f; exact ES2|].
split; [|apply same_io_materialized; exact Hsame].
intros a Ha Hno Hw. rewrite Hsp' in Hfr. apply (Hfr a Ha Hno); [|exact Hw].
rewrite ES2. apply cw_not_aowned_set_fs; [|exact Hno].
rewrite <- ES2, Hfrs2. intros x Hx. right. exact Hx.
Qed.
Lemma cpg_stack_malloc_keep : forall cid, astack_malloc_realizes segs B cid -> 0 <= cid <= 10 ->
forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k (o : Z) raw,
ajournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
count_cid cid (frames Sc) < fs_frames cid ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 (pc_stack_malloc (as_code B) cid)) memT (seg_rom segs)) mdc)
(fun W2 c2 => W2 = W /\ exists S2 regs2 mem2 md2 pos,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal segs B STK sp0 FP ly S W0 mem md ((cid, pos) :: own) lyc S2 W mem2 md2 k /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 (frame_addr lyc cid pos) /\
ablocks B lyc S2 = ablocks B lyc Sc /\ frames S2 = (cid, pos) :: frames Sc /\ ~ In (cid, pos) (frames Sc) /\
st_nev S2 = st_nev Sc /\ blocks_bytes S2 = blocks_bytes Sc /\
zero_shadow (aview segs (w_H W) mem2) SHADOW_OFF (frame_addr lyc cid pos) (fs_frame_bytes cid) /\
rdword (aview segs (w_H W) mem2) (frame_addr lyc cid pos + fs_frame_bytes cid - 8) = Some (flag_addr lyc cid pos) /\
acall_kept segs B lyc Sc W memT W mem2 (sp0 + o - ESTACK) (sp0 + o) (fun _ => False) /\
(exists f, S2 = set_fs f Sc) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ aowned B lyc Sc a -> ~ (sp0 + o - ESTACK <= a < sp0 + o) ->
 aview segs (w_H W) mem2 a = aview segs (w_H W) memT a)).
Proof.
intros cid ASM Hcid W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k o raw
HJ Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hcnt.
eapply SRr_mono; [exact (cpg_stack_malloc_keep_io cid ASM Hcid W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k o raw
HJ Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hcnt)|].
cbv beta. intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & pos & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & _).
split; [reflexivity|]. exists S2, regs2, mem2, md2, pos.
exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 (conj H8 (conj H9 (conj H10 (conj H11 (conj H12 (conj H13 H14))))))))))))).
Qed.
End h.

(* ================================ the kept invariant of a frame-owning walk ================================ *)
Section f.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
(* A byte of the walk's own new frame (cid, pos), of the frame's shadow, or the frame's flag byte is fresh for the
   call state (lyc, Sc): S1 is a state with that frame in front of the call state's frames, the call state's blocks
   and the call state's frame addresses. *)
Lemma cw_fresh_frame : frame_flag_lawP tfibsegs B -> forall ly1 S1 (W1 : world tfibsegs) mem1 md1 lyc Sc cid pos a,
AR tfibsegs B ly1 S1 W1 mem1 md1 -> frames S1 = (cid, pos) :: frames Sc ->
(forall b m, In (b, m) (ablocks B ly1 S1) <-> In (b, m) (ablocks B lyc Sc)) ->
(forall c p, frame_addr ly1 c p = frame_addr lyc c p) ->
(in_zr a (frame_rng ly1 (cid, pos)) \/ in_zr a (shadow_addr (frame_addr ly1 cid pos), fs_frame_bytes cid / 8) \/
 a = flag_addr ly1 cid pos) ->
cw_fresh B lyc Sc a.
Proof.
intros FFL ly1 S1 W1 mem1 md1 lyc Sc cid pos a HAR Hfrs Hbl Efa Ha.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hin : In (cid, pos) (frames S1)) by (rewrite Hfrs; left; reflexivity).
destruct (FFL ly1 S1 W1 mem1 md1 cid pos HAR Hin) as (_ & Hfo & (_ & Hfi) & (_ & _ & Hfc)).
destruct Ha as [Hr | [Hr | ->]].
1, 2: assert (Hz : in_zr a (frame_rng ly1 (cid, pos)) \/ in_zr a (shadow_addr (frame_addr ly1 cid pos), fs_frame_bytes cid / 8))
  by (first [left; exact Hr | right; exact Hr]); clear Hr;
  destruct (frame_zone tfibsegs B LAWS ly1 S1 W1 mem1 md1 cid pos a HAR Hin Hz) as (Hc & Hloc);
  split; [exact Hc|];
  split; [ intros Him; destruct Hloc as [(Hx & _) | Hx];
           [ exact (frm_img tfibsegs B LAWS ly1 S1 W1 mem1 md1 cid pos a HAR Hin Hx Him)
           | pose proof (tfib_segs_low a Him) as Hl; clear - Hl Hx C5; lia ] |];
  split; [ intros bb m i Hb Hi Ex; subst a;
           exact (block_not_frame_zone tfibsegs B LAWS ly1 S1 W1 mem1 md1 bb m i cid pos HAR (proj2 (Hbl bb m) Hb) Hin Hi Hz) |];
  intros c p Hcp; apply in_split in Hcp as (s1 & s2 & Es);
  assert (Hno : (in_zr a (frame_rng ly1 (c, p)) \/ in_zr a (shadow_addr (frame_addr ly1 c p), fs_frame_bytes c / 8)) -> False)
    by (intros Hg; apply (frames_zone_disj tfibsegs B LAWS ly1 S1 W1 mem1 md1 (cid, pos) (c, p) [] s1 s2 a HAR);
        [rewrite Hfrs, Es; reflexivity | exact Hz | exact Hg]);
  unfold frame_rng in *; cbn [fst snd] in *; rewrite <- !Efa;
  split; intros Hg; apply Hno; [left | right]; exact Hg.
split; [exact Hfc|]. split; [exact Hfi|].
split.
{ intros bb m i Hb Hi Ex.
  destruct (al_blocks _ _ LAWS ly1 S1 W1 mem1 md1 bb m HAR (proj2 (Hbl bb m) Hb)) as (_ & _ & _ & _ & Hbo & _).
  apply (proj2 (Hbo (bb + i) ltac:(lia))). rewrite <- Ex. exact Hfo. }
intros c p Hcp. assert (Hcp1 : In (c, p) (frames S1)) by (rewrite Hfrs; right; exact Hcp).
destruct (al_frames _ _ LAWS ly1 S1 W1 mem1 md1 c p HAR Hcp1) as (_ & _ & Hfb & Hsb).
unfold frame_rng, in_zr. cbn [fst snd]. rewrite <- !Efa.
split; intros Hg.
- exact (proj2 (Hfb _ Hg) Hfo).
- specialize (Hsb (flag_addr ly1 cid pos - shadow_addr (frame_addr ly1 c p)) ltac:(lia)).
  replace (shadow_addr (frame_addr ly1 c p) + (flag_addr ly1 cid pos - shadow_addr (frame_addr ly1 c p)))
    with (flag_addr ly1 cid pos) in Hsb by lia.
  exact (proj2 Hsb Hfo).
Qed.
(* The same in the coordinates of the call state, from the caller's journal at the call (HJ) and the walk's journal
   with the frame in its own frames (HJ3) and the blocks a permutation of the call state's. *)
Lemma cw_fresh_frame_j : frame_flag_lawP tfibsegs B ->
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ly3 S3 W3 mem3 md3 k3 cid pos a,
ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md0 ((cid, pos) :: own) ly3 S3 W3 mem3 md3 k3 ->
Permutation (ablocks B ly3 S3) (ablocks B lyc Sc) ->
(in_zr a (frame_rng lyc (cid, pos)) \/ in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8) \/
 a = flag_addr lyc cid pos) ->
cw_fresh B lyc Sc a.
Proof.
intros FFL STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ly3 S3 W3 mem3 md3 k3 cid pos a HJ HJ3 HP Ha.
pose proof HJ as (_ & Hly & _ & _ & _ & Hfrs & _). pose proof HJ3 as (HAR3 & Hly3 & _ & _ & _ & Hfrs3 & _).
destruct Hly as (_ & _ & _ & _ & _ & EF & _). destruct Hly3 as (_ & _ & _ & _ & _ & EF3 & _).
assert (Efa : forall c p, frame_addr ly3 c p = frame_addr lyc c p) by (intros c p; unfold frame_addr; rewrite EF, EF3; reflexivity).
assert (Efl : flag_addr ly3 cid pos = flag_addr lyc cid pos) by (unfold flag_addr; rewrite EF, EF3; reflexivity).
apply (cw_fresh_frame FFL ly3 S3 W3 mem3 md3 lyc Sc cid pos a HAR3).
- rewrite Hfrs3, Hfrs. reflexivity.
- intros b m. split; intros Hin; [exact (Permutation_in _ HP Hin) | exact (Permutation_in _ (Permutation_sym HP) Hin)].
- exact Efa.
- unfold frame_rng in *. cbn [fst snd] in *. rewrite Efa, Efl. exact Ha.
Qed.

(* ================================ the frame's facts and regions after the request ================================
   F = frame_addr ly cid pos is 64-aligned (YCem.frame_al64); the walk holds F in atom n, the flag address in atom nf,
   the frame's shadow address SB + F / 8 (= shadow_addr F) in atom s. *)
Lemma cw_frame_afacts : forall E (n nf s : nat) ly S (W : world tfibsegs) mem md cid pos,
frame_flag_lawP tfibsegs B -> AR tfibsegs B ly S W mem md -> In (cid, pos) (frames S) ->
ew E n = Z_to_bv 64 (frame_addr ly cid pos) -> ew E nf = Z_to_bv 64 (flag_addr ly cid pos) ->
ew E s = Z_to_bv 64 (shadow_addr (frame_addr ly cid pos)) ->
afact_ok E n (HPTR 6) /\ afact_ok E nf (HPTR 0) /\ afact_ok E s (mkAF (SB + 512) (SB + 2 ^ 44) 3).
Proof.
intros E n nf s ly S W mem md cid pos FFL HAR Hin En Enf Es.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (frames_bounds tfibsegs B LAWS ly S W mem md cid pos HAR Hin) as (H4096 & Hceil & _).
destruct (frame_al64 tfibsegs B ly S W mem md cid pos HAR Hin) as (H64 & _ & Hb64).
destruct (FFL ly S W mem md cid pos HAR Hin) as (_ & _ & _ & (Hfl0 & _ & Hflc)).
set (F := frame_addr ly cid pos) in *.
assert (HF8 : F / 8 = 8 * (F / 64)).
{ rewrite (Z.div_mod F 64) at 1 by lia. rewrite H64, Z.add_0_r.
  replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by lia. apply Z.div_mul. lia. }
assert (HF8a : 512 <= F / 8) by (apply Z.div_le_lower_bound; lia).
assert (HF8b : F / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia).
unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2]. rewrite En, Enf, Es.
unfold shadow_addr, SHADOW_OFF, SB in *.
rewrite !unsigned_lit_small by lia.
split; [change (2 ^ 6) with 64; split; [lia | split; [exact H64 | lia]]|].
split; [change (2 ^ 0) with 1; rewrite Z.mod_1_r; lia|].
change (2 ^ 3) with 8. split; [lia|]. split; [|lia].
rewrite HF8. replace (2147450880 + 8 * (F / 64)) with ((268431360 + F / 64) * 8) by lia. apply Z_mod_mult.
Qed.
(* The frame: [F, F + fs_frame_bytes cid), writable, the flag address at F + fs_frame_bytes cid - 8. *)
Lemma cw_frame_region_ok : frame_flag_lawP tfibsegs B -> forall E (n nf : nat) ly S (W : world tfibsegs) mem md cid pos,
AR tfibsegs B ly S W mem md -> In (cid, pos) (frames S) ->
ew E n = Z_to_bv 64 (frame_addr ly cid pos) -> ew E nf = Z_to_bv 64 (flag_addr ly cid pos) ->
rdword (aview tfibsegs (w_H W) mem) (frame_addr ly cid pos + fs_frame_bytes cid - 8) = Some (flag_addr ly cid pos) ->
region_ok tfibsegs E (mrestrict (w_H W) mem) (cw_frame_region n nf cid).
Proof.
intros FFL E n nf ly S W mem md cid pos HAR Hin En Enf Hfl.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (frames_bounds tfibsegs B LAWS ly S W mem md cid pos HAR Hin) as (H4096 & Hceil & _).
destruct (frame_al64 tfibsegs B ly S W mem md cid pos HAR Hin) as (_ & _ & Hb64).
destruct (al_frames _ _ LAWS ly S W mem md cid pos HAR Hin) as (_ & _ & Hfb & _).
destruct (FFL ly S W mem md cid pos HAR Hin) as (_ & _ & _ & (Hfl0 & _ & Hflc)).
unfold region_ok, cw_frame_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite En, unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split.
- intros o Ho. apply (apresent_writable tfibsegs). exact (proj1 (Hfb (frame_addr ly cid pos + o) ltac:(lia))).
- apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val tfibsegs E _ (frame_addr ly cid pos) (fs_frame_bytes cid - 8) 8 (SOff nf 0) (flag_addr ly cid pos)).
  + cbn [sv_denot]. rewrite Enf, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  + change (8 * Z.of_N 8) with 64. lia.
  + cbn. lia.
  + replace (frame_addr ly cid pos + (fs_frame_bytes cid - 8)) with (frame_addr ly cid pos + fs_frame_bytes cid - 8) by lia.
    exact (val_mem_of_rdword tfibsegs _ _ _ _ Hfl).
Qed.
(* The frame's shadow: [shadow_addr F, + fs_frame_bytes cid / 8), writable, zero after the request. *)
Lemma cw_fshadow_region_ok : forall E (s : nat) ly S (W : world tfibsegs) mem md cid pos,
AR tfibsegs B ly S W mem md -> In (cid, pos) (frames S) ->
ew E s = Z_to_bv 64 (shadow_addr (frame_addr ly cid pos)) ->
zero_shadow (aview tfibsegs (w_H W) mem) SHADOW_OFF (frame_addr ly cid pos) (fs_frame_bytes cid) ->
region_ok tfibsegs E (mrestrict (w_H W) mem) (cw_fshadow_region s cid).
Proof.
intros E s ly S W mem md cid pos HAR Hin Es Hz.
unfold region_ok, cw_fshadow_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (frames_bounds tfibsegs B LAWS ly S W mem md cid pos HAR Hin) as (H4096 & Hceil & _).
destruct (frame_al64 tfibsegs B ly S W mem md cid pos HAR Hin) as (_ & Hbm & Hb64).
destruct (al_frames _ _ LAWS ly S W mem md cid pos HAR Hin) as (_ & _ & _ & Hsb).
set (F := frame_addr ly cid pos) in *. set (bs := fs_frame_bytes cid) in *.
assert (Hb8 : bs / 8 = 8 * (bs / 64)).
{ rewrite (Z.div_mod bs 64) at 1 by lia. rewrite Hbm, Z.add_0_r.
  replace (64 * (bs / 64)) with ((8 * (bs / 64)) * 8) by lia. apply Z.div_mul. lia. }
assert (Hb8u : bs / 8 <= bs) by (apply Z.div_le_upper_bound; lia).
assert (HF0 : 0 <= F / 8) by (apply Z.div_pos; lia).
assert (HF8b : F / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia).
assert (Hb640 : 0 <= bs / 64) by (apply Z.div_pos; lia).
assert (HS0 : 0 <= shadow_addr F) by (unfold shadow_addr, SHADOW_OFF; lia).
assert (HS1 : shadow_addr F + bs / 8 <= 2 ^ 64) by (unfold shadow_addr, SHADOW_OFF; lia).
rewrite Es, unsigned_lit_small by (unfold shadow_addr, SHADOW_OFF in *; lia).
split; [lia|]. split; [lia|]. split.
- intros o Ho. apply (apresent_writable tfibsegs). exact (proj1 (Hsb o ltac:(lia))).
- apply Forall_forall. intros c Hc. unfold cw_zero_chunks in Hc. apply in_map_iff in Hc as (j & <- & Hj).
  apply in_seq in Hj. assert (Hj' : 0 <= Z.of_nat j < bs / 64) by lia.
  apply (chunk_ok_val tfibsegs E _ (shadow_addr F) (8 * Z.of_nat j) 8 (SLit 0) 0).
  + reflexivity.
  + change (8 * Z.of_N 8) with 64. lia.
  + cbn. lia.
  + apply val_mem_zero8. intros i Hi.
    replace (shadow_addr F + 8 * Z.of_nat j + i) with (shadow_of_addr SHADOW_OFF F + (8 * Z.of_nat j + i))
      by (unfold shadow_of_addr, shadow_addr; lia).
    apply Hz. lia.
Qed.
(* The flag byte: [FL, FL + 1), writable (the release's flag clear). *)
Lemma cw_flag_region_ok : frame_flag_lawP tfibsegs B -> forall E (nf : nat) ly S (W : world tfibsegs) mem md cid pos,
AR tfibsegs B ly S W mem md -> In (cid, pos) (frames S) ->
ew E nf = Z_to_bv 64 (flag_addr ly cid pos) ->
region_ok tfibsegs E (mrestrict (w_H W) mem) (cw_flag_region nf).
Proof.
intros FFL E nf ly S W mem md cid pos HAR Hin Enf.
destruct (FFL ly S W mem md cid pos HAR Hin) as (Hp & _ & _ & (Hfl0 & _ & Hflc)).
pose proof asan_consts as (C1 & _).
unfold region_ok, cw_flag_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite Enf, unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
intros o Ho. apply (apresent_writable tfibsegs). replace (flag_addr ly cid pos + o) with (flag_addr ly cid pos) by lia. exact Hp.
Qed.
End f.
(* The flag byte is the runtime's own (frame_flag_lawP), so it lies outside every extent of bytes that are not:
   the frame, its shadow, a heap block, the machine stack (all_disjoint of the flag region). *)
Lemma cw_flag_apart : forall B ly S FL lo hi, aowned B ly S FL -> (forall a, lo <= a < hi -> ~ aowned B ly S a) ->
hi <= FL \/ FL + 1 <= lo.
Proof.
intros B ly S FL lo hi Ho Hn. destruct (Z_lt_le_dec FL lo) as [H1|H1]; [right; lia|].
destruct (Z_lt_le_dec FL hi) as [H2|H2]; [exfalso; exact (Hn FL ltac:(lia) Ho) | left; lia].
Qed.
(* Write windows inside the frame or inside its shadow are the walk's own frame's (in_frames). *)
Lemma cw_awr_ok_cons_frame : forall E r rs STK sp0 FP bl0 blc ly own cid pos m,
YP09.r_base r = Some m -> bv_unsigned (ew E m) = frame_addr ly cid pos -> In (cid, pos) own ->
0 <= YP09.r_wlo r -> YP09.r_whi r <= fs_frame_bytes cid ->
awr_ok E rs STK sp0 FP bl0 blc ly own -> awr_ok E (r :: rs) STK sp0 FP bl0 blc ly own.
Proof.
intros E r rs STK sp0 FP bl0 blc ly own cid pos m Hb Hm Hin Hlo Hhi H a (r' & [<- | Hr] & Ha).
- rewrite Hb in Ha. cbn [base_val] in Ha. rewrite Hm in Ha.
  right; right; right. exists cid, pos. split; [exact Hin|]. left. unfold in_zr. cbn [fst snd]. lia.
- apply H. exists r'. split; [exact Hr | exact Ha].
Qed.
Lemma cw_awr_ok_cons_fshadow : forall E r rs STK sp0 FP bl0 blc ly own cid pos m,
YP09.r_base r = Some m -> bv_unsigned (ew E m) = shadow_addr (frame_addr ly cid pos) -> In (cid, pos) own ->
0 <= YP09.r_wlo r -> YP09.r_whi r <= fs_frame_bytes cid / 8 ->
awr_ok E rs STK sp0 FP bl0 blc ly own -> awr_ok E (r :: rs) STK sp0 FP bl0 blc ly own.
Proof.
intros E r rs STK sp0 FP bl0 blc ly own cid pos m Hb Hm Hin Hlo Hhi H a (r' & [<- | Hr] & Ha).
- rewrite Hb in Ha. cbn [base_val] in Ha. rewrite Hm in Ha.
  right; right; right. exists cid, pos. split; [exact Hin|]. right. unfold in_zr. cbn [fst snd]. lia.
- apply H. exists r'. split; [exact Hr | exact Ha].
Qed.
(* The write premise of the release run (aj_run_flag / aj_run_flag_sh): the flag region in front, based at the atom
   holding FL with its window inside [0, 1), and the rest of the state's windows the walk's to write. *)
Lemma cw_awrf_flag_front : forall E r rs STK sp0 FP bl0 blc ly own (nf : nat) FL,
YP09.r_base r = Some nf -> bv_unsigned (ew E nf) = FL -> 0 <= YP09.r_wlo r -> YP09.r_whi r <= 1 ->
awr_ok E rs STK sp0 FP bl0 blc ly own ->
forall a, in_wrange E (r :: rs) a -> awr_byte STK sp0 FP bl0 blc ly own a \/ a = FL.
Proof.
intros E r rs STK sp0 FP bl0 blc ly own nf FL Hb Hv Hlo Hhi H a (r' & [<- | Hr] & Ha).
- right. rewrite Hb in Ha. cbn [base_val] in Ha. rewrite Hv in Ha. lia.
- left. apply H. exists r'. split; [exact Hr | exact Ha].
Qed.
(* A runtime call's kept fact over a stack [slo, shi) inside the walk's window [sp - T, sp), with the window present
   after the call, is the tcj_kept of the window. *)
Lemma cw_tcj_of_acall : forall B T lyc Sc (W : world tfibsegs) memc W2 mem2 sp slo shi (E : Z -> Prop),
sp - T <= slo -> shi <= sp ->
acall_kept tfibsegs B lyc Sc W memc W2 mem2 slo shi E ->
(forall a, sp - T <= a < sp -> apresent (w_H W2) mem2 a) ->
tcj_kept tfibsegs B T lyc Sc W memc W2 mem2 sp E.
Proof.
intros B T lyc Sc W memc W2 mem2 sp slo shi E Hlo Hhi (A1 & A2 & A3 & A4 & A5 & _) Hw.
split; [intros a Ha Hn _; apply A1; [exact Ha | intros H; apply Hn; lia]|].
split; [exact A2|]. split; [exact A3|]. split; [exact A4|].
split; [intros a Ha Hn Hp; apply A5; [exact Ha | intros H; apply Hn; lia | exact Hp]|].
exact Hw.
Qed.

(* ================================ the leaf after the release ================================ *)
(* The frames of the state at the leaf are the call state's: both journals extend the same caller journal by the
   same own frames. *)
Lemma cw_frames_back : forall segs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world segs) memc mdc k ly3 S3 W3 mem3 md3 k3,
ajournal segs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
ajournal segs B STK sp0 FP ly S W0 mem0 md0 own ly3 S3 W3 mem3 md3 k3 ->
frames S3 = frames Sc.
Proof.
intros segs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ly3 S3 W3 mem3 md3 k3
(_ & _ & _ & _ & _ & Hf1 & _) (_ & _ & _ & _ & _ & Hf3 & _). rewrite Hf1, Hf3. reflexivity.
Qed.
Lemma cw_perm_release : forall B ly3 S3 lyc Sc cid pos,
Permutation (ablocks B ly3 S3) (ablocks B lyc Sc) ->
Permutation (ablocks B ly3 (stack_free_state cid pos S3)) (ablocks B lyc Sc).
Proof. intros B ly3 S3 lyc Sc cid pos H. unfold ablocks in *. rewrite blocks_stack_free_state. exact H. Qed.
Lemma cw_mo_le_release : forall MT, ameter_fs_laws MT -> forall Sc S3 cid pos m,
mo_le MT Sc S3 m -> mo_le MT Sc (stack_free_state cid pos S3) m.
Proof. intros MT MTF Sc S3 cid pos m H. unfold stack_free_state. apply (mo_le_set_fs_r MT MTF). exact H. Qed.
(* What the walk carries from the request (S2 = set_fs f Sc) ... *)
Lemma cw_frame_start : forall MT, ameter_laws MT -> ameter_fs_laws MT -> forall B lyc Sc S2,
(exists f, S2 = set_fs f Sc) -> Permutation (ablocks B lyc S2) (ablocks B lyc Sc) /\ mo_le MT Sc S2 0.
Proof.
intros MT MTL MTF B lyc Sc S2 (f & ->).
assert (E : blocks (set_fs f Sc) = blocks Sc) by reflexivity.
split; [unfold ablocks; rewrite E; apply Permutation_refl|].
apply (mo_le_set_fs_r MT MTF). apply (mo_le_refl MT MTL).
Qed.
(* ... and through a call of an own callee whose cdc_post took (ly1, S2) to (ly2, S3). *)
Lemma cw_frame_step : forall MT, ameter_laws MT -> forall B lyc Sc ly1 S2 ly2 S3,
Permutation (ablocks B ly1 S2) (ablocks B lyc Sc) -> mo_le MT Sc S2 0 ->
Permutation (ablocks B ly2 S3) (ablocks B ly1 S2) -> mo_le MT S2 S3 0 ->
Permutation (ablocks B ly2 S3) (ablocks B lyc Sc) /\ mo_le MT Sc S3 0.
Proof.
intros MT MTL B lyc Sc ly1 S2 ly2 S3 P1 M1 P2 M2.
split; [eapply Permutation_trans; [exact P2 | exact P1]|].
exact (mo_le_trans MT MTL _ _ _ 0 0 M1 M2).
Qed.
(* The three clauses together: the journal at the call (HJ0), the journal after the release (state
   stack_free_state cid pos S3), the blocks permutation and the meter the walk carried to S3. *)
Lemma cw_release_post : forall MT, ameter_fs_laws MT ->
forall segs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world segs) memc mdc k ly3 S3 W3 mem3 md3 k3 cid pos,
ajournal segs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
ajournal segs B STK sp0 FP ly S W0 mem0 md0 own ly3 (stack_free_state cid pos S3) W3 mem3 md3 k3 ->
Permutation (ablocks B ly3 S3) (ablocks B lyc Sc) -> mo_le MT Sc S3 0 ->
frames (stack_free_state cid pos S3) = frames Sc /\
Permutation (ablocks B ly3 (stack_free_state cid pos S3)) (ablocks B lyc Sc) /\
mo_le MT Sc (stack_free_state cid pos S3) 0.
Proof.
intros MT MTF segs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ly3 S3 W3 mem3 md3 k3 cid pos HJ0 HJ HP HM.
split; [exact (cw_frames_back segs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ly3 _ W3 mem3 md3 k3 HJ0 HJ)|].
split; [exact (cw_perm_release B ly3 S3 lyc Sc cid pos HP) | exact (cw_mo_le_release MT MTF Sc S3 cid pos 0 HM)].
Qed.

(* ================================ a source range on the caller's machine stack ================================
   [x, x + n) inside the caller's stack allowance below sp0 (an __asan_memcpy source): the stack's shadow is zero in
   every state (AR_zshadow_law's first range), ly_stk_lo / ly_stk_hi are page-aligned (lo_top), so the shadow hull of
   the range is inside the stack's shadow; the bytes are present (the journal's stack presence). *)
Lemma cw_stack_src : forall B STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world tfibsegs) memc mdc k x n,
AR_laws tfibsegs B -> ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
sp0 - STK <= x -> x + n < sp0 -> 0 < n ->
amem_range x n /\ range_addressable (aview tfibsegs (w_H W) memc) SHADOW_OFF x n /\
shadow_hull_vis (aview tfibsegs (w_H W) memc) x n /\
(forall a, x <= a < x + n -> aview tfibsegs (w_H W) memc a <> None).
Proof.
intros B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k x n LAWS HJ Hx0 Hx1 Hn.
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Eslo & Eshi & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (al_zshadow _ _ LAWS lyc Sc W memc mdc _ HAR (or_introl eq_refl)) as Hz. cbn [fst snd] in Hz.
pose proof HAR as (M & _). pose proof (lo_top _ (am_layout _ _ _ _ M)) as (_ & _ & _ & _ & Tlo & Thi & _).
unfold page_aligned in Tlo, Thi. rewrite Eslo in Tlo, Hz. rewrite Eshi in Thi, Hz.
clear HJ Hly Hstk M HAR.
set (lo := ly_stk_lo ly) in *. set (hi := ly_stk_hi ly) in *.
assert (Dlo : lo = 4096 * (lo / 4096)) by (pose proof (Z.div_mod lo 4096 ltac:(lia)); lia).
assert (Dhi : hi = 4096 * (hi / 4096)) by (pose proof (Z.div_mod hi 4096 ltac:(lia)); lia).
assert (L8 : lo / 8 = 512 * (lo / 4096)).
{ transitivity (((512 * (lo / 4096)) * 8) / 8); [f_equal; lia | apply Z.div_mul; lia]. }
assert (E8 : (hi - lo) / 8 = 512 * (hi / 4096 - lo / 4096)).
{ transitivity (((512 * (hi / 4096 - lo / 4096)) * 8) / 8); [f_equal; lia | apply Z.div_mul; lia]. }
assert (ESO : SHADOW_OFF = 8 * 268431360) by reflexivity.
assert (Hlx : lo <= x) by (clear - Hx0 Hslo; lia).
assert (Hxh : x + n < hi) by (clear - Hx1 Hshi; lia).
split.
{ unfold amem_range. right. rewrite C3, C4. clear - Hlx Hxh H47 Hceil C1. lia. }
split.
{ intros y Hy. exists 0. split; [|left; reflexivity].
  assert (Y1 : 512 * (lo / 4096) <= y / 8) by (apply Z.div_le_lower_bound; [lia | clear - Dlo Hlx Hy; lia]).
  assert (Y2 : y / 8 < 512 * (hi / 4096)) by (apply Z.div_lt_upper_bound; [lia | clear - Dhi Hxh Hy; lia]).
  assert (Hi : 0 <= y / 8 - lo / 8 < (hi - lo) / 8) by (clear - Y1 Y2 L8 E8; lia).
  pose proof (Hz _ Hi) as H0. unfold shadow_of_addr in H0 |- *.
  replace (SHADOW_OFF + lo / 8 + (y / 8 - lo / 8)) with (SHADOW_OFF + y / 8) in H0 by ring. exact H0. }
split.
{ intros s Hs. unfold shadow_addr in Hs.
  assert (X1 : 512 * (lo / 4096) <= x / 8) by (apply Z.div_le_lower_bound; [lia | clear - Dlo Hlx; lia]).
  assert (X2 : (x + n - 1) / 8 < 512 * (hi / 4096)) by (apply Z.div_lt_upper_bound; [lia | clear - Dhi Hxh; lia]).
  assert (Q1 : 268431360 + 64 * (lo / 4096) <= (SHADOW_OFF + x / 8) / 8)
    by (apply Z.div_le_lower_bound; [lia | clear - X1 ESO; lia]).
  assert (Q2 : (SHADOW_OFF + (x + n - 1) / 8) / 8 < 268431360 + 64 * (hi / 4096))
    by (apply Z.div_lt_upper_bound; [lia | clear - X2 ESO; lia]).
  assert (Hi : 0 <= s - SHADOW_OFF - lo / 8 < (hi - lo) / 8) by (clear - Hs Q1 Q2 L8 E8 ESO; lia).
  pose proof (Hz _ Hi) as H0. unfold shadow_of_addr in H0.
  replace (SHADOW_OFF + lo / 8 + (s - SHADOW_OFF - lo / 8)) with s in H0 by ring. rewrite H0. discriminate. }
intros a Ha. apply (aview_some_of_apresent tfibsegs). apply Hpres. clear - Ha Hx0 Hx1. lia.
Qed.
End b.

(* same_io mdc md at a leaf: through the runs' materializations (cw_same_io_wvb) and the same_io facts of the calls
   in context, back to mdc. *)
Ltac cw_io :=
let rec kio := first [ apply same_io_refl | assumption
  | eapply same_io_trans; [| apply cw_same_io_wvb]; kio
  | eapply same_io_trans; [| eassumption]; kio ] in kio.
(* cdc_post's frames / blocks / model / meter clauses at the state (ly3, stack_free_state cid pos S3) of the journal
   HJ after the release: frames from the call's entry journal in context (cw_frames_back), blocks and meter from
   P3 : Permutation (ablocks B ly3 S3) (ablocks B lyc Sc), M3 : mo_le MT Sc S3 0 and MTF : ameter_fs_laws MT in
   context. Leaves the memory clause /\ the result. *)
Ltac cw_frame_clauses HJ :=
split; [eapply cw_frames_back; [| exact HJ]; eassumption|];
split; [apply cw_perm_release; assumption|];
split; [cw_io|];
split; [lazymatch goal with MTF : ameter_fs_laws _ |- _ => apply (cw_mo_le_release _ MTF); assumption end|].
(* The `ret` leaf of a frame-owning walk after the release: cw_leaf with the state of the latest journal
   (ly3, stack_free_state cid pos S3) and cw_frame_clauses. ktac proves the memory clause (tcj_kept; the carried kept
   invariant: ltac:(idtac; exact KK)), rtac the result. *)
Ltac cw_frame_leaf ktac rtac :=
lazymatch goal with
| HS : st_ok _ ?E _ (restrict (w_H ?W) ?ms),
  HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ ?ly3 (stack_free_state ?cid ?pos ?S3) _ _ _ _ |- _ =>
let R1 := fresh "R1" in rreg HS (1%bv : bv 5) R1;
let R10 := fresh "R10" in cw_r10 R10;
eapply (SRr_ret_at tfibsegs tfibtbl_lib tfibtbl_lib_ok Hwx_tfa W E); [exact HS | reflexivity | vm_compute; reflexivity |];
let mat' := fresh "mat" in intros mat';
red; exists ly3, (stack_free_state cid pos S3), (ms_regs ms), (ms_mem ms); eexists;
split; [lazymatch goal with E1 : ew _ 1 = _, Hra : YK0s.ret_ok _ |- _ => rewrite R1, E1, Hra; reflexivity end|];
split; [unfold EV_CDC; rewrite Z.add_0_r; eapply ajournal_materialize; eassumption|];
split; [eapply aregs_preserved_of_st_ok;
  [exact HS | lazymatch goal with HAE : env_agree 32 _ _ |- _ => env_agree_chain HAE end | vm_compute; reflexivity]|];
cw_frame_clauses HJ;
split; [ktac | rtac]
end.

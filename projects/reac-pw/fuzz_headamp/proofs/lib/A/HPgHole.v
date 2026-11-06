(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YCbq.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-10: off_img's image bounds cite fuzz_knock's image (YImgTop.IMG_LO, YImgTop.IMG_TOP = 0x5f3000, both knock ASan builds) in place of cgif's 0x10000 and 0x5fb000. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_knock/lib/Reusable/YCbq.v at origin/ossv/recipes 6ebe35ba632 (fuzz_knock's released ASan tree); module paths changed to reac-pw/fuzz_headamp. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/Reusable/YCbq.v, with its module paths and module names changed; 986 of its 1333 lines of code are new or changed and 2813 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: the journal lemmas rdp_aj_write_U, rdp_ecall_preU_k and rdp_aj_roU of
   proofs/omx-clap-core/fuzz_manifest/lib/A/FMW_rd_pre_k.v (lines 494-584 at origin/ossv/recipes 09c6822d886), the
   frame law ARU_frame of lib/A/FMupoison.v (lines 166-187) and the post rt_post_roU of lib/A/FMH_Rt.v (lines 97-104)
   of the same tree, restated for a hole in the shadow of a real-stack frame in place of fuzz_manifest's user-poisoned
   heap granules; the chunk runners SRr_chain_tok_AJ / SRr_run_tok_AJ / SRr_run_to_tok_AJ / SRr_chain_AJ /
   SRr_run_AJ / SRr_run_to_AJ of lib/Reusable/YCbq.v (lines 2408-2546) restated with the journal over the unpoisoned
   memory. The rest is new. *)
(* reac-pw/fuzz_headamp: THE FRAME HOLE of reac_headamp_prop_parse_result. Proves no function (kind: segment lemma).

   WHY. The parse (image A 0x845b4, image B 0x849ac) takes `addi sp,sp,-0x100; andi sp,sp,-0x20` and keeps one ASan
   stack object, the strtol end pointer, in its own REAL-stack frame: with sp' its sp after the `andi`, the 64 bytes
   [sp' + 0x40, sp' + 0x80) are the frame object (a 32-byte left redzone, the 8-byte end pointer at sp' + 0x60, a
   24-byte right redzone), and the parse writes their eight shadow bytes itself (measured on the pinned images,
   capstone over the unstripped twins):
     open   A 0x84648 .. 0x84668, B 0x84a40 .. 0x84a60: bytes 4..7 := f8 f3 f3 f3, then bytes 0..3 := f1 f1 f1 f1;
     dot    A 0x849f8, B 0x84dc8: byte 4 := 00 (the end pointer in scope, just before the strtol call);
            A 0x84aec / 0x84b2c, B 0x84ec0 / 0x84f08: byte 4 := f8 (out of scope again);
     close  A 0x84744 .. 0x84760, B 0x84b44 .. 0x84b60: bytes 4..7, 0..3 := 00, before the one `ret`
            (A 0x847a8, B 0x84ba8); every return path of the parse passes A 0x84738 / B 0x84b38.
   The kit's AR asks every shadow byte of the stack range to read 0 (YG0n.v am_zshadow, zero_shadow_ranges), and the
   journal (YCbq.v ajournal) asks AR at EVERY state of a walk, so between the open and the close neither AR nor
   ajournal holds of the parse's memory.

   THE FORM. As fuzz_manifest holds AR across its user-poison window (FMupoison.v ARU, FMW_rd_pre_k.v), the walk holds
   AR of the memory read with the hole's shadow bytes as 0: unpoison (hU fr pat) mem (FMupoison.v in_ush / unpoison,
   ported unchanged as lib/A/Rt/FMupoison.v), with
     hU fr pat     = [(fr, 8 |pat|)]: the hole, the shadow bytes of [fr, fr + 8 |pat|);
     hstack_ok     : fr granule-aligned, the frame inside the stack range [ly_stk_lo, ly_stk_hi), pat bytes;
     hpat          : the hole's shadow bytes, read through the view, are pat;
     ARH           = AR at unpoison (hU fr pat) mem /\ hstack_ok /\ hpat     (the state form);
     hjournal      = ajournal at unpoison (hU fr pat) memc /\ hstack_ok /\ hpat (the cut-state form).
   For the parse: fr = sp' + 0x40, |pat| = 8, and pat is PAT_KEY = f1 f1 f1 f1 f8 f3 f3 f3 (after the open, at the
   strncmp call) or PAT_DOT = f1 f1 f1 f1 00 f3 f3 f3 (after A 0x849f8 / B 0x84dc8, at the strtol call and the three
   strcmp calls); PAT_ZERO before the open's stores land and after the close's.

   THE INTERFACE (for the parse walks; HOLE-INTERFACE.md says the same):
   - hj_enter (from a plain journal at the parse's own entry, hole bytes still 0) gives hjournal ... PAT_ZERO;
     the open's eight stores then run inside a chunk (aj_run_tokH / SRr_run_tok_AJH: the write set may hold the
     hole's shadow bytes, awr_okH), after which the walk re-reads hpat from its symbolic store (hj_repat_raw /
     hj_repat for a pattern change made outside a chunk).
   - every cut between the open and the close carries hjournal STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
     fr pat, with fr = sp' + 0x40 and the pattern that holds there;
   - the three wrapper calls inside the hole: hj_strncmp_at (pattern any, the parse has PAT_KEY), hj_strtol_at
     (needs the end pointer's shadow byte 0: PAT_DOT, hd_dot_ok), hj_strcmp_at (pattern any, the parse has PAT_DOT);
     each takes its wrapper's contract in hole form at the trampoline pc as an argument:
       hd_astrncmp_hole pc        (reac-pw/fuzz_pin lib/A/PPgWrap.v astrncmp_realizes in hole form),
       hd_astrtol_hole pc gotw guard (plugin-hostd/fuzz_command lib/A/Rt/RtNumber.v astrtol_realizes in hole form),
       hd_astrcmp_hole pc         (libreac/fuzz_identity lib/Reusable/AStrcmpDef.v astrcmp_realizes in hole form);
   - hj_leave (all eight hole bytes 0 again, after the close's stores) gives the plain journal back, before the `ret`
     where hd_post's journal clause is discharged.
   Image A's numbers are at the end of this file; image B's twin is lib/AU/HPgHole.v, which shares every definition
   and lemma of this file. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI04.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YG0q YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YM05 YI16.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI08 YN3v YI00 YI0m YI09 YC5d YG05 YO09.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A.Rt Require Import FMupoison.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ======================================== the patterns ======================================== *)
Definition PAT_ZERO : list Z := [0; 0; 0; 0; 0; 0; 0; 0].
Definition PAT_KEY : list Z := [0xf1; 0xf1; 0xf1; 0xf1; 0xf8; 0xf3; 0xf3; 0xf3].
Definition PAT_DOT : list Z := [0xf1; 0xf1; 0xf1; 0xf1; 0x00; 0xf3; 0xf3; 0xf3].
(* The frame object's base from the parse's sp after `andi sp,sp,-0x20`, and the end pointer's cell. *)
Definition hd_fr (spa : Z) : Z := spa + 0x40.
Definition hd_dot (spa : Z) : Z := spa + 0x60.

Section h. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.

(* ======================================== the definitions ======================================== *)
Definition hU (fr : Z) (pat : list Z) : list (Z * Z) := [(fr, 8 * Z.of_nat (length pat))].

Definition hstack_ok (ly : alayout) (fr : Z) (pat : list Z) : Prop :=
fr mod 8 = 0 /\ (0 < length pat)%nat /\ ly_stk_lo ly <= fr /\ fr + 8 * Z.of_nat (length pat) <= ly_stk_hi ly /\
Forall (fun v => 0 <= v < 256) pat.

Definition hpat (W : world segs) (mem : word -> option byte) (fr : Z) (pat : list Z) : Prop :=
forall i, 0 <= i < Z.of_nat (length pat) ->
aview segs (w_H W) mem (shadow_addr fr + i) = Some (nth (Z.to_nat i) pat 0).

Definition ARH (ly : alayout) (S : astate) (fr : Z) (pat : list Z) (W : world segs) (mem : word -> option byte)
(md : Model) : Prop :=
AR segs B ly S W (unpoison (hU fr pat) mem) md /\ hstack_ok ly fr pat /\ hpat W mem fr pat.

Definition hjournal (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
(lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (mdc : Model) (k : Z)
(fr : Z) (pat : list Z) : Prop :=
ajournal segs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (unpoison (hU fr pat) memc) mdc k /\
hstack_ok lyc fr pat /\ hpat W memc fr pat.

(* The premise of a runtime call made inside the hole: ecall_pre (YG0d.v) of the unpoisoned memory, the hole's place
   and pattern, and STK bytes of present stack below sp in the real memory (fuzz_manifest's ecall_preU_k,
   FMH_Base.v:162-165, with the hole in place of the user-poisoned granules). *)
Definition ecall_preH (STK : Z) (ly : alayout) (S : astate) (fr : Z) (pat : list Z) (W : world segs)
(regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop :=
ecall_pre segs B ly S W regs (unpoison (hU fr pat) mem) md /\ hstack_ok ly fr pat /\ hpat W mem fr pat /\
ly_stk_lo ly + STK <= spZ regs /\ (forall a, spZ regs - STK <= a < spZ regs -> apresent (w_H W) mem a).

(* ======================================== the hole's bytes ======================================== *)
Lemma in_hU : forall fr pat s,
in_ush (hU fr pat) s = true <-> shadow_addr fr <= s < shadow_addr fr + Z.of_nat (length pat).
Proof.
intros fr pat s. unfold in_ush, hU. cbn [existsb fst snd]. rewrite Bool.orb_false_r.
rewrite Z.mul_comm, Z.div_mul by lia. split; intros H.
- apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
- apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.

Lemma in_hU_false : forall fr pat s,
~ (shadow_addr fr <= s < shadow_addr fr + Z.of_nat (length pat)) -> in_ush (hU fr pat) s = false.
Proof.
intros fr pat s H. destruct (in_ush (hU fr pat) s) eqn:E; [|reflexivity]. exfalso. apply H. apply in_hU. exact E.
Qed.

Lemma hU_len : forall fr pat pat', length pat' = length pat -> hU fr pat' = hU fr pat.
Proof. intros fr pat pat' E. unfold hU. rewrite E. reflexivity. Qed.

Lemma hw64 : forall a, 0 <= a < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 a) = a.
Proof. intros a Ha. apply unsigned_lit_small. exact Ha. Qed.

(* The hole lies in the high shadow band, below the stack range and above the image. *)
Lemma hole_band : forall ly fr pat, layout_ok ly -> hstack_ok ly fr pat ->
forall s, shadow_addr fr <= s < shadow_addr fr + Z.of_nat (length pat) ->
kHighShadowBeg <= s < kHighShadowEnd /\ s < ly_stk_lo ly /\ kLowMemEnd <= s /\ in_band_rw s /\ 0 <= s < 2 ^ 64.
Proof.
intros ly fr pat LO (H8 & HL & Hlo & Hhi & _) s Hs.
pose proof (lo_top ly LO) as (_ & _ & _ & T4 & _ & _ & T7).
apply Z.mod_divide in H8 as [q Hq]; [|lia]. subst fr.
unfold shadow_addr in Hs. rewrite Z.div_mul in Hs by lia.
unfold in_band_rw, kHighShadowBeg, kHighShadowEnd, kLowShadowBeg, kLowShadowEnd, kLowMemEnd, SHADOW_OFF,
  kHighMemBeg, kHighMemEnd in *.
lia.
Qed.

Lemma hole_not_img : forall ly fr pat, layout_ok ly -> hstack_ok ly fr pat ->
forall s, shadow_addr fr <= s < shadow_addr fr + Z.of_nat (length pat) -> ~ in_img segs s.
Proof.
intros ly fr pat LO OK s Hs Hi. pose proof (segs_low s Hi) as L.
pose proof (hole_band ly fr pat LO OK s Hs) as (_ & _ & L2 & _). lia.
Qed.

(* A byte that reads 0 through the view, outside the image, is a visible 0 byte of the memory. *)
Lemma raw_of_aview0 : forall H (mem : word -> option byte) s, 0 <= s < 2 ^ 64 -> ~ in_img segs s ->
aview segs H mem s = Some 0 -> H (Z_to_bv 64 s) = false /\ mem (Z_to_bv 64 s) = Some (Z_to_bv 8 0).
Proof.
intros H mem s Hs Hn E. unfold aview, mbyte, mrestrict in E.
destruct (H (Z_to_bv 64 s)) eqn:EH.
- rewrite (seg_rom_none segs s Hs Hn) in E. discriminate E.
- destruct (mem (Z_to_bv 64 s)) as [b|] eqn:EM.
  + split; [reflexivity|]. cbn in E. injection E as E. f_equal. apply bv_eq. rewrite E. reflexivity.
  + rewrite (seg_rom_none segs s Hs Hn) in E. discriminate E.
Qed.

(* Under AR, every byte of a hole inside the stack range is a visible 0 (am_zshadow over the stack range). *)
Lemma hole_raw_zero : forall ly S W mem md fr pat, AR segs B ly S W mem md -> hstack_ok ly fr pat ->
forall x : word, in_ush (hU fr pat) (bv_unsigned x) = true -> w_H W x = false /\ mem x = Some (Z_to_bv 8 0).
Proof.
intros ly S W mem md fr pat HAR OK x Hx. apply in_hU in Hx.
pose proof (AR_laws_ok segs B) as LAWS.
pose proof (am_layout B ly S _ (proj1 HAR)) as LO.
pose proof (lo_top ly LO) as (_ & _ & _ & T4 & T5 & _ & T7).
pose proof (hole_band ly fr pat LO OK _ Hx) as (_ & _ & _ & _ & Hr).
pose proof (hole_not_img ly fr pat LO OK _ Hx) as Hn.
pose proof (al_zshadow _ _ LAWS ly S W mem md (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly) HAR
  ltac:(left; reflexivity)) as ZS.
cbn [fst snd] in ZS. destruct OK as (H8 & HL & Hlo & Hhi & _).
unfold page_aligned in T5.
set (s := bv_unsigned x) in *.
assert (E0 : aview segs (w_H W) mem s = Some 0).
{ apply Z.mod_divide in H8 as [q Hq]; [|lia]. apply Z.mod_divide in T5 as [p Hp]; [|lia].
  unfold shadow_addr in Hx. rewrite Hq, Z.div_mul in Hx by lia.
  assert (Hi : 0 <= s - SHADOW_OFF - 512 * p < (ly_stk_hi ly - ly_stk_lo ly) / 8).
  { split; [lia|]. enough (s - SHADOW_OFF - 512 * p + 1 <= (ly_stk_hi ly - ly_stk_lo ly) / 8) by lia.
    apply Z.div_le_lower_bound; lia. }
  pose proof (ZS _ Hi) as Z1. unfold shadow_of_addr in Z1. rewrite Hp in Z1.
  replace (p * 4096) with ((512 * p) * 8) in Z1 by lia. rewrite Z.div_mul in Z1 by lia.
  replace (SHADOW_OFF + 512 * p + (s - SHADOW_OFF - 512 * p)) with s in Z1 by lia. exact Z1. }
destruct (raw_of_aview0 (w_H W) mem s Hr Hn E0) as [EH EM].
subst s. rewrite Z_to_bv_bv_unsigned in EH, EM. split; [exact EH | exact EM].
Qed.

Lemma unpoison_agree : forall U (m1 m2 : word -> option byte),
(forall x, in_ush U (bv_unsigned x) = false -> m1 x = m2 x) -> unpoison U m1 = unpoison U m2.
Proof.
intros U m1 m2 H. apply functional_extensionality. intros x. unfold unpoison.
destruct (in_ush U (bv_unsigned x)) eqn:E; [reflexivity | exact (H x E)].
Qed.

(* Under AR, unpoisoning a hole inside the stack range changes nothing. *)
Lemma unpoison_zero : forall ly S W mem md fr pat, AR segs B ly S W mem md -> hstack_ok ly fr pat ->
unpoison (hU fr pat) mem = mem.
Proof.
intros ly S W mem md fr pat HAR OK. apply functional_extensionality. intros x. unfold unpoison.
destruct (in_ush (hU fr pat) (bv_unsigned x)) eqn:E; [|reflexivity].
symmetry. exact (proj2 (hole_raw_zero ly S W mem md fr pat HAR OK x E)).
Qed.

(* A memory whose hole bytes are visible zeros is its own unpoisoned memory. *)
Lemma unpoison_of_zero_pat : forall ly fr pat (W : world segs) (mem : word -> option byte), layout_ok ly ->
hstack_ok ly fr pat -> Forall (fun v => v = 0) pat -> hpat W mem fr pat -> unpoison (hU fr pat) mem = mem.
Proof.
intros ly fr pat W mem LO OK HZ HP. apply functional_extensionality. intros x. unfold unpoison.
destruct (in_ush (hU fr pat) (bv_unsigned x)) eqn:E; [|reflexivity].
apply in_hU in E. set (s := bv_unsigned x) in *.
pose proof (hole_band ly fr pat LO OK _ E) as (_ & _ & _ & _ & Hr).
pose proof (hole_not_img ly fr pat LO OK _ E) as Hn.
assert (E0 : aview segs (w_H W) mem s = Some 0).
{ replace s with (shadow_addr fr + (s - shadow_addr fr)) by lia. rewrite (HP (s - shadow_addr fr) ltac:(lia)).
  f_equal. rewrite Forall_forall in HZ. apply HZ. apply nth_In. lia. }
destruct (raw_of_aview0 (w_H W) mem s Hr Hn E0) as [_ EM].
subst s. rewrite Z_to_bv_bv_unsigned in EM. symmetry. exact EM.
Qed.

Lemma hstack_ok_repat : forall ly fr pat pat', hstack_ok ly fr pat -> length pat' = length pat ->
Forall (fun v => 0 <= v < 256) pat' -> hstack_ok ly fr pat'.
Proof. intros ly fr pat pat' (H1 & H2 & H3 & H4 & _) E HB. rewrite <- E in H2, H4. repeat split; assumption. Qed.

(* ======================================== the state form ======================================== *)
Lemma ARH_AR : forall ly S fr pat W mem md, ARH ly S fr pat W mem md -> AR segs B ly S W (unpoison (hU fr pat) mem) md.
Proof. intros ly S fr pat W mem md (H & _ & _). exact H. Qed.

(* Opening the hole: from AR with the hole's bytes still 0, a memory that differs only on the hole and reads pat
   there is ARH. *)
Lemma ARH_open : forall ly S W mem md fr pat mem1,
AR segs B ly S W mem md -> hstack_ok ly fr pat ->
(forall x, in_ush (hU fr pat) (bv_unsigned x) = false -> mem1 x = mem x) -> hpat W mem1 fr pat ->
ARH ly S fr pat W mem1 md.
Proof.
intros ly S W mem md fr pat mem1 HAR OK HA HP.
assert (E : unpoison (hU fr pat) mem1 = mem).
{ transitivity (unpoison (hU fr pat) mem); [apply unpoison_agree; exact HA|].
  exact (unpoison_zero ly S W mem md fr pat HAR OK). }
split; [rewrite E; exact HAR|]. split; [exact OK | exact HP].
Qed.

(* Closing the hole: with every hole byte 0 again, ARH is AR. *)
Lemma ARH_close : forall ly S fr pat W mem md, ARH ly S fr pat W mem md -> Forall (fun v => v = 0) pat ->
AR segs B ly S W mem md.
Proof.
intros ly S fr pat W mem md (HAR & OK & HP) HZ.
pose proof (am_layout B ly S _ (proj1 HAR)) as LO.
rewrite (unpoison_of_zero_pat ly fr pat W mem LO OK HZ HP) in HAR. exact HAR.
Qed.

(* A pattern change: a memory that differs only on the hole. *)
Lemma ARH_repat : forall ly S fr pat pat' W mem md mem',
ARH ly S fr pat W mem md ->
(forall x, in_ush (hU fr pat) (bv_unsigned x) = false -> mem' x = mem x) ->
length pat' = length pat -> Forall (fun v => 0 <= v < 256) pat' -> hpat W mem' fr pat' ->
ARH ly S fr pat' W mem' md.
Proof.
intros ly S fr pat pat' W mem md mem' (HAR & OK & _) HA HL HB HP.
unfold ARH. rewrite (hU_len fr pat pat' HL). split; [|split; [exact (hstack_ok_repat ly fr pat pat' OK HL HB) | exact HP]].
rewrite (unpoison_agree (hU fr pat) mem' mem HA). exact HAR.
Qed.

(* The frame law (FMupoison.v ARU_frame for the hole): a step that keeps every owned byte outside the hole, every
   visible byte visible, the model's mappings and the hidden band bytes, and leaves the pattern in place. *)
Lemma ARH_frame : forall ly S fr pat W mem md mem' md',
ARH ly S fr pat W mem md ->
(forall a, 0 <= a < 2 ^ 64 -> aowned B ly S a -> in_ush (hU fr pat) a = false ->
 aview segs (w_H W) mem' a = aview segs (w_H W) mem a) ->
(forall a, aview segs (w_H W) mem a <> None -> aview segs (w_H W) mem' a <> None) ->
m_vmmaps md' = m_vmmaps md -> m_vm_lazy md' = m_vm_lazy md -> eager_used md' = eager_used md ->
(forall a, in_band_rw a -> w_H W (w64 a) = true -> mem' (w64 a) = mem (w64 a)) ->
hpat W mem' fr pat ->
ARH ly S fr pat W mem' md'.
Proof.
intros ly S fr pat W mem md mem' md' (HAR & OK & _) HOWN HVIS E1 E2 E3 HB HP.
pose proof (AR_laws_ok segs B) as LAWS.
split; [|split; [exact OK | exact HP]].
apply (al_frame _ _ LAWS ly S W (unpoison (hU fr pat) mem) md (unpoison (hU fr pat) mem') md' HAR);
  [| |exact E1|exact E2|exact E3|].
- intros a Ha Hown. destruct (in_ush (hU fr pat) (bv_unsigned (Z_to_bv 64 a))) eqn:Ei.
  + apply aview_unpoison_in. exact Ei.
  + rewrite !aview_unpoison_out by exact Ei. rewrite (hw64 a Ha) in Ei. exact (HOWN a Ha Hown Ei).
- intros a Hv. destruct (in_ush (hU fr pat) (bv_unsigned (Z_to_bv 64 a))) eqn:Ei.
  + rewrite (aview_unpoison_in segs _ (hU fr pat) mem' mem a Ei). exact Hv.
  + rewrite aview_unpoison_out in Hv |- * by exact Ei. exact (HVIS a Hv).
- intros a Hb Hh. unfold unpoison. destruct (in_ush (hU fr pat) (bv_unsigned (w64 a))); [reflexivity | exact (HB a Hb Hh)].
Qed.

(* ======================================== the cut-state form ======================================== *)
Lemma hj_AR : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k fr pat,
hjournal STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k fr pat ->
ARH lyc Sc fr pat W memc mdc.
Proof. intros until pat. intros (HJ & OK & HP). split; [exact (proj1 HJ)|]. split; [exact OK | exact HP]. Qed.

(* The entry step: the plain journal of a walk at a state whose hole bytes are still 0 (the parse's entry) holds of
   the unpoisoned memory of any memory that differs from it only on the hole; with the pattern read there. *)
Lemma hj_enter : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k fr pat memc1,
ajournal segs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
hstack_ok lyc fr pat ->
(forall x, in_ush (hU fr pat) (bv_unsigned x) = false -> memc1 x = memc x) ->
hpat W memc1 fr pat ->
hjournal STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc1 mdc k fr pat.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k fr pat memc1 HJ OK HA HP.
assert (E : unpoison (hU fr pat) memc1 = memc).
{ transitivity (unpoison (hU fr pat) memc); [apply unpoison_agree; exact HA|].
  exact (unpoison_zero lyc Sc W memc mdc fr pat (proj1 HJ) OK). }
split; [rewrite E; exact HJ|]. split; [exact OK | exact HP].
Qed.

(* The entry step at an unchanged memory: the pattern is all 0. *)
Lemma hpat_zero_of_AR : forall ly S W mem md fr pat, AR segs B ly S W mem md -> hstack_ok ly fr pat ->
Forall (fun v => v = 0) pat -> hpat W mem fr pat.
Proof.
intros ly S W mem md fr pat HAR OK HZ i Hi.
pose proof (am_layout B ly S _ (proj1 HAR)) as LO.
assert (Hs : shadow_addr fr <= shadow_addr fr + i < shadow_addr fr + Z.of_nat (length pat)) by lia.
pose proof (hole_band ly fr pat LO OK _ Hs) as (_ & _ & _ & _ & Hr).
assert (Hx : in_ush (hU fr pat) (bv_unsigned (Z_to_bv 64 (shadow_addr fr + i))) = true)
  by (rewrite (hw64 _ Hr); apply in_hU; exact Hs).
destruct (hole_raw_zero ly S W mem md fr pat HAR OK _ Hx) as [EH EM].
unfold aview, mbyte, mrestrict. rewrite EH, EM. cbn.
rewrite Forall_forall in HZ. rewrite (HZ (nth (Z.to_nat i) pat 0)) by (apply nth_In; lia). reflexivity.
Qed.

Lemma hj_enter0 : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k fr,
ajournal segs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
hstack_ok lyc fr PAT_ZERO ->
hjournal STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k fr PAT_ZERO.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k fr HJ OK.
apply (hj_enter STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k fr PAT_ZERO memc HJ OK); [intros; reflexivity|].
apply (hpat_zero_of_AR lyc Sc W memc mdc fr PAT_ZERO (proj1 HJ) OK). repeat constructor.
Qed.

(* The exit step: every hole byte 0 again, the plain journal of the memory itself. *)
Lemma hj_leave : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k fr pat,
hjournal STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k fr pat ->
Forall (fun v => v = 0) pat ->
ajournal segs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k fr pat (HJ & OK & HP) HZ.
pose proof (am_layout B lyc Sc _ (proj1 (proj1 HJ))) as LO.
rewrite (unpoison_of_zero_pat lyc fr pat W memc LO OK HZ HP) in HJ. exact HJ.
Qed.

(* A pattern change outside a chunk: a memory that differs only on the hole. *)
Lemma hj_repat : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k fr pat pat' memc',
hjournal STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k fr pat ->
(forall x, in_ush (hU fr pat) (bv_unsigned x) = false -> memc' x = memc x) ->
length pat' = length pat -> Forall (fun v => 0 <= v < 256) pat' -> hpat W memc' fr pat' ->
hjournal STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc' mdc k fr pat'.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k fr pat pat' memc' (HJ & OK & _) HA HL HB HP.
unfold hjournal. rewrite (hU_len fr pat pat' HL), (unpoison_agree (hU fr pat) memc' memc HA).
split; [exact HJ|]. split; [exact (hstack_ok_repat lyc fr pat pat' OK HL HB) | exact HP].
Qed.

(* The pattern is a fact of the real memory alone: a new pattern read at the same journal (after a chunk whose
   continuation already has the journal over the unpoisoned memory). *)
Lemma hj_repat_raw : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k fr pat pat',
ajournal segs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (unpoison (hU fr pat) memc) mdc k ->
hstack_ok lyc fr pat -> length pat' = length pat -> Forall (fun v => 0 <= v < 256) pat' -> hpat W memc fr pat' ->
hjournal STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k fr pat'.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k fr pat pat' HJ OK HL HB HP.
unfold hjournal. rewrite (hU_len fr pat pat' HL).
split; [exact HJ|]. split; [exact (hstack_ok_repat lyc fr pat pat' OK HL HB) | exact HP].
Qed.

(* ======================================== the journal lemmas (fuzz_manifest FMW_rd_pre_k.v) ======================================== *)
Lemma hp_apresent_unp : forall H U m a, in_ush U (bv_unsigned (Z_to_bv 64 a)) = false ->
(apresent H (unpoison U m) a <-> apresent H m a).
Proof. intros H U m a E. unfold apresent. rewrite (unpoison_out U m _ E). tauto. Qed.

(* A stack byte is never a hole byte. *)
Lemma hole_free_stack : forall ly fr pat a, layout_ok ly -> hstack_ok ly fr pat -> ly_stk_lo ly <= a < 2 ^ 64 ->
in_ush (hU fr pat) (bv_unsigned (Z_to_bv 64 a)) = false.
Proof.
intros ly fr pat a LO OK Ha. pose proof (lo_top ly LO) as (_ & _ & _ & _ & _ & _ & T7).
apply in_hU_false. rewrite (hw64 a) by (unfold kHighMemBeg in T7; lia).
intros Hs. pose proof (hole_band ly fr pat LO OK _ Hs) as (_ & L & _). lia.
Qed.

(* rdp_aj_write_U (FMW_rd_pre_k.v:494-522) for any U: a write inside the hole's lifetime, the journal over the
   unpoisoned memory. *)
Lemma hj_aj_write_U : forall STK sp0 FP ly S W mem md own lyc Sc Wc U memc mdc k memc' mdc' (Wr : Z -> Prop),
ajournal segs B STK sp0 FP ly S W mem md own lyc Sc Wc (unpoison U memc) mdc k ->
(forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> aview segs (w_H Wc) memc' a = aview segs (w_H Wc) memc a) ->
(forall a, apresent (w_H Wc) memc a -> apresent (w_H Wc) memc' a) ->
same_but_materialized mdc mdc' ->
(forall a, Wr a -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a) ->
AR segs B lyc Sc Wc (unpoison U memc') mdc' ->
ajournal segs B STK sp0 FP ly S W mem md own lyc Sc Wc (unpoison U memc') mdc' k.
Proof.
intros STK sp0 FP ly S W mem md own lyc Sc Wc U memc mdc k memc' mdc' Wr HJ Heq Hpr Hsame HW HAR'.
pose proof (AR_laws_ok segs B) as LAWS.
pose proof HJ as (_ & _ & _ & _ & _ & Hfrs & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HQT).
eapply (ajournal_after_write segs B LAWS segs_low STK sp0 FP ly S W mem md own lyc Sc Wc (unpoison U memc) mdc k
  (unpoison U memc') mdc' Wr Sc own HJ).
- intros a Ha HWa. destruct (in_ush U (bv_unsigned (Z_to_bv 64 a))) eqn:E.
  + apply aview_unpoison_in. exact E.
  + rewrite !aview_unpoison_out by exact E. exact (Heq a Ha HWa).
- intros a Hp. destruct (in_ush U (bv_unsigned (Z_to_bv 64 a))) eqn:E.
  + destruct Hp as [Hh _]. split; [exact Hh|]. exists (Z_to_bv 8 0). apply unpoison_in. exact E.
  + apply (hp_apresent_unp _ U memc' a E). apply Hpr. apply (hp_apresent_unp _ U memc a E). exact Hp.
- exact Hsame.
- intros a Ha. left. exact (HW a Ha).
- exact HAR'.
- reflexivity.
- reflexivity.
- lia.
- exact Hfrs.
- exact HQT.
Qed.

(* rdp_ecall_preU_k (FMW_rd_pre_k.v:525-547) for the hole: the premise of a runtime call made inside the hole, at
   sp = sp0 + o of the walk's journal with STKr bytes of the callee inside the journal's window. *)
Lemma hj_ecall_pre : forall STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k fr pat regsc (o : Z) STKr,
hjournal STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k fr pat ->
spZ regsc = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK <= STKr -> STKr - o <= STK ->
YK0s.ret_ok (getr regsc 1) -> getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
ecall_preH STKr lyc Sc fr pat W regsc memc mdc.
Proof.
intros STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k fr pat regsc o STKr (HJ & OK & HP) Hsp Hal Hneg Hes Hbud
  Hra Hgp Htp.
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstatic & _).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
pose proof (am_layout B lyc Sc _ (proj1 HAR)) as LO.
assert (ESTACK = 4096) as HE4 by reflexivity.
split; [exact (ecall_pre_at segs B STK sp0 FP ly S W0 mem md own lyc Sc W _ mdc k regsc o HJ Hsp Hal Hneg
  ltac:(lia) Hra Hgp Htp)|].
split; [exact OK|]. split; [exact HP|].
split; [rewrite Eslo, Hsp; lia|].
intros a Ha. rewrite Hsp in Ha.
apply (proj1 (hp_apresent_unp _ (hU fr pat) memc a (hole_free_stack lyc fr pat a LO OK ltac:(rewrite Eslo; lia)))).
apply Hpres. lia.
Qed.

End h.

(* ======================================== the three wrapper contracts in hole form ========================================
   Each is its released text, word for word with the text's own definitions unfolded, with two changes only: the
   premise ecall_pre (with the contract's stack window) is ecall_preH (ecall_pre of unpoison (hU fr pat) mem, the hole's
   place and pattern, the window present in mem), and the post's AR of mem' is AR of unpoison (hU fr pat) mem' with
   hpat W mem' fr pat (the pattern kept), for every hole (fr, pat). Every other premise is stated over the real memory
   mem, as in the released text: the wrapper's walk reads the real memory, and at the strtol call the end pointer's
   shadow byte is a hole byte that must read 0 there (hd_dot_ok below). fuzz_manifest's astrstr_realizes and
   asnprintf_realizes (FMH_Rt.v:160-202, with FMupoison.v ecall_preU and FMH_Rt.v rt_post_roU) are the same change for
   its heap user-poison window. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require StrFun.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog Require __intscan_c.
Module PIS := OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.__intscan_c.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.

(* reac-pw/fuzz_pin lib/A/PPgWrap.v:121-133 astrncmp_realizes (awrap_str :82-93, awrap_post :98-106,
   aro_unowned of libreac/fuzz_identity lib/A/Rt/WrapRo.v:24-26 unfolded, as lib/A/HPgCallsStr.v's STRNCMP states it),
   in hole form. *)
Definition hd_astrncmp_hole (pc : Z) : Prop :=
forall ly S W regs mem md x y n (ls rs : list byte) (d : Z) (fr : Z) (pat : list Z),
ecall_preH segs B (2 * ESTACK) ly S fr pat W regs mem md ->
getr regs 10 = w64 x -> getr regs 11 = w64 y -> getr regs 12 = w64 n ->
0 <= n < 2 ^ 32 ->
(0 < x /\ ~ In (Z_to_bv 8 0) ls /\
 Z.of_nat (length ls) + 1 < 2 ^ 32 /\ x + Z.of_nat (length ls) + 1 <= 2 ^ 63 /\
 garr8 segs (mrestrict (w_H W) mem) x (map (fun b : byte => bv_unsigned b) ls ++ [0]) /\
 src_ok segs W regs mem x (Z.of_nat (length ls) + 1) /\
 (forall a, x <= a <= x + Z.of_nat (length ls) -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs)) /\
 amem_range x (Z.of_nat (length ls) + 1) /\
 range_addressable (aview segs (w_H W) mem) SHADOW_OFF x (Z.of_nat (length ls) + 1) /\
 shadow_hull_vis (aview segs (w_H W) mem) x (Z.of_nat (length ls) + 1) /\
 (forall a, x + Z.of_nat (length ls) < a < x + Z.of_nat (length ls) - (x + Z.of_nat (length ls)) mod 8 + 8 ->
  aview segs (w_H W) mem a <> None)) ->
(0 < y /\ ~ In (Z_to_bv 8 0) rs /\
 Z.of_nat (length rs) + 1 < 2 ^ 32 /\ y + Z.of_nat (length rs) + 1 <= 2 ^ 63 /\
 garr8 segs (mrestrict (w_H W) mem) y (map (fun b : byte => bv_unsigned b) rs ++ [0]) /\
 src_ok segs W regs mem y (Z.of_nat (length rs) + 1) /\
 (forall a, y <= a <= y + Z.of_nat (length rs) -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs)) /\
 amem_range y (Z.of_nat (length rs) + 1) /\
 range_addressable (aview segs (w_H W) mem) SHADOW_OFF y (Z.of_nat (length rs) + 1) /\
 shadow_hull_vis (aview segs (w_H W) mem) y (Z.of_nat (length rs) + 1) /\
 (forall a, y + Z.of_nat (length rs) < a < y + Z.of_nat (length rs) - (y + Z.of_nat (length rs)) mod 8 + 8 ->
  aview segs (w_H W) mem a <> None)) ->
amem_range x (Z.of_nat (length ls) + 8) -> amem_range y (Z.of_nat (length rs) + 8) ->
StrFun.strncmp_model (ls ++ [Z_to_bv 8 0]) (rs ++ [Z_to_bv 8 0]) n = Some d ->
(forall a, in_rom segs a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
 aview segs (w_H W) mem a = option_map (fun b : byte => bv_unsigned b) (seg_rom segs (Z_to_bv 64 a))) ->
SRr segs W (cfg_at segs pc regs mem md)
(fun (W' : world segs) (c' : config) => W' = W /\ exists regs' mem' md',
 c' = cfg_at segs (raZ regs) regs' mem' md' /\
 AR segs B ly S W (unpoison (hU fr pat) mem') md' /\ hpat segs W mem' fr pat /\
 aregs_preserved regs regs' /\ same_but_materialized md md' /\
 (exists v : word, getr regs' 10 = v /\ (v = w64 0 <-> d = 0)) /\
 (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs) ->
  aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
 (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).

(* plugin-hostd/fuzz_command lib/A/Rt/RtNumber.v:81-111 astrtol_realizes at origin/ossv/recipes 09c6822d886 (the same
   text at 2d2ff01bb6f), with RtDefs.v's ecall_pre_stk, aread_ok, awrite_ok, astr_at, atail_vis, aguard_ok, art_post,
   aerrno_cell and rt_rom_view (lines 25-147) unfolded; s10_val / s10_end / s10_errno are headamp's copy of
   fuzz_command's plain model, lib/Prog/__intscan_c.v (fuzz_command's lib/Prog/__intscan_c.v with module paths and
   the plain image's __intscan address changed). In hole form. *)
Definition hd_astrtol_hole (pc gotw guard : Z) : Prop :=
forall ly S W regs mem md x e (str : list byte) ev (fr : Z) (pat : list Z),
(rdword (aview segs (w_H W) mem) gotw = Some guard /\ (exists can, rdword (aview segs (w_H W) mem) guard = Some can)) ->
ecall_preH segs B (3 * ESTACK) ly S fr pat W regs mem md ->
getr regs 10 = w64 x -> getr regs 11 = w64 e -> getr regs 12 = w64 10 -> 0 < x -> 0 < e ->
((forall i, (i < length (str ++ [Z_to_bv 8 0]))%nat ->
  aview segs (w_H W) mem (x + Z.of_nat i) = Some (bv_unsigned (nth i (str ++ [Z_to_bv 8 0]) (Z_to_bv 8 0)))) /\
 ~ In (Z_to_bv 8 0) str) ->
x + Z.of_nat (length str) + 1 < 2 ^ 64 ->
(0 <= x /\ x + (Z.of_nat (length str) + 1) <= 2 ^ 63 /\ 0 <= Z.of_nat (length str) + 1 < 2 ^ 32 /\
 (forall a, x <= a < x + (Z.of_nat (length str) + 1) ->
  aview segs (w_H W) mem a <> None /\ ~ (spZ regs - 3 * ESTACK <= a < spZ regs)) /\
 amem_range x (Z.of_nat (length str) + 1) /\
 range_addressable (aview segs (w_H W) mem) SHADOW_OFF x (Z.of_nat (length str) + 1) /\
 (0 < Z.of_nat (length str) + 1 -> shadow_hull_vis (aview segs (w_H W) mem) x (Z.of_nat (length str) + 1))) ->
amem_range x (Z.of_nat (length str) + 8) ->
(forall a, x + Z.of_nat (length str) < a < x + Z.of_nat (length str) - (x + Z.of_nat (length str)) mod 8 + 8 ->
 aview segs (w_H W) mem a <> None) ->
(0 <= e /\ e + 8 <= 2 ^ 63 /\ 0 <= 8 < 2 ^ 32 /\
 (forall a, e <= a < e + 8 ->
  writable_at segs (mrestrict (w_H W) mem) a /\ ~ aowned B ly S a /\ ~ (spZ regs - 3 * ESTACK <= a < spZ regs)) /\
 amem_range e 8 /\
 range_addressable (aview segs (w_H W) mem) SHADOW_OFF e 8 /\
 (0 < 8 -> shadow_hull_vis (aview segs (w_H W) mem) e 8)) ->
amem_range e 16 ->
(e + 8 <= x \/ x + Z.of_nat (length str) + 1 <= e) ->
(e + 8 <= as_errno B \/ as_errno B + 4 <= e) ->
e mod 8 = 0 ->
(forall a, e <= a < e + 8 -> ~ in_zr a (ly_img ly)) ->
(as_errno B + 4 <= x \/ x + Z.of_nat (length str) + 1 <= as_errno B) ->
rd32 (aview segs (w_H W) mem) (as_errno B) ev ->
(forall a, in_rom segs a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
 aview segs (w_H W) mem a = option_map (fun b : byte => bv_unsigned b) (seg_rom segs (Z_to_bv 64 a))) ->
SRr segs W (cfg_at segs pc regs mem md)
(fun (W' : world segs) (c' : config) => W' = W /\ exists regs' mem' md',
 c' = cfg_at segs (raZ regs) regs' mem' md' /\
 AR segs B ly S W (unpoison (hU fr pat) mem') md' /\ hpat segs W mem' fr pat /\
 aregs_preserved regs regs' /\ same_but_materialized md md' /\
 (getr regs' 10 = w64 (PIS.s10_val str) /\
  rdword (aview segs (w_H W) mem') e = Some (x + PIS.s10_end str) /\
  rd32 (aview segs (w_H W) mem') (as_errno B) (bv_unsigned (PIS.s10_errno str (Z_to_bv 64 ev)))) /\
 (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 3 * ESTACK <= a < spZ regs) ->
  ~ ((e <= a < e + 8) \/ (as_errno B <= a < as_errno B + 4)) ->
  aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
 (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a) /\
 (forall a, spZ regs - 3 * ESTACK <= a < spZ regs -> apresent (w_H W) mem' a)).

(* libreac/fuzz_identity lib/Reusable/AStrcmpDef.v:44-64 astrcmp_realizes at origin/ossv/recipes 09c6822d886, with
   str_meet (:37-42) and strcmp_res (:34) unfolded, in hole form. *)
Definition hd_astrcmp_hole (pc : Z) : Prop :=
forall ly S W regs mem md x y k c1 c2 (fr : Z) (pat : list Z),
ecall_preH segs B (2 * ESTACK) ly S fr pat W regs mem md ->
getr regs 10 = w64 x -> getr regs 11 = w64 y -> 0 < x -> 0 < y ->
k + 1 < 2 ^ 32 -> x + k + 1 <= 2 ^ 63 -> y + k + 1 <= 2 ^ 63 ->
(0 <= k /\
 (forall i, 0 <= i < k -> exists b, aview segs (w_H W) mem (x + i) = Some b /\
                                    aview segs (w_H W) mem (y + i) = Some b /\ b <> 0) /\
 aview segs (w_H W) mem (x + k) = Some c1 /\ aview segs (w_H W) mem (y + k) = Some c2 /\
 (c1 <> c2 \/ c1 = 0)) ->
src_ok segs W regs mem x (k + 1) -> src_ok segs W regs mem y (k + 1) ->
(forall a, x <= a <= x + k -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs)) ->
(forall a, y <= a <= y + k -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs)) ->
amem_range x (k + 1) -> amem_range y (k + 1) ->
range_addressable (aview segs (w_H W) mem) SHADOW_OFF x (k + 1) -> shadow_hull_vis (aview segs (w_H W) mem) x (k + 1) ->
range_addressable (aview segs (w_H W) mem) SHADOW_OFF y (k + 1) -> shadow_hull_vis (aview segs (w_H W) mem) y (k + 1) ->
SRr segs W (cfg_at segs pc regs mem md)
(fun (W' : world segs) (c' : config) => W' = W /\ exists regs' mem' md',
 c' = cfg_at segs (raZ regs) regs' mem' md' /\
 AR segs B ly S W (unpoison (hU fr pat) mem') md' /\ hpat segs W mem' fr pat /\
 aregs_preserved regs regs' /\ same_but_materialized md md' /\
 getr regs' 10 = w64 (if c1 =? c2 then 0 else if c1 <? c2 then -1 else 1) /\
 (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs) ->
  aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
 (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).

(* ======================================== the calls inside the hole ========================================
   lib/A/HPgCallsStr.v hc_strncmp_at (the call inside a caller's journal) with the journal in hole form:
   fuzz_manifest's rdp_aj_roU (FMW_rd_pre_k.v:550-584). The pattern is the caller's and is kept. *)
Lemma hj_strncmp_at : forall pc, hd_astrncmp_hole pc ->
forall W (regsT : bvmap 5 word) memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x y n (ls rs : list byte) (d o : Z) raw
  fr pat,
hjournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k fr pat ->
getr regsT 10 = w64 x -> getr regsT 11 = w64 y -> getr regsT 12 = w64 n -> 0 <= n < 2 ^ 32 ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 2 * ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
(0 < x /\ ~ In (Z_to_bv 8 0) ls /\
 Z.of_nat (length ls) + 1 < 2 ^ 32 /\ x + Z.of_nat (length ls) + 1 <= 2 ^ 63 /\
 garr8 segs (mrestrict (w_H W) memT) x (map (fun b : byte => bv_unsigned b) ls ++ [0]) /\
 src_ok segs W regsT memT x (Z.of_nat (length ls) + 1) /\
 (forall a, x <= a <= x + Z.of_nat (length ls) -> ~ (spZ regsT - 2 * ESTACK <= a < spZ regsT)) /\
 amem_range x (Z.of_nat (length ls) + 1) /\
 range_addressable (aview segs (w_H W) memT) SHADOW_OFF x (Z.of_nat (length ls) + 1) /\
 shadow_hull_vis (aview segs (w_H W) memT) x (Z.of_nat (length ls) + 1) /\
 (forall a, x + Z.of_nat (length ls) < a < x + Z.of_nat (length ls) - (x + Z.of_nat (length ls)) mod 8 + 8 ->
  aview segs (w_H W) memT a <> None)) ->
(0 < y /\ ~ In (Z_to_bv 8 0) rs /\
 Z.of_nat (length rs) + 1 < 2 ^ 32 /\ y + Z.of_nat (length rs) + 1 <= 2 ^ 63 /\
 garr8 segs (mrestrict (w_H W) memT) y (map (fun b : byte => bv_unsigned b) rs ++ [0]) /\
 src_ok segs W regsT memT y (Z.of_nat (length rs) + 1) /\
 (forall a, y <= a <= y + Z.of_nat (length rs) -> ~ (spZ regsT - 2 * ESTACK <= a < spZ regsT)) /\
 amem_range y (Z.of_nat (length rs) + 1) /\
 range_addressable (aview segs (w_H W) memT) SHADOW_OFF y (Z.of_nat (length rs) + 1) /\
 shadow_hull_vis (aview segs (w_H W) memT) y (Z.of_nat (length rs) + 1) /\
 (forall a, y + Z.of_nat (length rs) < a < y + Z.of_nat (length rs) - (y + Z.of_nat (length rs)) mod 8 + 8 ->
  aview segs (w_H W) memT a <> None)) ->
amem_range x (Z.of_nat (length ls) + 8) -> amem_range y (Z.of_nat (length rs) + 8) ->
StrFun.strncmp_model (ls ++ [Z_to_bv 8 0]) (rs ++ [Z_to_bv 8 0]) n = Some d ->
(forall a, in_rom segs a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
 aview segs (w_H W) memT a = option_map (fun b : byte => bv_unsigned b) (seg_rom segs (Z_to_bv 64 a))) ->
SRr segs W (cfg_at segs pc regsT memT mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
 c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
 hjournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k fr pat /\
 aregs_preserved regsT regs2 /\ same_io mdc md2 /\
 (exists v : word, getr regs2 10 = v /\ (v = w64 0 <-> d = 0)) /\
 (forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o) ->
  aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
 (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof.
intros pc HC W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x y n ls rs d o raw fr pat
  HJ Ha0 Ha1 Ha2 Hn Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hx Hy Hmx Hmy Hmd Hro.
pose proof HJ as (HJ0 & OK & _).
assert (ESTACK = 4096) as Hes by reflexivity.
assert (HPRE : ecall_preH segs B (2 * ESTACK) lyc Sc fr pat W regsT memT mdc).
{ apply (hj_ecall_pre segs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k fr pat regsT o (2 * ESTACK) HJ Hsp'
    Hal Hneg); [lia | lia | rewrite Hra; exact Hraw | exact Hgp | exact Htp]. }
eapply SRr_mono.
{ exact (HC lyc Sc W regsT memT mdc x y n ls rs d fr pat HPRE Ha0 Ha1 Ha2 Hn Hx Hy Hmx Hmy Hmd Hro). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP2 & HPr & Hsame & Hres & Hfr & Hpres2).
rewrite Hsp' in Hfr.
split; [reflexivity|]. exists regs2, mem2, md2.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ split; [|split; [exact OK | exact HP2]].
  apply (hj_aj_write_U segs B segs_low STK sp0 FP ly S W0 mem md own lyc Sc W (hU fr pat) memT mdc k mem2 md2
    (fun a => sp0 + o - 2 * ESTACK <= a < sp0 + o) HJ0); [exact Hfr | exact Hpres2 | exact Hsame | | exact HAR2].
  intros a Ha. left. lia. }
split; [exact HPr|]. split; [apply same_io_materialized; exact Hsame|].
split; [exact Hres|]. split; [exact Hfr | exact Hpres2].
Qed.

(* The same for the strcmp wrapper (lib/Reusable/YCbq.v aj_bcmp_at's journal threading, as HPgCallsStr's first
   donor line records for strcmp). *)
Lemma hj_strcmp_at : forall pc, hd_astrcmp_hole pc ->
forall W (regsT : bvmap 5 word) memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x y kk c1 c2 (o : Z) raw fr pat,
hjournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k fr pat ->
getr regsT 10 = w64 x -> getr regsT 11 = w64 y -> 0 < x -> 0 < y ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 2 * ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
kk + 1 < 2 ^ 32 -> x + kk + 1 <= 2 ^ 63 -> y + kk + 1 <= 2 ^ 63 ->
(0 <= kk /\
 (forall i, 0 <= i < kk -> exists b, aview segs (w_H W) memT (x + i) = Some b /\
                                     aview segs (w_H W) memT (y + i) = Some b /\ b <> 0) /\
 aview segs (w_H W) memT (x + kk) = Some c1 /\ aview segs (w_H W) memT (y + kk) = Some c2 /\
 (c1 <> c2 \/ c1 = 0)) ->
src_ok segs W regsT memT x (kk + 1) -> src_ok segs W regsT memT y (kk + 1) ->
(forall a, x <= a <= x + kk -> ~ (spZ regsT - 2 * ESTACK <= a < spZ regsT)) ->
(forall a, y <= a <= y + kk -> ~ (spZ regsT - 2 * ESTACK <= a < spZ regsT)) ->
amem_range x (kk + 1) -> amem_range y (kk + 1) ->
range_addressable (aview segs (w_H W) memT) SHADOW_OFF x (kk + 1) -> shadow_hull_vis (aview segs (w_H W) memT) x (kk + 1) ->
range_addressable (aview segs (w_H W) memT) SHADOW_OFF y (kk + 1) -> shadow_hull_vis (aview segs (w_H W) memT) y (kk + 1) ->
SRr segs W (cfg_at segs pc regsT memT mdc)
(fun W2 c2' => W2 = W /\ exists regs2 mem2 md2,
 c2' = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
 hjournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k fr pat /\
 aregs_preserved regsT regs2 /\ same_io mdc md2 /\
 getr regs2 10 = w64 (if c1 =? c2 then 0 else if c1 <? c2 then -1 else 1) /\
 (forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o) ->
  aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
 (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof.
intros pc HC W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x y kk c1 c2 o raw fr pat
  HJ Ha0 Ha1 Hx0 Hy0 Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hk1 Hxk Hyk Hmeet Hsx Hsy Hwx Hwy Hmx Hmy Hrx Hhx Hry Hhy.
pose proof HJ as (HJ0 & OK & _).
assert (ESTACK = 4096) as Hes by reflexivity.
assert (HPRE : ecall_preH segs B (2 * ESTACK) lyc Sc fr pat W regsT memT mdc).
{ apply (hj_ecall_pre segs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k fr pat regsT o (2 * ESTACK) HJ Hsp'
    Hal Hneg); [lia | lia | rewrite Hra; exact Hraw | exact Hgp | exact Htp]. }
eapply SRr_mono.
{ exact (HC lyc Sc W regsT memT mdc x y kk c1 c2 fr pat HPRE Ha0 Ha1 Hx0 Hy0 Hk1 Hxk Hyk Hmeet Hsx Hsy Hwx Hwy
    Hmx Hmy Hrx Hhx Hry Hhy). }
cbv beta. intros W2 c2' _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP2 & HPr & Hsame & Hres & Hfr & Hpres2).
rewrite Hsp' in Hfr.
split; [reflexivity|]. exists regs2, mem2, md2.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ split; [|split; [exact OK | exact HP2]].
  apply (hj_aj_write_U segs B segs_low STK sp0 FP ly S W0 mem md own lyc Sc W (hU fr pat) memT mdc k mem2 md2
    (fun a => sp0 + o - 2 * ESTACK <= a < sp0 + o) HJ0); [exact Hfr | exact Hpres2 | exact Hsame | | exact HAR2].
  intros a Ha. left. lia. }
split; [exact HPr|]. split; [apply same_io_materialized; exact Hsame|].
split; [exact Hres|]. split; [exact Hfr | exact Hpres2].
Qed.

End c.

(* ======================================== the hole at the parse: the call sites' premises and satisfiability ========================================
   At every one of the parse's five wrapper calls the parse's sp is sp' = (sp - 0x100) & -32 (no instruction between
   A 0x845f4 / B 0x849ec and the epilogue moves sp), the hole is (hd_fr sp', pat) and the callee's window is 2 ESTACK
   (strncmp, strcmp) or 3 ESTACK (strtol) below sp'. hd_site_pre gives each call's ecall_preH from the caller's hd_pre
   at the parse's entry and the walk's hjournal at the call; hd_dot_ok gives the strtol contract's two shadow facts
   of the end pointer's word [sp' + 0x60, sp' + 0x68) from the pattern PAT_DOT. hd_hole_sat_A: from the parse's own
   precondition (HPgCSpec.hd_pre at T_parse_STK) the memory after the open's eight stores (hset) satisfies the
   cut-state form at PAT_KEY: ARH holds at the parse's real entry state, and is not vacuous. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgCSpec.

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.

(* Under AR every shadow byte of the stack range reads 0 (am_zshadow). *)
Lemma stack_shadow_zero : forall ly S W mem md s, AR segs B ly S W mem md ->
shadow_addr (ly_stk_lo ly) <= s < shadow_addr (ly_stk_lo ly) + (ly_stk_hi ly - ly_stk_lo ly) / 8 ->
aview segs (w_H W) mem s = Some 0.
Proof.
intros ly S W mem md s HAR Hs.
pose proof (AR_laws_ok segs B) as LAWS.
pose proof (al_zshadow _ _ LAWS ly S W mem md (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly) HAR
  ltac:(left; reflexivity)) as ZS.
cbn [fst snd] in ZS.
pose proof (ZS (s - shadow_addr (ly_stk_lo ly)) ltac:(lia)) as Z1. unfold shadow_of_addr, shadow_addr in Z1.
unfold shadow_addr in Hs.
replace (SHADOW_OFF + ly_stk_lo ly / 8 + (s - (SHADOW_OFF + ly_stk_lo ly / 8))) with s in Z1 by lia. exact Z1.
Qed.

(* The end pointer's word at the strtol call: with the pattern PAT_DOT its granule's shadow byte is 0, and the
   aligned shadow word around it is readable (the hole's bytes and, beside them, stack shadow bytes, which AR reads
   as 0). These are the shadow parts of the strtol contract's write premise for e = fr + 32. *)
Lemma hd_dot_ok : forall ly S fr W mem md, ARH segs B ly S fr PAT_DOT W mem md ->
ly_stk_lo ly + 64 <= fr -> fr + 128 <= ly_stk_hi ly ->
range_addressable (aview segs (w_H W) mem) SHADOW_OFF (fr + 32) 8 /\
shadow_hull_vis (aview segs (w_H W) mem) (fr + 32) 8.
Proof.
intros ly S fr W mem md (HAR & OK & HP) Hlo Hhi.
pose proof (am_layout B ly S _ (proj1 HAR)) as LO.
pose proof (lo_top ly LO) as (_ & _ & _ & T4 & T5 & _ & T7). unfold page_aligned in T5.
pose proof OK as (H8 & _ & _ & _ & _).
apply Z.mod_divide in H8 as [q Hq]; [|lia]. apply Z.mod_divide in T5 as [p Hp]; [|lia].
assert (HS : shadow_addr fr = SHADOW_OFF + q) by (unfold shadow_addr; rewrite Hq, Z.div_mul by lia; reflexivity).
split.
- intros x Hx. exists 0. split; [|left; reflexivity].
  assert (Hd : x / 8 = q + 4) by (symmetry; apply Z.div_unique with (x - 8 * (q + 4)); lia).
  unfold shadow_of_addr. rewrite Hd. replace (SHADOW_OFF + (q + 4)) with (shadow_addr fr + 4) by lia.
  exact (HP 4 ltac:(cbn; lia)).
- intros s Hs.
  assert (E1 : shadow_addr (fr + 32) = SHADOW_OFF + q + 4).
  { unfold shadow_addr. rewrite Hq. replace (q * 8 + 32) with ((q + 4) * 8) by lia. rewrite Z.div_mul by lia. lia. }
  assert (E2 : shadow_addr (fr + 32 + 8 - 1) = SHADOW_OFF + q + 4).
  { unfold shadow_addr. rewrite Hq. assert (D : (q * 8 + 32 + 8 - 1) / 8 = q + 4) by (symmetry; apply Z.div_unique with 7; lia).
    rewrite D. lia. }
  rewrite E1, E2 in Hs.
  pose proof (Z.div_mod (SHADOW_OFF + q + 4) 8 ltac:(lia)) as DM.
  pose proof (Z.mod_pos_bound (SHADOW_OFF + q + 4) 8 ltac:(lia)) as MB.
  assert (Hs' : SHADOW_OFF + q - 3 <= s < SHADOW_OFF + q + 12) by lia. clear Hs DM MB.
  assert (Hr : 0 <= s < 2 ^ 64) by (unfold SHADOW_OFF in Hs'; unfold kHighMemEnd in T4; unfold kHighMemBeg in T7; lia).
  destruct (Z_lt_le_dec s (SHADOW_OFF + q)) as [L1|L1]; [|destruct (Z_lt_le_dec s (SHADOW_OFF + q + 8)) as [L2|L2]].
  2: { replace s with (shadow_addr fr + (s - shadow_addr fr)) by lia. rewrite (HP (s - shadow_addr fr) ltac:(cbn; lia)).
       discriminate. }
  all: assert (Hout : in_ush (hU fr PAT_DOT) (bv_unsigned (Z_to_bv 64 s)) = false)
         by (rewrite (hw64 s Hr); apply in_hU_false; change (Z.of_nat (length PAT_DOT)) with 8; lia).
  all: rewrite <- (aview_unpoison_out segs _ (hU fr PAT_DOT) mem s Hout).
  all: assert (Hst : shadow_addr (ly_stk_lo ly) <= s < shadow_addr (ly_stk_lo ly) + (ly_stk_hi ly - ly_stk_lo ly) / 8)
         by (unfold shadow_addr; rewrite Hp; replace (p * 4096) with ((512 * p) * 8) by lia; rewrite Z.div_mul by lia;
             split; [lia|]; enough (q + 16 - 512 * p <= (ly_stk_hi ly - (512 * p) * 8) / 8) by lia;
             apply Z.div_le_lower_bound; lia).
  all: rewrite (stack_shadow_zero ly S W _ md s HAR Hst); discriminate.
Qed.

(* The memory after the open's stores: the hole's bytes hold pat. *)
Definition hset (m : word -> option byte) (s : Z) (pat : list Z) : word -> option byte :=
fun w => if (s <=? bv_unsigned w) && (bv_unsigned w <? s + Z.of_nat (length pat))
         then Some (Z_to_bv 8 (nth (Z.to_nat (bv_unsigned w - s)) pat 0)) else m w.

(* Opening the hole at a plain journal whose state has the hole inside the stack range: the memory with the hole's
   bytes written to pat is the cut-state form. *)
Lemma hd_hole_open_sat : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k fr pat,
ajournal segs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
hstack_ok lyc fr pat ->
hjournal segs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (hset memc (shadow_addr fr) pat) mdc k fr pat.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k fr pat HJ OK.
pose proof (am_layout B lyc Sc _ (proj1 (proj1 HJ))) as LO.
apply (hj_enter segs B segs_low STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k fr pat _ HJ OK).
- intros x Hx. unfold hset.
  destruct ((shadow_addr fr <=? bv_unsigned x) && (bv_unsigned x <? shadow_addr fr + Z.of_nat (length pat))) eqn:E;
    [|reflexivity].
  exfalso. apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
  rewrite (proj2 (in_hU fr pat (bv_unsigned x)) (conj E1 E2)) in Hx. discriminate Hx.
- intros i Hi.
  assert (Hs : shadow_addr fr <= shadow_addr fr + i < shadow_addr fr + Z.of_nat (length pat)) by lia.
  pose proof (hole_band lyc fr pat LO OK _ Hs) as (_ & _ & _ & _ & Hr).
  assert (Hx : in_ush (hU fr pat) (bv_unsigned (Z_to_bv 64 (shadow_addr fr + i))) = true)
    by (rewrite (hw64 _ Hr); apply in_hU; exact Hs).
  destruct (hole_raw_zero segs B segs_low lyc Sc W memc mdc fr pat (proj1 HJ) OK _ Hx) as [EH _].
  unfold aview, mbyte, mrestrict. rewrite EH. unfold hset. rewrite (hw64 _ Hr).
  replace ((shadow_addr fr <=? shadow_addr fr + i) && (shadow_addr fr + i <? shadow_addr fr + Z.of_nat (length pat)))
    with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
  replace (shadow_addr fr + i - shadow_addr fr) with i by lia. cbn [option_map].
  pose proof OK as (_ & _ & _ & _ & HB). rewrite Forall_forall in HB.
  pose proof (HB (nth (Z.to_nat i) pat 0) ltac:(apply nth_In; lia)) as HBi.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma hd_land32 : forall x, Z.land x (-32) = 32 * (x / 32).
Proof.
intros x. change (-32) with (Z.lnot (Z.ones 5)).
rewrite <- Z.ldiff_land, Z.ldiff_ones_r, Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. change (2 ^ 5) with 32. lia.
Qed.

(* The parse's frame from its caller's hd_pre: with sp' = (sp - 0x100) & -32, the hole (hd_fr sp', 8 bytes) is inside
   the stack range with 0x40 bytes of stack below and above it, and sp' is inside the caller's journal window with
   3 ESTACK below it. *)
Lemma hd_parse_frame : forall STK sp0 FP ly S W0 mem0 md0 own k (regs : bvmap 5 word) lyc Sc W memc mdc,
hd_pre segs B STK sp0 FP ly S W0 mem0 md0 own k T_parse_STK regs lyc Sc W memc mdc ->
let spa := Z.land (spZ regs - 0x100) (-32) in
spa mod 32 = 0 /\ spZ regs - 0x120 < spa <= spZ regs - 0x100 /\ sp0 - STK + 3 * ESTACK <= spa /\ spa <= sp0 /\
ly_stk_lo lyc + 64 <= hd_fr spa /\ hd_fr spa + 128 <= ly_stk_hi lyc /\ spa mod 16 = 0 /\ sp0 mod 16 = 0.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc (HJ & _ & _ & _ & _ & Hal & Hw1 & Hw2 & _) spa.
pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstatic & _).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
pose proof (ASAN_CEIL_range) as [[C1 C2] _]. unfold ASAN_CEIL in C1.
unfold T_parse_STK, T_PARSE_FRAME, ESTACK in Hw1.
assert (Es : spa = 32 * ((spZ regs - 256) / 32)) by (unfold spa; apply hd_land32).
pose proof (Z.div_mod (spZ regs - 256) 32 ltac:(lia)) as DM.
pose proof (Z.mod_pos_bound (spZ regs - 256) 32 ltac:(lia)) as MB.
unfold hd_fr. rewrite Eslo, Eshi. unfold ESTACK.
split; [rewrite Es, Z.mul_comm; apply Z.mod_mul; lia|].
split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
split; [rewrite Es; replace (32 * ((spZ regs - 256) / 32)) with ((2 * ((spZ regs - 256) / 32)) * 16) by lia;
        apply Z.mod_mul; lia | exact Hal16].
Qed.

(* The premise of each of the parse's five wrapper calls (STKr = 2 ESTACK for strncmp and strcmp, 3 ESTACK for
   strtol), at sp = sp', from the caller's hd_pre at the parse's entry and the walk's hjournal at the call. *)
Lemma hd_site_pre : forall STK sp0 FP ly S W0 mem0 md0 own k (regs : bvmap 5 word) lyc Sc W memc mdc
  own' lyc' Sc' W' memc' mdc' k' (regsT : bvmap 5 word) STKr pat,
hd_pre segs B STK sp0 FP ly S W0 mem0 md0 own k T_parse_STK regs lyc Sc W memc mdc ->
hjournal segs B STK sp0 FP ly S W0 mem0 md0 own' lyc' Sc' W' memc' mdc' k' (hd_fr (Z.land (spZ regs - 0x100) (-32))) pat ->
spZ regsT = Z.land (spZ regs - 0x100) (-32) ->
ESTACK <= STKr <= 3 * ESTACK ->
YK0s.ret_ok (getr regsT 1) -> getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
ecall_preH segs B STKr lyc' Sc' (hd_fr (Z.land (spZ regs - 0x100) (-32))) pat W' regsT memc' mdc'.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc own' lyc' Sc' W' memc' mdc' k' regsT STKr pat
  HPRE HJ Hsp HS Hra Hgp Htp.
pose proof (hd_parse_frame STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc HPRE) as
  (F32 & F1 & F2 & F2' & F3 & F4 & F16 & S16).
set (spa := Z.land (spZ regs - 0x100) (-32)) in *.
assert (ESTACK = 4096) as Hes by reflexivity.
apply (hj_ecall_pre segs B STK sp0 FP ly S W0 mem0 md0 own' lyc' Sc' W' memc' mdc' k' (hd_fr spa) pat regsT (spa - sp0)
  STKr HJ); [lia | | lia | lia | lia | exact Hra | exact Hgp | exact Htp].
rewrite Zminus_mod, F16, S16. reflexivity.
Qed.

(* hd_hole_sat_A: ARH is satisfiable at the parse's real entry state. From the caller's hd_pre at the parse's entry
   (HPgCSpec.hd_pre at T_parse_STK, the premise of hd_parse_result_specX), the memory after the open's eight stores
   (the hole's bytes PAT_KEY, A 0x84648 .. 0x84668) satisfies the cut-state form with fr = hd_fr sp'. The statement
   holds for every segs and B: at image B (stores B 0x84a40 .. 0x84a60) lib/AU/HPgHole.v uses it as it stands. *)
Lemma hd_hole_sat_A : forall STK sp0 FP ly S W0 mem0 md0 own k (regs : bvmap 5 word) lyc Sc W memc mdc,
hd_pre segs B STK sp0 FP ly S W0 mem0 md0 own k T_parse_STK regs lyc Sc W memc mdc ->
hjournal segs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W
  (hset memc (shadow_addr (hd_fr (Z.land (spZ regs - 0x100) (-32)))) PAT_KEY) mdc k
  (hd_fr (Z.land (spZ regs - 0x100) (-32))) PAT_KEY.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc HPRE.
pose proof (hd_parse_frame STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc HPRE) as
  (F32 & F1 & F2 & F2' & F3 & F4 & F16 & S16).
set (spa := Z.land (spZ regs - 0x100) (-32)) in *.
apply hd_hole_open_sat; [exact (proj1 HPRE)|].
unfold hstack_ok, hd_fr in *. change (Z.of_nat (length PAT_KEY)) with 8.
split; [apply Z.mod_divide in F32 as [m Hm]; [|lia]; rewrite Hm;
        replace (m * 32 + 64) with ((4 * m + 8) * 8) by lia; apply Z.mod_mul; lia|].
split; [cbn; lia|]. split; [lia|]. split; [lia|].
unfold PAT_KEY. repeat apply Forall_cons; try apply Forall_nil; lia.
Qed.

(* The state form at the same point. *)
Corollary hd_ARH_sat_A : forall STK sp0 FP ly S W0 mem0 md0 own k (regs : bvmap 5 word) lyc Sc W memc mdc,
hd_pre segs B STK sp0 FP ly S W0 mem0 md0 own k T_parse_STK regs lyc Sc W memc mdc ->
ARH segs B lyc Sc (hd_fr (Z.land (spZ regs - 0x100) (-32))) PAT_KEY W
  (hset memc (shadow_addr (hd_fr (Z.land (spZ regs - 0x100) (-32)))) PAT_KEY) mdc.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc HPRE.
exact (hj_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (hd_hole_sat_A STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc HPRE)).
Qed.

End s.

(* Modified by Theorem Labs, 2026-10: proofs/plugin-hostd/fuzz_command/lib/A/Prog/numberK.v (ajournal_after_write_errno
   :33-180, aj_strtol_atS :189-268) at origin/ossv/recipes 09c6822d886, restated on this tree's kit (whose awr_byte has
   no frame-list argument; the proof is lib/Reusable/YCbq.v ajournal_after_write's, :519-637, with the errno case added
   to each frame clause) and, for the call, in hole form. *)
(* ======================================== the strtol call inside the hole ========================================
   strtol writes its stack window, the end pointer's word (a cell of the caller's own window: at the parse sp' + 0x60)
   and the errno cell, which lies in the image and which the journal's image and extra-range clauses leave out. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0p.

Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Hypothesis errno_low : api_env segs B.

Lemma ajournal_after_write_errno : forall STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k memc' mdc' (Wr : Z -> Prop) S' own2,
ajournal segs B STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k ->
(forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> aview segs (w_H Wc) memc' a = aview segs (w_H Wc) memc a) ->
(forall a, apresent (w_H Wc) memc a -> apresent (w_H Wc) memc' a) ->
same_but_materialized mdc mdc' ->
(forall a, Wr a -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a \/
 (aowned B lyc Sc a /\ app_addr a /\ ~ in_img segs a) \/ (as_errno B <= a < as_errno B + 4 /\ in_img segs a)) ->
AR segs B lyc S' Wc memc' mdc' ->
ablocks B lyc S' = ablocks B lyc Sc -> st_secs S' = st_secs Sc -> st_nev S' <= st_nev Sc -> frames S' = own2 ++ frames S ->
qtight S' ->
ajournal segs B STK sp0 FP ly S W mem md own2 lyc S' Wc memc' mdc' k.
Proof.
intros STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k memc' mdc' Wr S' own2 HJ Heqw Hgr Hsame HW HAR' Eab' Esecs' Hnev' Hfrs' HQT'.
pose proof (AR_laws_ok segs B) as LAWS.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres & Hstatic & F5 & HQT).
pose proof Hstatic as (Hal & Hstk0 & Hceil & Hlo & Hhi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HWw : forall a, Wr a ->
((~ aowned B lyc Sc a /\
((alloc_ceiling <= a /\ sp0 - STK <= a < sp0) \/
(app_addr a /\ exists b n, In (b, n) (ablocks B lyc Sc) /\ b <= a < b + req_size n /\ (inFP FP a \/ ~ In (b, n) (ablocks B ly S))) \/
(exists cid pos, In (cid, pos) own /\
((app_addr a /\ in_zr a (frame_rng lyc (cid, pos))) \/
(kLowMemEnd <= a < kHighShadowEnd /\ in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8))))))
\/ (aowned B lyc Sc a /\ app_addr a /\ ~ in_img segs a)) \/
(as_errno B <= a < as_errno B + 4 /\ in_img segs a /\ 0 <= a < kLowMemEnd)).
{ intros a Ha. destruct (HW a Ha) as [Hw | [Hx | (He1 & He2)]].
  - left; left. exact (awr_byte_cases segs B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ Hw).
  - left; right. exact Hx.
  - right. split; [exact He1|]. split; [exact He2 | exact (segs_low a He2)]. }
split; [exact HAR'|].
split; [exact Hly|]. split; [rewrite Esecs'; exact Hsecs|]. split; [exact Hwle|].
split; [eapply aos_step_same_io; [exact Hio | apply same_io_materialized, Hsame]|].
split; [exact Hfrs'|]. split; [zlia|]. split; [exact Hk|]. rewrite !Eab'. split.
{
intros a Ha Hs. rewrite <- (F1 a Ha Hs). apply Heqw; [zlia|]. intros HWa.
destruct (HWw a HWa) as [[(_ & [[_ Hs'] | [[[_ Hlow] _] | (cid & pos & _ & [[[_ Hlow] _] | [[_ Hlow] _]])]]) | (_ & Hx)] | (_ & _ & Hlo')];
  [exact (Hs Hs') | zlia | zlia | zlia | zlia | zlia]. }
split.
{
intros p n i H1 H2 Hi Hnf. rewrite <- (F2 p n i H1 H2 Hi Hnf).
destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc p n HAR H2) as (_ & H4096 & Hceilp & [Hh1 Hh2] & _ & _).
apply Heqw; [zlia|]. intros HWa.
destruct (HWw _ HWa) as [[(_ & [[Hc' _] | [(_ & b & m & Hbin & Hr & [Hfp | Hnot]) | (cid & pos & Hown & [[_ Hr] | [[Hsl Hsh] _]])]]) | (Hxo & Hx)] | (_ & Hei & _)].
- zlia.
- exact (Hnf Hfp).
-
assert (Hne : (b, m) <> (p, n)) by (intros E; rewrite E in Hnot; exact (Hnot H1)).
pose proof (sep_blocks segs B LAWS lyc Sc Wc memc mdc b m p n HAR Hbin H2 Hne) as Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd. zlia.
-
assert (Hin' : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
pose proof (sep_block_frame segs B LAWS lyc Sc Wc memc mdc p n cid pos HAR H2 Hin') as Hd.
unfold zdisjoint, in_zr, frame_rng in *. cbn [fst snd] in Hd, Hr. zlia.
- zlia.
-
exfalso. exact (proj2 (proj1 (proj2 (proj2 (proj2 (proj2 (al_blocks _ _ LAWS lyc Sc Wc memc mdc p n HAR H2))))) (p + i) ltac:(zlia)) Hxo).
- exact (blk_img segs B LAWS lyc Sc Wc memc mdc p n (p + i) HAR H2 ltac:(zlia) Hei). }
split.
{
intros a Hi Hns He Hsp. rewrite <- (F3 a Hi Hns He Hsp). pose proof (segs_low a Hi) as Hal'.
apply Heqw; [zlia|]. intros HWa.
destruct (HWw a HWa) as [[(_ & [[Hc' _] | [(_ & b & m & Hbin & Hr & _) | (cid & pos & Hown & [[_ Hr] | [[Hsl Hsh] _]])]]) | (Hxo & Hx & Hxi)] | (Her & _ & _)].
- zlia.
- exact (blk_img segs B LAWS _ _ _ _ _ _ _ _ HAR Hbin Hr Hi).
- assert (Hin' : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr. exact (frm_img segs B LAWS _ _ _ _ _ _ _ _ HAR Hin' Hr Hi).
- zlia.
- exact (Hxi Hi).
- exact (He Her). }
split.
{
intros cid pos a Hin Hr Hnf. rewrite <- (F4 cid pos a Hin Hr Hnf).
assert (HinC : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; right; exact Hin).
destruct (frames_bounds segs B LAWS lyc Sc Wc memc mdc cid pos HAR HinC) as (Hf0 & Hfc & Hfh).
assert (Efa : frame_addr lyc cid pos = frame_addr ly cid pos).
{ unfold frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
rewrite <- Efa in Hr. unfold frame_rng, in_zr in Hr. cbn [fst snd] in Hr.
pose proof (shadow_addr_bounds (frame_addr lyc cid pos) ltac:(zlia)) as Hsb1.
pose proof (shadow_addr_bounds (frame_addr lyc cid pos + fs_frame_bytes cid) ltac:(zlia)) as Hsb2.
pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) ltac:(zlia)) as Hse.
apply Heqw; [zlia|]. intros HWa.
destruct (HWw _ HWa) as [[(_ & [[Hc' _] | [([Hlo0 Hlow] & b & m & Hbin & Hrb & _) | (c' & p' & Hown & Hr')]]) | (Hxo & Hx)] | (_ & Hei & Hlw)].
- zlia.
- destruct Hr as [Hr | Hr]; [|zlia].
pose proof (sep_block_frame segs B LAWS lyc Sc Wc memc mdc b m cid pos HAR Hbin HinC) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. zlia.
-
apply in_split in Hown as (o1 & o2 & Eo). apply in_split in Hin as (g1 & g2 & Eg).
assert (Hd : zdisjoint (frame_rng lyc (c', p')) (frame_rng lyc (cid, pos))).
{ eapply (sep_frames_pos segs B LAWS lyc Sc Wc memc mdc _ _ o1 (o2 ++ g1) g2 HAR).
rewrite Hfrs, Eo, Eg. repeat (rewrite <- app_assoc; cbn). reflexivity. }
unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd.
destruct (frames_bounds segs B LAWS lyc Sc Wc memc mdc c' p' HAR ltac:(rewrite Hfrs; apply in_or_app; left; rewrite Eo; apply in_or_app; right; left; reflexivity)) as (Hf0' & Hfc' & Hfh').
pose proof (shadow_range_end (frame_addr lyc c' p') (fs_frame_bytes c') (fs_frame_bytes_nonneg c')) as Hse'.
pose proof (fs_frame_bytes_nonneg c') as Hnn'.
destruct Hr' as [[[Hlo0' Hlo'] Hr'] | [[Hlo1' Hhi'] Hr']]; unfold in_zr, frame_rng in Hr'; cbn [fst snd] in Hr'.
+ destruct Hr as [Hr | Hr]; [zlia | zlia].
+ destruct Hr as [Hr | Hr]; [zlia |].
destruct Hd as [Hd | Hd].
* pose proof (shadow_mono _ _ Hd). zlia.
* pose proof (shadow_mono _ _ Hd). zlia.
-
destruct (al_frames _ _ LAWS lyc Sc Wc memc mdc cid pos HAR HinC) as (_ & _ & Hfb & Hfsh).
rewrite <- ?Efa in Hr.
exfalso. destruct Hr as [Hr|Hr]; [exact (proj2 (Hfb a Hr) Hxo)|].
specialize (Hfsh (a - shadow_addr (frame_addr lyc cid pos)) ltac:(zlia)).
replace (shadow_addr (frame_addr lyc cid pos) + (a - shadow_addr (frame_addr lyc cid pos))) with a in Hfsh by zlia.
exact (proj2 Hfsh Hxo).
- rewrite <- ?Efa in Hr. destruct Hr as [Hr | Hr].
  + exact (frm_img segs B LAWS lyc Sc Wc memc mdc cid pos a HAR HinC Hr Hei).
  + zlia. }
split; [exact Hgone|].
split; [intros a Ha; apply Hgr; apply Hpres, Ha|].
split; [exact Hstatic|]. split; [|exact HQT'].
{
intros a HXa He. rewrite <- (F5 a HXa He).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Eslo & Eshi & _ & _ & Eextra & _).
assert (HXc : Exists (in_zr a) (ly_extra lyc)) by (rewrite Eextra; exact HXa).
pose proof (AR_extra_law_ok segs B lyc Sc Wc memc mdc a HAR HXc) as (Xo & Xb & Xf & Xs & Xi & Xsh & Xapp).
assert (Ha64 : 0 <= a < 2 ^ 64) by (unfold app_addr, ASAN_CEIL, kLowShadowBeg, kHighMemBeg in Xapp; zlia).
apply Heqw; [exact Ha64|]. intros HWa. exfalso.
destruct (HWw a HWa) as [[(_ & [[Hc' Hs'] | [(_ & b & m & Hbin & Hr & _) | (cid & pos & Hown & [[_ Hr] | [[Hsl Hsh] Hr]])]]) | (Hxo & Hx)] | (Her & _ & _)].
- apply Xs. rewrite Eslo, Eshi. zlia.
- exact (Xb b m Hbin Hr).
- assert (Hin' : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr. exact (proj1 (Xf cid pos Hin') Hr).
- assert (Hin' : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
unfold in_zr in Hr; cbn [fst snd] in Hr. exact (proj2 (Xf cid pos Hin') Hr).
- exact (Xo Hxo).
- exact (He Her). }
Qed.

(* numberK.v aj_strtol_atS in hole form: the strtol call at sp = sp0 + o inside the hole, with the end pointer's word
   [e, e + 8) a cell of the caller's window above the callee's sp. The pattern is kept. *)
Lemma hj_strtol_at : forall pc gotw guard, hd_astrtol_hole segs B pc gotw guard ->
forall W (regsT : bvmap 5 word) memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x e (str : list byte) ev (o : Z) raw
  fr pat,
hjournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k fr pat ->
getr regsT 10 = w64 x -> getr regsT 11 = w64 e -> getr regsT 12 = w64 10 -> 0 < x -> 0 < e ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 3 * ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
(rdword (aview segs (w_H W) memT) gotw = Some guard /\ (exists can, rdword (aview segs (w_H W) memT) guard = Some can)) ->
((forall i, (i < length (str ++ [Z_to_bv 8 0]))%nat ->
  aview segs (w_H W) memT (x + Z.of_nat i) = Some (bv_unsigned (nth i (str ++ [Z_to_bv 8 0]) (Z_to_bv 8 0)))) /\
 ~ In (Z_to_bv 8 0) str) ->
x + Z.of_nat (length str) + 1 < 2 ^ 64 ->
(0 <= x /\ x + (Z.of_nat (length str) + 1) <= 2 ^ 63 /\ 0 <= Z.of_nat (length str) + 1 < 2 ^ 32 /\
 (forall a, x <= a < x + (Z.of_nat (length str) + 1) ->
  aview segs (w_H W) memT a <> None /\ ~ (spZ regsT - 3 * ESTACK <= a < spZ regsT)) /\
 amem_range x (Z.of_nat (length str) + 1) /\
 range_addressable (aview segs (w_H W) memT) SHADOW_OFF x (Z.of_nat (length str) + 1) /\
 (0 < Z.of_nat (length str) + 1 -> shadow_hull_vis (aview segs (w_H W) memT) x (Z.of_nat (length str) + 1))) ->
amem_range x (Z.of_nat (length str) + 8) ->
(forall a, x + Z.of_nat (length str) < a < x + Z.of_nat (length str) - (x + Z.of_nat (length str)) mod 8 + 8 ->
 aview segs (w_H W) memT a <> None) ->
sp0 + o <= e -> e + 8 <= sp0 -> e + 8 <= 2 ^ 63 -> amem_range e 16 ->
range_addressable (aview segs (w_H W) memT) SHADOW_OFF e 8 -> shadow_hull_vis (aview segs (w_H W) memT) e 8 ->
(e + 8 <= x \/ x + Z.of_nat (length str) + 1 <= e) ->
(e + 8 <= as_errno B \/ as_errno B + 4 <= e) ->
e mod 8 = 0 ->
(forall a, e <= a < e + 8 -> ~ in_zr a (ly_img lyc)) ->
(as_errno B + 4 <= x \/ x + Z.of_nat (length str) + 1 <= as_errno B) ->
rd32 (aview segs (w_H W) memT) (as_errno B) ev ->
(forall a, in_rom segs a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
 aview segs (w_H W) memT a = option_map (fun b : byte => bv_unsigned b) (seg_rom segs (Z_to_bv 64 a))) ->
SRr segs W (cfg_at segs pc regsT memT mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
 c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
 hjournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k fr pat /\
 aregs_preserved regsT regs2 /\ same_io mdc md2 /\
 getr regs2 10 = w64 (PIS.s10_val str) /\
 rdword (aview segs (w_H W) mem2) e = Some (x + PIS.s10_end str) /\
 rd32 (aview segs (w_H W) mem2) (as_errno B) (bv_unsigned (PIS.s10_errno str (Z_to_bv 64 ev))) /\
 (forall a, 0 <= a < 2 ^ 64 -> ~ (e <= a < e + 8) -> ~ (as_errno B <= a < as_errno B + 4) ->
  ~ (sp0 + o - 3 * ESTACK <= a < sp0 + o) -> aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
 (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof.
intros pc gotw guard HC W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x e str ev o raw fr pat
  HJ Ha0 Ha1 Ha2 Hx He Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hgd Hstr Hxl Hrd Hamx Htl He1 He2 He8 Hame Hra_e Hhull
  Hsep Hsepe Hem8 Heoff Hxer Hev Hrom.
pose proof (AR_laws_ok segs B) as LAWS.
pose proof HJ as (HJ0 & OK & _).
pose proof HJ0 as (HAR & Hly & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstatic & _ & HQT).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
pose proof (am_layout B lyc Sc _ (proj1 HAR)) as LO.
assert (ESTACK = 4096) as Hes by reflexivity.
assert (HPRE : ecall_preH segs B (3 * ESTACK) lyc Sc fr pat W regsT memT mdc).
{ apply (hj_ecall_pre segs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k fr pat regsT o (3 * ESTACK) HJ Hsp'
    Hal Hneg); [lia | lia | rewrite Hra; exact Hraw | exact Hgp | exact Htp]. }
assert (HWR : 0 <= e /\ e + 8 <= 2 ^ 63 /\ 0 <= 8 < 2 ^ 32 /\
  (forall a, e <= a < e + 8 ->
   writable_at segs (mrestrict (w_H W) memT) a /\ ~ aowned B lyc Sc a /\ ~ (spZ regsT - 3 * ESTACK <= a < spZ regsT)) /\
  amem_range e 8 /\ range_addressable (aview segs (w_H W) memT) SHADOW_OFF e 8 /\
  (0 < 8 -> shadow_hull_vis (aview segs (w_H W) memT) e 8)).
{ split; [lia|]. split; [exact He8|]. split; [lia|].
  split.
  { intros a Ha.
    assert (Hst : ly_stk_lo lyc <= a < 2 ^ 64) by (rewrite Eslo; lia).
    assert (Hp : apresent (w_H W) memT a).
    { apply (proj1 (hp_apresent_unp _ (hU fr pat) memT a (hole_free_stack lyc fr pat a LO OK Hst))). apply Hpres. lia. }
    split; [exact (apresent_writable segs _ _ a Hp)|].
    split; [exact (al_stack _ _ LAWS lyc Sc W _ mdc a HAR ltac:(rewrite Eslo, Eshi; lia))|].
    rewrite Hsp'. lia. }
  split; [unfold amem_range in *; lia|]. split; [exact Hra_e|]. intros _. exact Hhull. }
eapply SRr_mono.
{ exact (HC lyc Sc W regsT memT mdc x e str ev fr pat Hgd HPRE Ha0 Ha1 Ha2 Hx He Hstr Hxl Hrd Hamx Htl HWR Hame Hsep
    Hsepe Hem8 Heoff Hxer Hev Hrom). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP2 & HPr & Hsame & (Hres & Hend & Herr) & Hfr & Hpres2 & _).
rewrite Hsp' in Hfr.
split; [reflexivity|]. exists regs2, mem2, md2.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ split; [|split; [exact OK | exact HP2]].
  eapply (ajournal_after_write_errno STK sp0 FP ly S W0 mem md own lyc Sc W (unpoison (hU fr pat) memT) mdc k
    (unpoison (hU fr pat) mem2) md2
    (fun a => (sp0 + o - 3 * ESTACK <= a < sp0 + o) \/ (e <= a < e + 8) \/ (as_errno B <= a < as_errno B + 4)) Sc own HJ0).
  - intros a Ha Hna. destruct (in_ush (hU fr pat) (bv_unsigned (Z_to_bv 64 a))) eqn:Ei.
    + apply aview_unpoison_in. exact Ei.
    + rewrite !aview_unpoison_out by exact Ei.
      apply (Hfr a Ha); [intros H'; apply Hna; left; exact H' | intros H'; apply Hna; right; exact H'].
  - intros a Hp. destruct (in_ush (hU fr pat) (bv_unsigned (Z_to_bv 64 a))) eqn:Ei.
    + destruct Hp as [Hh _]. split; [exact Hh|]. exists (Z_to_bv 8 0). apply unpoison_in. exact Ei.
    + apply (hp_apresent_unp _ (hU fr pat) mem2 a Ei). apply Hpres2. apply (hp_apresent_unp _ (hU fr pat) memT a Ei). exact Hp.
  - exact Hsame.
  - intros a [Ha | [Ha | Ha]].
    + left. left. lia.
    + left. left. lia.
    + right; right. split; [exact Ha | exact (proj1 (proj2 errno_low) a Ha)].
  - exact HAR2.
  - reflexivity.
  - reflexivity.
  - lia.
  - exact Hfrs.
  - exact HQT. }
split; [exact HPr|]. split; [apply same_io_materialized; exact Hsame|].
split; [exact Hres|]. split; [exact Hend|]. split; [exact Herr|].
split; [intros a Ha H1 H2 H3; apply (Hfr a Ha); [exact H3 | intros [H' | H']; [exact (H1 H') | exact (H2 H')]]|].
exact Hpres2.
Qed.

End e.

(* ======================================== the chunk runners over the unpoisoned journal ========================================
   YCbq.v's runners (SRr_chain_AJ / SRr_run_AJ / SRr_run_to_AJ, lines 2408-2470, and the token forms
   SRr_chain_tok_AJ / SRr_run_tok_AJ / SRr_run_to_tok_AJ, lines 2471-2546) with the journal over unpoison U of the
   machine's memory at the chunk's start and end, and a write set whose bytes are the journal's (awr_byte) or the
   hole's (in_ush U). The proof is the kit's, with ajournal_exec applied to the unpoisoned memories: a hole byte reads
   0 on both sides, every other byte is the machine's. *)
Section r. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Variable tbl : ctable.
Hypothesis tbl_ok : table_ok segs tbl.
Hypothesis Hwx : wx_segs_nowrap segs.

Definition awr_okH (E : env) (rs : smem) (STK sp0 : Z) (FP : list (Z * Z)) (bl0 blc : list (Z * Z))
(ly : alayout) (own : list (Z * Z)) (U : list (Z * Z)) : Prop :=
forall a, in_wrange E rs a -> awr_byte STK sp0 FP bl0 blc ly own a \/ in_ush U a = true.

Lemma awr_okH_of_ok : forall E rs STK sp0 FP bl0 blc ly own U,
awr_ok E rs STK sp0 FP bl0 blc ly own -> awr_okH E rs STK sp0 FP bl0 blc ly own U.
Proof. intros E rs STK sp0 FP bl0 blc ly own U H a Ha. left. exact (H a Ha). Qed.

Lemma awr_okH_nil : forall E STK sp0 FP bl0 blc ly own U, awr_okH E [] STK sp0 FP bl0 blc ly own U.
Proof. intros E STK sp0 FP bl0 blc ly own U a (r & Hin & _). destruct Hin. Qed.

Lemma awr_okH_cons_gen : forall E r rs STK sp0 FP bl0 blc ly own U k b,
r_base r = Some k -> bv_unsigned (ew E k) = b ->
(forall a, b + r_wlo r <= a < b + r_whi r -> awr_byte STK sp0 FP bl0 blc ly own a \/ in_ush U a = true) ->
awr_okH E rs STK sp0 FP bl0 blc ly own U -> awr_okH E (r :: rs) STK sp0 FP bl0 blc ly own U.
Proof.
intros E r rs STK sp0 FP bl0 blc ly own U k b Hb Hk Hw H a (r' & [<-|Hin] & Ha).
- rewrite Hb in Ha. cbn [base_val] in Ha. rewrite Hk in Ha. apply Hw. lia.
- apply H. exists r'. auto.
Qed.

Lemma awr_okH_cons_ro : forall E r rs STK sp0 FP bl0 blc ly own U,
r_whi r <= r_wlo r -> awr_okH E rs STK sp0 FP bl0 blc ly own U -> awr_okH E (r :: rs) STK sp0 FP bl0 blc ly own U.
Proof.
intros E r rs STK sp0 FP bl0 blc ly own U Hro H a (r' & [<-|Hin] & Ha); [lia|]. apply H. exists r'. auto.
Qed.

(* A region based at the hole's first shadow byte whose writes stay inside the hole (the parse's s10 =
   shadow_addr (sp' + 0x40) with its byte stores at 0 .. 7). *)
Lemma awr_okH_cons_hole : forall E r rs STK sp0 FP bl0 blc ly own fr pat k,
r_base r = Some k -> bv_unsigned (ew E k) = shadow_addr fr -> 0 <= r_wlo r -> r_whi r <= Z.of_nat (length pat) ->
awr_okH E rs STK sp0 FP bl0 blc ly own (hU fr pat) -> awr_okH E (r :: rs) STK sp0 FP bl0 blc ly own (hU fr pat).
Proof.
intros E r rs STK sp0 FP bl0 blc ly own fr pat k Hb Hk Hlo Hhi H.
apply (awr_okH_cons_gen E r rs STK sp0 FP bl0 blc ly own (hU fr pat) k (shadow_addr fr) Hb Hk); [|exact H].
intros a Ha. right. apply in_hU. lia.
Qed.

Definition run_post_AJH (W : world segs) (E : env) (ss ss' : sstate)
(ms : machine_state) (STK sp0 : Z) (FP : list (Z * Z)) ly S W0 mem md own lyc Sc (mdc : Model) (k : Z)
(U : list (Z * Z)) (Q : world segs -> config -> Prop) : Prop :=
forall ms' mat',
st_ok segs E ss' (restrict (w_H W) ms') ->
ajournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W (unpoison U (ms_mem ms')) (with_vm_backing (m_vm_lazy mdc) mat' mdc) k ->
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
SRr segs W (mkCfg ms' (with_vm_backing (m_vm_lazy mdc) mat' mdc)) Q.

Definition run_post_tok_AJH (W : world segs) (E : env) (K : nat) (Bx : sv) (SH : list shent) (ss : sstate) (st' : shst)
(ms : machine_state) (STK sp0 : Z) (FP : list (Z * Z)) ly S W0 mem md own lyc Sc (mdc : Model) (k : Z)
(U : list (Z * Z)) (Q : world segs -> config -> Prop) : Prop :=
forall ws ms' mat',
length ws = sh_j st' ->
st_ok segs (extK E K ws) (sh_ss st') (restrict (w_H W) ms') ->
sh_ok segs Bx SH (extK E K ws) (mrestrict (w_H W) (ms_mem ms')) ->
ajournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W (unpoison U (ms_mem ms')) (with_vm_backing (m_vm_lazy mdc) mat' mdc) k ->
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
SRr segs W (mkCfg ms' (with_vm_backing (m_vm_lazy mdc) mat' mdc)) Q.

(* The step from a chunk's start to its end on the unpoisoned memories: ajournal_exec's memory premises. *)
Lemma aj_exec_unpoison : forall W E ss ms msr' STK sp0 FP ly S W0 mem md own lyc Sc mdc k U model',
frame_of E (ss_mem ss) (ms_mem (restrict (w_H W) ms)) (ms_mem msr') ->
mem_grows (mrestrict (w_H W) (ms_mem ms)) (ms_mem msr') ->
same_but_materialized mdc model' ->
ajournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W (unpoison U (ms_mem ms)) mdc k ->
awr_okH E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own U ->
ajournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W (unpoison U (ms_mem (unrestrict (w_H W) (ms_mem ms) msr')))
  (with_vm_backing (m_vm_lazy mdc) (m_vm_materialized model') mdc) k.
Proof.
intros W E ss ms msr' STK sp0 FP ly S W0 mem md own lyc Sc mdc k U model' Hfr Hgr Hsame HJ Hwr.
pose proof (AR_laws_ok segs B) as LAWS.
eapply (ajournal_exec segs B LAWS segs_low) with (Wr := fun a => in_wrange E (ss_mem ss) a /\ in_ush U a = false);
  [exact HJ | | | | |].
- intros x Hx. unfold mrestrict, unpoison. cbv beta.
  destruct (w_H W x) eqn:Eh; [reflexivity|].
  destruct (in_ush U (bv_unsigned x)) eqn:Ei; [reflexivity|].
  assert (Hnw : ~ in_wrange E (ss_mem ss) (bv_unsigned x)) by (intros Hw; apply Hx; split; [exact Hw | reflexivity]).
  cbn [unrestrict ms_mem]. unfold munrestrict. rewrite Eh. rewrite (Hfr x Hnw). cbn [restrict ms_mem].
  unfold mrestrict. rewrite Eh. reflexivity.
- intros x Hx. unfold mrestrict, unpoison in Hx |- *. cbv beta in Hx |- *.
  destruct (w_H W x) eqn:Eh; [exact Hx|].
  destruct (in_ush U (bv_unsigned x)) eqn:Ei; [discriminate|].
  cbn [unrestrict ms_mem]. unfold munrestrict. rewrite Eh. apply Hgr. unfold mrestrict. rewrite Eh. exact Hx.
- intros x Hx. unfold unpoison. destruct (in_ush U (bv_unsigned x)); [reflexivity|].
  cbn [unrestrict ms_mem]. unfold munrestrict. rewrite Hx. reflexivity.
- rewrite <- (same_but_materialized_wvb mdc model' Hsame). exact Hsame.
- intros a [Hw Ei]. destruct (Hwr a Hw) as [H|H]; [exact H | rewrite H in Ei; discriminate].
Qed.

Lemma SRr_chain_AJH : forall W E ss ss' ms msr' STK sp0 FP ly S W0 mem md own lyc Sc mdc k U Q,
msteps segs (restrict (w_H W) ms) msr' ->
st_ok segs E ss' msr' ->
frame_of E (ss_mem ss) (ms_mem (restrict (w_H W) ms)) (ms_mem msr') ->
ajournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W (unpoison U (ms_mem ms)) mdc k ->
awr_okH E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own U ->
run_post_AJH W E ss ss' ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k U Q ->
SRr segs W (mkCfg ms mdc) Q.
Proof.
intros W E ss ss' ms msr' STK sp0 FP ly S W0 mem md own lyc Sc mdc k U Q Hms HS' Hfr HJ Hwr Hk.
apply (SRr_msteps segs Hwx W ms msr' mdc Q Hms).
intros model' Hsame Hcl.
rewrite (same_but_materialized_wvb mdc model' Hsame).
pose proof (restrict_unrestrict_clean (w_H W) (ms_mem ms) msr' Hcl) as Hrr.
pose proof (mrestrict_unrestrict_mem (w_H W) (ms_mem ms) msr' Hcl) as Hmm.
pose proof (msteps_mem_grows segs _ _ Hms) as Hgr. cbn [ms_mem restrict] in Hgr.
apply (Hk (unrestrict (w_H W) (ms_mem ms) msr') (m_vm_materialized model')).
- rewrite Hrr. exact HS'.
- exact (aj_exec_unpoison W E ss ms msr' STK sp0 FP ly S W0 mem md own lyc Sc mdc k U model' Hfr Hgr Hsame HJ Hwr).
- cbn [unrestrict ms_mem]. apply frame_of_unrestrict. exact Hfr.
- rewrite Hmm. exact Hfr.
- rewrite Hmm. exact Hgr.
Qed.

Lemma SRr_run_AJH : forall W n E ss ss' st ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k U Q,
st_ok segs E ss (restrict (w_H W) ms) ->
sym_runN segs tbl n ss = (ss', st) ->
match st with RS_ecall => False | _ => True end ->
ajournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W (unpoison U (ms_mem ms)) mdc k ->
awr_okH E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own U ->
run_post_AJH W E ss ss' ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k U Q ->
SRr segs W (mkCfg ms mdc) Q.
Proof.
intros W n E ss ss' st ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k U Q HS Hrun Hst HJ Hwr Hk.
destruct (msteps_run_gen segs tbl tbl_ok n E ss ss' st _ HS Hrun) as (msr' & Hms & HS' & Hfr).
eapply SRr_chain_AJH; [exact Hms | destruct st; [exact HS' | destruct Hst | exact HS'] | exact Hfr | exact HJ | exact Hwr | exact Hk].
Qed.

Lemma SRr_run_to_AJH : forall W n stop E ss ss' st ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k U Q,
st_ok segs E ss (restrict (w_H W) ms) ->
sym_run_toN segs tbl n stop ss = (ss', st) ->
match st with RS_ecall => False | _ => True end ->
ajournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W (unpoison U (ms_mem ms)) mdc k ->
awr_okH E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own U ->
run_post_AJH W E ss ss' ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k U Q ->
SRr segs W (mkCfg ms mdc) Q.
Proof.
intros W n stop E ss ss' st ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k U Q HS Hrun Hst HJ Hwr Hk.
destruct (msteps_run_to_gen segs tbl tbl_ok n stop E ss ss' st _ HS Hrun) as (msr' & Hms & HS' & Hfr).
eapply SRr_chain_AJH; [exact Hms | destruct st; [exact HS' | destruct Hst | exact HS'] | exact Hfr | exact HJ | exact Hwr | exact Hk].
Qed.

Lemma SRr_chain_tok_AJH : forall W E K Bx SH ws ss st' ms msr' STK sp0 FP ly S W0 mem md own lyc Sc mdc k U Q,
msteps segs (restrict (w_H W) ms) msr' ->
length ws = sh_j st' ->
st_ok segs (extK E K ws) (sh_ss st') msr' ->
sh_ok segs Bx SH (extK E K ws) (ms_mem msr') ->
frame_of E (ss_mem ss) (ms_mem (restrict (w_H W) ms)) (ms_mem msr') ->
ajournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W (unpoison U (ms_mem ms)) mdc k ->
awr_okH E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own U ->
run_post_tok_AJH W E K Bx SH ss st' ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k U Q ->
SRr segs W (mkCfg ms mdc) Q.
Proof.
intros W E K Bx SH ws ss st' ms msr' STK sp0 FP ly S W0 mem md own lyc Sc mdc k U Q Hms Hlen HS' Hsh' Hfr HJ Hwr Hk.
apply (SRr_msteps segs Hwx W ms msr' mdc Q Hms).
intros model' Hsame Hcl.
rewrite (same_but_materialized_wvb mdc model' Hsame).
pose proof (restrict_unrestrict_clean (w_H W) (ms_mem ms) msr' Hcl) as Hrr.
pose proof (mrestrict_unrestrict_mem (w_H W) (ms_mem ms) msr' Hcl) as Hmm.
pose proof (msteps_mem_grows segs _ _ Hms) as Hgr. cbn [ms_mem restrict] in Hgr.
apply (Hk ws (unrestrict (w_H W) (ms_mem ms) msr') (m_vm_materialized model') Hlen).
- rewrite Hrr. exact HS'.
- rewrite Hmm. exact Hsh'.
- exact (aj_exec_unpoison W E ss ms msr' STK sp0 FP ly S W0 mem md own lyc Sc mdc k U model' Hfr Hgr Hsame HJ Hwr).
- cbn [unrestrict ms_mem]. apply frame_of_unrestrict. exact Hfr.
- rewrite Hmm. exact Hfr.
- rewrite Hmm. exact Hgr.
Qed.

Lemma SRr_run_tok_AJH : forall W n E K Bx Bspan SH ss st' r ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k U Q,
st_ok segs E ss (restrict (w_H W) ms) ->
sh_ok segs Bx SH E (mrestrict (w_H W) (ms_mem ms)) ->
sh_static_ok K Bx Bspan SH (ss_facts ss) (ss_mem ss) = true ->
sym_runN_tok segs tbl K Bx Bspan SH n ss = (st', r) ->
match r with TS_ecall => False | _ => True end ->
ajournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W (unpoison U (ms_mem ms)) mdc k ->
Forall (ob_holds segs Bx E (mrestrict (w_H W) (ms_mem ms))) (sh_obls st') ->
awr_okH E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own U ->
run_post_tok_AJH W E K Bx SH ss st' ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k U Q ->
SRr segs W (mkCfg ms mdc) Q.
Proof.
intros W n E K Bx Bspan SH ss st' r ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k U Q HS Hsh Hchk Hrun Hr HJ Hobl Hwr Hk.
destruct (sym_run_tok_sound segs tbl K Bx Bspan SH tbl_ok n E ss _ st' r HS Hsh Hchk Hrun Hobl)
as (ws & msr' & Hlen & Hms & HS' & Hsh' & _ & Hfr).
eapply SRr_chain_tok_AJH; [exact Hms | exact Hlen | destruct r; [exact HS' | destruct Hr | exact HS'] | exact Hsh' | exact Hfr | exact HJ | exact Hwr | exact Hk].
Qed.

Lemma SRr_run_to_tok_AJH : forall W n stop E K Bx Bspan SH ss st' r ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k U Q,
st_ok segs E ss (restrict (w_H W) ms) ->
sh_ok segs Bx SH E (mrestrict (w_H W) (ms_mem ms)) ->
sh_static_ok K Bx Bspan SH (ss_facts ss) (ss_mem ss) = true ->
sym_run_toN_tok segs tbl K Bx Bspan SH n stop ss = (st', r) ->
match r with TS_ecall => False | _ => True end ->
ajournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W (unpoison U (ms_mem ms)) mdc k ->
Forall (ob_holds segs Bx E (mrestrict (w_H W) (ms_mem ms))) (sh_obls st') ->
awr_okH E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own U ->
run_post_tok_AJH W E K Bx SH ss st' ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k U Q ->
SRr segs W (mkCfg ms mdc) Q.
Proof.
intros W n stop E K Bx Bspan SH ss st' r ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k U Q HS Hsh Hchk Hrun Hr HJ Hobl Hwr Hk.
destruct (sym_run_to_tok_sound segs tbl K Bx Bspan SH tbl_ok n stop E ss _ st' r HS Hsh Hchk Hrun Hobl)
as (ws & msr' & Hlen & Hms & HS' & Hsh' & _ & Hfr).
eapply SRr_chain_tok_AJH; [exact Hms | exact Hlen | destruct r; [exact HS' | destruct Hr | exact HS'] | exact Hsh' | exact Hfr | exact HJ | exact Hwr | exact Hk].
Qed.

End r.

(* The kit's aj_run / aj_run_to / aj_run_tok / aj_run_to_tok (YCbq.v:3045-3166) for the unpoisoned journal: HJ is
   `ajournal segs B ... W (unpoison U (ms_mem ms)) mdc k`; the goals left are the write-set obligation awr_okH (for
   the token forms after the run's obligations), then the continuation with the journal over unpoison U of the
   chunk's end memory. *)
Ltac aj_runH tblok HS HJ :=
lazymatch type of HS with
| st_ok ?segs ?E ?ss (restrict (w_H ?W) ?ms) =>
lazymatch type of tblok with
| table_ok _ ?tbl =>
let r := eval vm_compute in (sym_runN segs tbl FUEL ss) in
lazymatch r with
| (?ss', ?st) =>
let Hrun := fresh "Hrun" in
assert (Hrun : sym_runN segs tbl FUEL ss = (ss', st)) by (vm_compute; reflexivity);
let HSL := aj_segs_low in let HWX := aj_wx in
eapply (SRr_run_AJH segs _ HSL tbl tblok HWX W FUEL E ss ss' st ms _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HS Hrun I HJ);
[ clear Hrun | clear Hrun HS HJ; aj_after_run HS HJ ]
end
end
| _ => fail "aj_runH: HS must be  st_ok segs E ss (restrict (w_H W) ms)"
end.
Ltac aj_run_toH tblok HS HJ stop :=
lazymatch type of HS with
| st_ok ?segs ?E ?ss (restrict (w_H ?W) ?ms) =>
lazymatch type of tblok with
| table_ok _ ?tbl =>
let r := eval vm_compute in (sym_run_toN segs tbl FUEL stop ss) in
lazymatch r with
| (?ss', ?st) =>
let Hrun := fresh "Hrun" in
assert (Hrun : sym_run_toN segs tbl FUEL stop ss = (ss', st)) by (vm_compute; reflexivity);
let HSL := aj_segs_low in let HWX := aj_wx in
eapply (SRr_run_to_AJH segs _ HSL tbl tblok HWX W FUEL stop E ss ss' st ms _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HS Hrun I HJ);
[ clear Hrun | clear Hrun HS HJ; cbv beta iota; aj_after_run HS HJ ]
end
end
| _ => fail "aj_run_toH: HS must be  st_ok segs E ss (restrict (w_H W) ms)"
end.
Ltac aj_run_tokH tblok HS HJ SHOK Bspan :=
lazymatch type of HS with
| st_ok ?segs ?E ?ss (restrict (w_H ?W) ?ms) =>
lazymatch type of SHOK with
| sh_ok _ ?Bx ?SH _ _ =>
lazymatch type of tblok with
| table_ok _ ?tbl =>
let K := eval vm_compute in (run_K 0 Bx SH ss) in
let r := eval vm_compute in (sym_runN_tok segs tbl K Bx Bspan SH FUEL ss) in
lazymatch r with
| (?st', ?rs) =>
let Hrun := fresh "Hrun" in
assert (Hrun : sym_runN_tok segs tbl K Bx Bspan SH FUEL ss = (st', rs)) by (vm_compute; reflexivity);
let HSL := aj_segs_low in let HWX := aj_wx in
eapply (SRr_run_tok_AJH segs _ HSL tbl tblok HWX W FUEL E K Bx Bspan SH ss st' rs ms _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HS SHOK
ltac:(vm_compute; reflexivity) Hrun I HJ);
[ clear Hrun; cbn [sh_obls]; srr_obls
| clear Hrun
| clear Hrun HS HJ SHOK; try match type of ms with machine_state => clear ms | _ => idtac end;
aj_after_run_tok HS HJ SHOK ]
end
end end
| _ => fail "aj_run_tokH: HS must be  st_ok segs E ss (restrict (w_H W) ms)"
end.
Ltac aj_run_to_tokH tblok HS HJ SHOK Bspan stop :=
lazymatch type of HS with
| st_ok ?segs ?E ?ss (restrict (w_H ?W) ?ms) =>
lazymatch type of SHOK with
| sh_ok _ ?Bx ?SH _ _ =>
lazymatch type of tblok with
| table_ok _ ?tbl =>
let K := eval vm_compute in (run_K 0 Bx SH ss) in
let r := eval vm_compute in (sym_run_toN_tok segs tbl K Bx Bspan SH FUEL stop ss) in
lazymatch r with
| (?st', ?rs) =>
let Hrun := fresh "Hrun" in
assert (Hrun : sym_run_toN_tok segs tbl K Bx Bspan SH FUEL stop ss = (st', rs)) by (vm_compute; reflexivity);
let HSL := aj_segs_low in let HWX := aj_wx in
eapply (SRr_run_to_tok_AJH segs _ HSL tbl tblok HWX W FUEL stop E K Bx Bspan SH ss st' rs ms _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HS SHOK
ltac:(vm_compute; reflexivity) Hrun I HJ);
[ clear Hrun; cbn [sh_obls]; srr_obls
| clear Hrun
| clear Hrun HS HJ SHOK; try match type of ms with machine_state => clear ms | _ => idtac end;
aj_after_run_tok HS HJ SHOK ]
end
end end
| _ => fail "aj_run_to_tokH: HS must be  st_ok segs E ss (restrict (w_H W) ms)"
end.

(* ======================================== image A's numbers ========================================
   fuzz_headamp.asan, pinned sha256 f3e0669d2819724922df0556b11c2dcd22d1e16fe7e0fe1535ce784b34436c47 (addresses measured
   on the unstripped twin b5f352154c54a97c66fd92dfa228e8a854498f6cd313dba0107900546b043f9a, whose loaded sections are
   byte-equal to the pin's except .note.gnu.build-id). The trampolines are the ones HPgCSpec's header names. Every (pc, instruction word) below
   is checked against image A's loaded segments (lib/A/Img0.v) by computation. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Img0 HPgSat.
Definition A_PARSE_RESULT : Z := 0x845b4.
Definition A_TRAMP_STRNCMP : Z := 0x41ba4.
Definition A_TRAMP_STRTOL : Z := 0x41c28.
Definition A_TRAMP_STRCMP : Z := 0x41ba0.
(* The five calls inside the hole: strncmp (pattern PAT_KEY), strtol and the three strcmp (pattern PAT_DOT). *)
Definition A_CALL_STRNCMP : Z := 0x849c8.
Definition A_CALL_STRTOL : Z := 0x84a0c.
Definition A_CALLS_STRCMP : list Z := [0x84a50; 0x84a6c; 0x84a80].
(* The open's eight stores, the dot stores, the close's eight stores and the parse's one return. *)
Definition A_OPEN : list Z := [0x84648; 0x8464c; 0x84650; 0x84654; 0x8465c; 0x84660; 0x84664; 0x84668].
Definition A_DOT_IN : Z := 0x849f8.
Definition A_DOT_OUT : list Z := [0x84aec; 0x84b2c].
Definition A_CLOSE : list Z := [0x84744; 0x84748; 0x8474c; 0x84750; 0x84754; 0x84758; 0x8475c; 0x84760].
Definition A_RET : Z := 0x847a8.
Definition headamp_A_hole_insns : list (Z * Z) :=
  [(0x845b4, 0xf0010113) (* addi sp,sp,-256 *); (0x845f4, 0xfe017113) (* andi sp,sp,-32 *);
   (0x84614, 0x04010793) (* addi a5,sp,64: fr *); (0x84640, 0x0037d793) (* srli a5,a5,3 *);
   (0x84644, 0x01b78d33) (* add s10,a5,s11: shadow_addr fr *);
   (0x84648, 0x00bd0223); (0x8464c, 0x010d02a3); (0x84650, 0x010d0323); (0x84654, 0x010d03a3);
   (0x8465c, 0x00bd0023); (0x84660, 0x00bd00a3); (0x84664, 0x00bd0123); (0x84668, 0x00bd01a3) (* open: f8 f3 f3 f3, f1 x4 *);
   (0x849c8, 0x9dcbd0ef) (* jal 0x41ba4 *); (0x849f8, 0x000d0223) (* sb zero,4(s10) *);
   (0x849fc, 0x06013023) (* sd zero,96(sp) *); (0x84a08, 0x06010593) (* addi a1,sp,96: e = fr + 32 *);
   (0x84a0c, 0xa1cbd0ef) (* jal 0x41c28 *); (0x84a50, 0x950bd0ef); (0x84a6c, 0x934bd0ef); (0x84a80, 0x920bd0ef) (* jal 0x41ba0 *);
   (0x84aec, 0x00ad0223); (0x84b2c, 0x00ad0223) (* sb a0,4(s10), a0 = -8 *);
   (0x84744, 0x000d0223); (0x84748, 0x000d02a3); (0x8474c, 0x000d0323); (0x84750, 0x000d03a3);
   (0x84754, 0x000d0023); (0x84758, 0x000d00a3); (0x8475c, 0x000d0123); (0x84760, 0x000d01a3) (* close *);
   (0x847a8, 0x00008067) (* ret *)].
Lemma headamp_A_hole_insns_chk : HPgSat.entries_chk Img0.rsegs headamp_A_hole_insns = true.
Proof. vm_compute. reflexivity. Qed.
Lemma headamp_A_hole_insns_ok : forall a w, In (a, w) headamp_A_hole_insns ->
  forall k, (k < 4)%nat -> seg_rom Img0.rsegs (Z_to_bv 64 (a + Z.of_nat k)) = Some (Z_to_bv 8 (YO0f.le_byte w 4 k)).
Proof.
intros a w Hin k Hk. refine (HPgSat.img_val_chk_ok Img0.rsegs a 4 w _ k Hk).
pose proof headamp_A_hole_insns_chk as E. unfold HPgSat.entries_chk in E. rewrite forallb_forall in E.
exact (E (a, w) Hin).
Qed.

(* hd_hole_sat_A at image A's own segments (lib/A/Img0.v), the twin of lib/AU/HPgHole.v hd_hole_sat_B. hd_hole_open_sat
   gives the same at any later plain-journal state of the walk with the hole inside the stack range (the walk reaches
   the open after the frame-header stores A 0x84630 .. 0x84638, stack stores the plain journal carries). *)
Section ai. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis segs_low : forall a, in_img Img0.rsegs a -> 0 <= a < kLowMemEnd.
Lemma hd_hole_sat_A_img : forall STK sp0 FP ly S W0 mem0 md0 own k (regs : bvmap 5 word) lyc Sc W memc mdc,
hd_pre Img0.rsegs B STK sp0 FP ly S W0 mem0 md0 own k T_parse_STK regs lyc Sc W memc mdc ->
hjournal Img0.rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W
  (hset memc (shadow_addr (hd_fr (Z.land (spZ regs - 0x100) (-32)))) PAT_KEY) mdc k
  (hd_fr (Z.land (spZ regs - 0x100) (-32))) PAT_KEY.
Proof. exact (hd_hole_sat_A Img0.rsegs B segs_low). Qed.
End ai.
Print Assumptions hd_hole_sat_A_img.

Print Assumptions in_hU.
Print Assumptions hole_raw_zero.
Print Assumptions ARH_open.
Print Assumptions ARH_close.
Print Assumptions ARH_repat.
Print Assumptions ARH_frame.
Print Assumptions hj_enter.
Print Assumptions hj_enter0.
Print Assumptions hj_leave.
Print Assumptions hj_repat.
Print Assumptions hj_repat_raw.
Print Assumptions hj_aj_write_U.
Print Assumptions hj_ecall_pre.
Print Assumptions hj_strncmp_at.
Print Assumptions hj_strcmp_at.
Print Assumptions stack_shadow_zero.
Print Assumptions hd_dot_ok.
Print Assumptions hd_hole_open_sat.
Print Assumptions hd_parse_frame.
Print Assumptions hd_site_pre.
Print Assumptions hd_hole_sat_A.
Print Assumptions hd_ARH_sat_A.
Print Assumptions awr_okH_cons_hole.
Print Assumptions SRr_chain_AJH.
Print Assumptions SRr_run_AJH.
Print Assumptions SRr_run_to_AJH.
Print Assumptions SRr_chain_tok_AJH.
Print Assumptions SRr_run_tok_AJH.
Print Assumptions SRr_run_to_tok_AJH.
Print Assumptions headamp_A_hole_insns_ok.
Print Assumptions ajournal_after_write_errno.
Print Assumptions hj_strtol_at.

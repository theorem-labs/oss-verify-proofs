(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_box_catalogue on fuzz_segconf.asan-ubsan (image B, pin sha256
   c3796c0b38f3, twin 80e82127e8ca; entry 0x8a8a0, 84 bytes, 21 instructions, a 16-byte frame, no side-stack
   frame): reac_box_catalogue_contract of lib/B/Prog/reac_box_catalogue_c.v (image B's copy of the image-A owner's FINAL
   text at 6f783602b5e3) at image B's numbers, in plugin-hostd/fuzz_command's lib/A/Prog form (afn_pre at the
   entry, SRr of apost_base at the return, over `Context {PI : PAImg seg_listing}` of image B's listing,
   lib/B/Prog/SegPa.v).
   ADAPTATION (relocation + one trap) of lib/A/Prog/reac_box_catalogueA.v (the image-A m_file-family lane, commit
   434ade288123, both arms): the same entry seeds, token runs and return steps over image B's listing modules and
   B's kit copies. The UBSan alignment check is read from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_catalogue.v
   at origin/ossv/recipes 3abc3740de97 (the same image-B code but 4 pc-relative words; caller-journal form, not
   copied), whose token run decides it the same way.
   Image B's code differs from image A's by two instructions: `andi a1,a0,7` (0x8a8ac) and `bnez a1,0x8a8ec`
   (0x8a8b0) to `unimp` (0x8a8ec), the UBSan alignment check of the 8-byte store through c.
   UBSan trap branch (one): 0x8a8b0 `bnez a1` -> unimp 0x8a8ec. Not taken: the c <> 0 run's entry seed carries the
   fact (10%nat, mkAF 4096 (2 ^ 47 - 8) 3) on a0 (rbc_facts: c is 2^3-aligned, from the contract premise
   c mod 8 = 0, seeded by rbc_entry), so the token executor (paj_run_tok, its branch step under facts_ok) computes
   a1 = c & 7 = 0 and decides the branch not taken; the trap instruction is never executed. The c = 0 run leaves at
   the beqz 0x8a8a8 (a0 pinned to 0) before the check.
   c <> 0: the instrumented check of the 8-byte cell (a load of the shadow byte at (c >> 3) + the shadow base, lbu
   0x8a8c8, and a compare, bnez 0x8a8cc) reads 0, because the contract's sa_addr gives the cell addressable; so the
   error path (the call of errpath_store8 at 0x8a8f0) is not reached; the sd at 0x8a8d4 writes 11 as 8 bytes. In
   both arms a0 = fuzz_catalogue (auipc/addi 0x8a8d8-0x8a8dc, 0xa20a0). The shadow base is the word the GOT cell
   as_got_shadow B holds (image B 0xa3210, the ld at 0x8a8b8, listing object 0; its target
   __asan_shadow_memory_dynamic_address 0xac7b8, listing object 12): the walk takes both from PALib (pal_got_shadow,
   pal_cell), a listing fact, not a contract premise.
   Positional names checked against image B's own listing (lib/B/Prog/SegAddr.v seg_objs, SegList.v) by address and
   anchor symbol (twin nm): A_OBJ 0 = 0xa3210 (the .got word the ld at 0x8a8b8 reads), A_OBJ 12 = 0xac7b8
   (__asan_shadow_memory_dynamic_address), A_OBJ 77 = RBC_CAT_OBJ = 0xa20a0 (fuzz_catalogue; SegList.v
   `PAddHi (10%bv : reg) (10%bv : reg) 123 (A_OBJ 77) 0x0` at 0x8a8dc), AF_reac_box_catalogue = 0x5ae0 =
   0x8a8a0 - seg_text 0x84dc0, atom 32 = the first extra env word (the shadow base SB, rbc_extra): 5 checked, 0
   pointing elsewhere.
   Image B's numbers of the statement: the entry BASE + AF_reac_box_catalogue; STK_reac_box_catalogue = 16 (the
   contract's STK comment: its frame, 0x8a8a0 addi sp,sp,-16 released at 0x8a8e4; the unimp at 0x8a8ec and the jal
   at 0x8a8f0 are the dead trap and error arms; no callee); cat = catA = 0xa20a0. Both are lib/B/Prog/SegInstB.v's
   definitions (SegInstA's names at image B): SegInstB.STK_reac_box_catalogue and SegInstB.catA, tied to this walk
   by the lemmas STK_reac_box_catalogue_B (the value 16) and catA_B (listing object 77 of B's seg_objs). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module names changed; 642 of its 693 lines of code are new or changed and 402 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/pf_seg_B10b_rk.v; 67 of its 272 lines of code are new or changed and 488 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca): the frame facts
   that segment B6 of reac_segconf_parse_file's walk needs at its two calls (strspn 0x88260, refuse 0x882b4): the
   geometry of a cut state, the shadow cell of a frame byte, sa_addr of a range of the frame whose shadow cells
   are 0, sa_fframe of a range of the frame, and one %s argument of refuse lying in the frame.
   The B6 segment lane of the image-B G3 walk owner, 2026-10-30. proves no function (kind: walk kit).
   COPIED, with the prefix b6a_ changed to b6a_, from the sibling B11c segment lane of this same stream
   (lib/B/Prog/pf_seg_B11c_k.v and pf_seg_B11c_r.v at commit 98d1e87bd9d7, themselves ADAPTED
   from the image-A G3 walk owner's lib/A/Prog/pf_a7_s.v and pf_a11b_f.v); those files are not in this lane's base, so the text
   is carried here rather than Required. *)

From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq YG0d_tail.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec pfA_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList
SegAddr SegPa SegObj SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPaLib PaDenot PaLibG PaLibF PaLibH PaCall
PaCallRun PaArt PaFx.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import refuse_c reac_segconf_parse_file_c SegInstB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import pf_pieces.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Lemma b6a_m16 : forall a b, a mod 16 = 0 -> b mod 16 = 0 -> (a - b) mod 16 = 0.
Proof. intros a b Ha Hb. rewrite Zminus_mod, Ha, Hb. reflexivity. Qed.
Lemma b6a_round32 : forall x, 0 <= x -> x mod 16 = 0 ->
  x - 16 <= x - x mod 32 <= x /\ (x - x mod 32) mod 32 = 0 /\ (x - x mod 32) mod 16 = 0.
Proof.
intros x Hx H16. pose proof (Z.div_mod x 32 ltac:(lia)) as D. pose proof (Z.mod_pos_bound x 32 ltac:(lia)) as M.
pose proof (Z.div_mod x 16 ltac:(lia)) as D16.
assert (E : x - x mod 32 = 32 * (x / 32)) by lia. rewrite E.
assert (x mod 32 = 0 \/ x mod 32 = 16) by lia.
split; [lia|]. split; [rewrite Z.mul_comm; apply Z_mod_mult|].
replace (32 * (x / 32)) with ((2 * (x / 32)) * 16) by lia. apply Z_mod_mult.
Qed.
Lemma b6a_zrange : forall (f : Z -> bool) lo (n : nat),
  forallb (fun k => f (lo + Z.of_nat k)) (seq 0 n) = true -> forall i, lo <= i < lo + Z.of_nat n -> f i = true.
Proof.
intros f lo n H i Hi. rewrite forallb_forall in H.
specialize (H (Z.to_nat (i - lo)) ltac:(apply in_seq; lia)).
replace (lo + Z.of_nat (Z.to_nat (i - lo))) with i in H by lia. exact H.
Qed.
Lemma b6a_rg : forall rX L r v, pf_rg rX L -> In (r, v) L -> getr rX (Z_to_bv 5 r) = w64 v.
Proof. intros rX L r v H Hin. exact (proj1 (Forall_forall _ _) H (r, v) Hin). Qed.
Ltac b6a_in := cbn [In app]; repeat first [left; reflexivity | right].
Ltac b6a_rreg HS :=
 lazymatch goal with |- getr (ms_regs ?ms) ?r = _ =>
 lazymatch type of HS with
 | st_ok_pi _ _ ?E ?ss (restrict ?Hh ms) =>
  rewrite (st_ok_pi_restrict_reg Hh E ss ms r HS);
  let v := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with v
 end end.
Ltac b6a_clear_md := repeat match goal with |- context [with_vm_backing (m_vm_lazy ?m) ?x ?m] =>
  let mdv := fresh "mdv" in set (mdv := with_vm_backing (m_vm_lazy m) x m) in *; clearbody mdv end.
Lemma b6a_w64_u : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (w64 z) = z.
Proof. intros z Hz. unfold w64. apply unsigned_lit_small. lia. Qed.

(* ---------- the frame shadow scopes B11c changes (pf_pieces.v pf_shb) ---------- *)
(* model low's three cells (0x5c-0x5e): 0x00 in PF_SC_L146, 0xf8 in PF_SC_LINE; every other cell the same *)
Lemma b6a_shb_line : forall i, 0x5c <= i < 0x5f -> pf_shb PF_SC_LINE i = 0xf8.
Proof.
intros i Hi. apply Z.eqb_eq. revert i Hi.
apply (b6a_zrange (fun i => pf_shb PF_SC_LINE i =? 0xf8) 0x5c 3). vm_compute. reflexivity.
Qed.

(* ---------- the frame shadow scopes B11c changes (pf_pieces.v pf_shb) ---------- *)
(* model low's three cells (0x5c-0x5e): 0x00 in PF_SC_L146, 0xf8 in PF_SC_LINE; every other cell the same *)
Lemma b6a_nth_firstn : forall {A} n (l : list A) k d, (k < n)%nat -> nth k (firstn n l) d = nth k l d.
Proof.
  intros A n. induction n as [|n IH]; intros l k d Hk; [lia|].
  destruct l as [|x l]; [destruct k; reflexivity|]. cbn [firstn].
  destruct k as [|k]; [reflexivity|]. cbn [nth]. apply IH. lia.
Qed.
Lemma b6a_le65535 : forall m : nat, (m <= 65535)%nat -> Z.of_nat m <= 65535.
Proof.
  intros m H. apply Nat2Z.inj_le in H.
  assert (E : Z.of_nat 65535%nat = 65535) by (vm_compute; reflexivity).
  rewrite E in H. exact H.
Qed.
Lemma b6a_round8 : forall x M, x <= M -> M mod 8 = 0 -> x + (- x) mod 8 <= M.
Proof.
  intros x M H1 H2.
  pose proof (Z.div_mod (- x) 8 ltac:(lia)) as D1.
  pose proof (Z.mod_pos_bound (- x) 8 ltac:(lia)) as M1.
  pose proof (Z.div_mod M 8 ltac:(lia)) as D2.
  lia.
Qed.
Lemma b6a_nm_str : forall (rd : reader) a nm, a mod 8 = 0 -> pf_nm rd a nm ->
  sa_str rd a nm /\ (length nm < 16)%nat.
Proof.
  intros rd a nm Ha (f & Hb & Hl & Hn & Hz & Hf).
  assert (Hnth : forall i, (i < 16)%nat -> rd (a + Z.of_nat i) = Some (nth i (seg_spec.zs f) 0)).
  { intros i Hi. rewrite (Hb i ltac:(lia)). f_equal. unfold seg_spec.zs.
    rewrite <- (map_nth bv_unsigned f ZB0 i). apply nth_indep. rewrite length_map. lia. }
  split; [|exact Hn].
  split; [split; [|exact Hz]|].
  - intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
    rewrite (Hnth i ltac:(lia)). f_equal. rewrite <- Hf. rewrite b6a_nth_firstn by lia. reflexivity.
  - intros x Hx.
    pose proof (Z.div_mod (a + Z.of_nat (length nm)) 8 ltac:(lia)) as D.
    pose proof (Z.mod_pos_bound (a + Z.of_nat (length nm)) 8 ltac:(lia)) as M.
    pose proof (Z.div_mod a 8 ltac:(lia)) as Da. rewrite Ha in Da.
    replace x with (a + Z.of_nat (Z.to_nat (x - a))) by lia.
    rewrite (Hnth (Z.to_nat (x - a)) ltac:(lia)). discriminate.
Qed.
Lemma b6a_bvr : forall (rr : bvmap 5 word) (r : bv 5) k x, bv_unsigned r = k -> getr rr (Z_to_bv 5 k) = x -> getr rr r = x.
Proof. intros rr r k x Hr H. subst k. rewrite Z_to_bv_bv_unsigned in H. exact H. Qed.

(* in PF_SC_LINE the cells of cur_name (4, 5) and buf (8 .. 71) are 0 *)
Lemma b6a_shb_line0 : forall i, (4 <= i < 6 \/ 8 <= i < 72) -> pf_shb PF_SC_LINE i = 0.
Proof.
intros i Hi. apply Z.eqb_eq.
destruct Hi as [Hi | Hi]; revert i Hi;
  [apply (b6a_zrange (fun i => pf_shb PF_SC_LINE i =? 0) 4 2)
  |apply (b6a_zrange (fun i => pf_shb PF_SC_LINE i =? 0) 8 64)]; vm_compute; reflexivity.
Qed.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Variable B : asyms.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Definition b6a_geoP (v : pfv) (pos : Z) : Prop :=
  alloc_ceiling + 12832 <= pf_sp0 v /\ pf_sp0 v <= 2 ^ 47 /\ pf_sp0 v mod 16 = 0 /\
  pf_sp0 v - 368 <= pf_s1 v <= pf_sp0 v - 352 /\ pf_s1 v mod 32 = 0 /\ pf_s1 v mod 16 = 0 /\
  4096 <= pf_F v pos /\ pf_F v pos + 2048 <= alloc_ceiling /\ pf_F v pos mod 32 = 0 /\
  (pf_F v pos + 2048 <= 0x7fff7000 \/ 0x10007fff8000 <= pf_F v pos) /\
  (forall a, 0x10000 <= a < kImgEnd -> ~ (pf_F v pos <= a < pf_F v pos + 2048)).
Lemma b6a_geo : forall v pos lyc Sc Wc rX memc mdc, pf_cx B v -> pf_fi B v pos lyc Sc Wc rX memc mdc ->
  b6a_geoP v pos /\ In (5, pos) (frames Sc) /\ frame_addr lyc 5 pos = pf_F v pos /\
  frames Sc = (5, pos) :: frames (p_S v) /\ AR SEGS B lyc Sc Wc memc mdc.
Proof.
intros v pos lyc Sc Wc rX memc mdc HCX HFI.
destruct HCX as (HPRE & _). destruct HPRE as (_ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hal & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof STK_values as (_ & _ & _ & ESTK & _). rewrite ESTK in Hslo.
destruct HFI as (HJ & Hly & _).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hin : In (5, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (al_frames _ _ LAWS lyc Sc Wc memc mdc 5 pos HAR Hin) as (H32 & Happ & _ & _).
destruct (frames_bounds SEGS B LAWS lyc Sc Wc memc mdc 5 pos HAR Hin) as (Hf0 & Hfc & _).
assert (EF : frame_addr lyc 5 pos = pf_F v pos) by (subst lyc; reflexivity).
pose proof asan_consts as (C1 & _).
change (fs_frame_bytes 5) with 2048 in Hfc, Happ.
rewrite EF in H32, Happ, Hf0, Hfc.
change (spZ (p_regs v)) with (pf_sp0 v) in Hal, Hslo, Hshi.
assert (Hsp : 0 <= pf_sp0 v) by lia.
pose proof (b6a_round32 (pf_sp0 v - 352) ltac:(lia) ltac:(apply b6a_m16; [exact Hal | reflexivity])) as (R1 & R2 & R3).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ.
split; [|split; [exact Hin | split; [exact EF | split; [exact Hfrs | exact HAR]]]].
unfold b6a_geoP, pf_s1.
split; [lia|]. split; [lia|]. split; [exact Hal|]. split; [lia|]. split; [exact R2|]. split; [exact R3|].
split; [lia|]. split; [lia|]. split; [exact H32|]. split; [lia|].
pose proof HAR as (_ & LG & _).
pose proof (pa_img_cover lyc Sc mdc LG) as [IC1 IC2].
intros a Ha Hf. rewrite <- EF in Hf.
destruct (al_client_img _ _ LAWS lyc Sc Wc memc mdc a HAR
  ltac:(right; left; exists 5, pos; split; [exact Hin | change (fs_frame_bytes 5) with 2048; exact Hf])) as (Hz & _).
apply Hz. unfold in_zr. unfold kImgEnd in *. lia.
Qed.
Lemma b6a_SHb : forall v pos, b6a_geoP v pos ->
  pf_SH v pos = SHADOW_OFF + pf_F v pos / 8 /\ 0x7fff8000 + 512 <= pf_SH v pos /\
  pf_SH v pos + 256 <= 0x10007fff8000 /\ pf_F v pos = 8 * (pf_F v pos / 8) /\ pf_SH v pos mod 4 = 0.
Proof.
intros v pos (S1 & S2 & S3 & S4 & S5 & S6 & F1 & F2 & F3 & F4 & _). pose proof asan_consts as (C1 & _).
assert (F8 : pf_F v pos mod 8 = 0).
{ apply Z.mod_divide in F3 as [q Hq]; [|lia]. rewrite Hq. replace (q * 32) with ((4 * q) * 8) by lia. apply Z_mod_mult. }
pose proof (Z.div_mod (pf_F v pos) 8 ltac:(lia)) as DF. rewrite F8 in DF.
assert (F4' : (pf_F v pos / 8) mod 4 = 0).
{ apply Z.mod_divide in F3 as [q Hq]; [|lia]. rewrite Hq. replace (q * 32) with ((4 * q) * 8) by lia.
  rewrite Z.div_mul by lia. replace (4 * q) with (q * 4) by lia. apply Z_mod_mult. }
unfold pf_SH, shadow_addr, SHADOW_OFF.
split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
rewrite Zplus_mod, F4'. reflexivity.
Qed.
Lemma b6a_sh_cell : forall v pos x, b6a_geoP v pos -> pf_F v pos <= x < pf_F v pos + 2048 ->
  shadow_of_addr SHADOW_OFF x = pf_SH v pos + (x - pf_F v pos) / 8.
Proof.
intros v pos x HG Hx.
destruct (b6a_SHb v pos HG) as (ESH & _ & _ & EF & _).
pose proof HG as (_ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
assert (HF8 : pf_F v pos mod 8 = 0) by (pose proof (Z.div_mod (pf_F v pos) 32 ltac:(lia)); lia).
replace x with (pf_F v pos + (x - pf_F v pos)) at 1 by lia.
rewrite (shadow_of_addr_aligned_off SHADOW_OFF (pf_F v pos) (x - pf_F v pos) HF8).
reflexivity.
Qed.
Lemma b6a_addr_frame : forall v pos (rd : reader) sc q n, b6a_geoP v pos -> pf_fsh rd (pf_SH v pos) sc ->
  pf_F v pos + 32 <= q -> 0 <= n -> q + n <= pf_F v pos + 1088 ->
  (forall x, q <= x < q + n -> pf_shb sc ((x - pf_F v pos) / 8) = 0) ->
  sa_addr rd q n.
Proof.
intros v pos rd sc q n HG HF Hq Hn Hqn HZ.
pose proof HG as (S1 & S2 & S3 & S4 & S5 & S6 & F1 & F2 & F3 & F4 & _).
destruct (b6a_SHb v pos HG) as (ESH & SH1 & SH2 & EF & SH4).
pose proof alloc_ceiling_lt as HC.
assert (HF8 : pf_F v pos mod 8 = 0) by (pose proof (Z.div_mod (pf_F v pos) 32 ltac:(lia)); lia).
split; [lia|]. split; [lia|].
split.
{ apply amem_range_high; [lia| |lia]. destruct F4 as [F4|F4]; [left; lia | right; lia]. }
split.
- intros x Hx. exists 0. split; [|left; reflexivity].
  rewrite (b6a_sh_cell v pos x HG ltac:(lia)).
  assert (B0 : 0 <= (x - pf_F v pos) / 8 < 144) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
  rewrite (HF ((x - pf_F v pos) / 8) B0). f_equal. exact (HZ x Hx).
- intros Hn0 s Hs.
  assert (E1 : shadow_addr q = pf_SH v pos + (q - pf_F v pos) / 8)
    by exact (b6a_sh_cell v pos q HG ltac:(lia)).
  assert (E2 : shadow_addr (q + n - 1) = pf_SH v pos + (q + n - 1 - pf_F v pos) / 8)
    by exact (b6a_sh_cell v pos (q + n - 1) HG ltac:(lia)).
  assert (B1 : 4 <= (q - pf_F v pos) / 8) by (apply Z.div_le_lower_bound; lia).
  assert (B2 : (q + n - 1 - pf_F v pos) / 8 < 136) by (apply Z.div_lt_upper_bound; lia).
  rewrite E1, E2 in Hs.
  pose proof (Z.div_mod (pf_SH v pos + (q - pf_F v pos) / 8) 8 ltac:(lia)) as D1.
  pose proof (Z.mod_pos_bound (pf_SH v pos + (q - pf_F v pos) / 8) 8 ltac:(lia)) as M1.
  pose proof (Z.div_mod (pf_SH v pos + (q + n - 1 - pf_F v pos) / 8) 8 ltac:(lia)) as D2.
  pose proof (Z.mod_pos_bound (pf_SH v pos + (q + n - 1 - pf_F v pos) / 8) 8 ltac:(lia)) as M2.
  pose proof (Z.div_mod (pf_SH v pos) 4 ltac:(lia)) as D4. rewrite SH4 in D4.
  assert (Hlo : pf_SH v pos <= s).
  { (* the hull's first word: SH is 4-aligned and the first cell is at least 4 *)
    assert (Q : (pf_SH v pos + (q - pf_F v pos) / 8) / 8 * 8 >= pf_SH v pos) by lia. lia. }
  assert (Hhi : s < pf_SH v pos + 144) by lia.
  replace s with (pf_SH v pos + (s - pf_SH v pos)) by lia.
  rewrite (HF (s - pf_SH v pos) ltac:(lia)). discriminate.
Qed.
Lemma b6a_fframe : forall v pos lyc Sc q n, In (5, pos) (frames Sc) -> frame_addr lyc 5 pos = pf_F v pos ->
  pf_F v pos <= q -> 0 <= n -> q + n <= pf_F v pos + 2048 -> sa_fframe lyc Sc q n.
Proof.
intros v pos lyc Sc q n Hin EF Hq Hn Hqn. exists 5, pos. split; [exact Hin|]. split; [lia|].
rewrite EF. change (fs_frame_bytes 5) with 2048. lia.
Qed.
Lemma b6a_va_frame : forall v pos lyc Sc (Wc : world SEGS) memc mdc sc (rd : reader) q s sp (k : nat) M,
  b6a_geoP v pos -> AR SEGS B lyc Sc Wc memc mdc -> In (5, pos) (frames Sc) -> frame_addr lyc 5 pos = pf_F v pos ->
  pf_fsh rd (pf_SH v pos) sc -> sa_str rd q s -> (length s <= 65535)%nat ->
  pf_F v pos + 32 <= q -> q + Z.of_nat (length s) + 1 <= M -> M mod 8 = 0 -> M <= pf_F v pos + 1088 ->
  (forall x, q <= x < q + (Z.of_nat (length s) + 1) -> pf_shb sc ((x - pf_F v pos) / 8) = 0) ->
  sa_heap B lyc Sc (p_c v) seg_spec.SEG_C_SIZE -> (k <= 8)%nat -> alloc_ceiling <= ly_stk_lo lyc ->
  sa_va_arg rd
    [(ly_stk_lo lyc, sp);
     (seg_spec.refusal_addr (p_c v) k, seg_spec.refusal_addr (p_c v) k + seg_spec.RC_REFUSAL_LEN);
     (p_c v + seg_spec.RC_REFUSED, p_c v + seg_spec.RC_REFUSED + 4)] (w64 q) (AS s) /\
  sa_fframe lyc Sc q (Z.of_nat (length s) + 1).
Proof.
intros v pos lyc Sc Wc memc mdc sc rd q s sp k M HG HAR Hin EF HF HS HL Hq HM HM8 HMF HZ Hc Hk Hceil.
pose proof HG as (S1 & S2 & S3 & S4 & S5 & S6 & F1 & F2 & F3 & F4 & _).
pose proof asan_consts as (C1 & _).
assert (EQ : bv_unsigned (w64 q) = q) by (apply b6a_w64_u; lia).
split; [|apply (b6a_fframe v pos lyc Sc q _ Hin EF); lia].
cbn [sa_va_arg]. rewrite EQ.
split; [lia|]. split; [exact HS|]. split; [exact HL|].
split; [apply (b6a_addr_frame v pos rd sc q (Z.of_nat (length s) + 1) HG HF Hq ltac:(lia) ltac:(lia) HZ)|].
(* the span stays in the frame, below the stack and apart from the block c *)
pose proof (b6a_round8 (q + Z.of_nat (length s) + 1) M HM HM8) as HR.
assert (HSP : q + seg_spec.cstr_span q s <= M) by (unfold seg_spec.cstr_span; lia).
destruct Hc as (b & m & Hb & Hb1 & Hb2).
pose proof (sep_block_frame SEGS B LAWS lyc Sc Wc memc mdc b m 5 pos HAR Hb Hin) as Hsep.
destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc b m HAR Hb) as (_ & _ & _ & _ & _ & _ & Hm).
pose proof (req_size_pos m (proj1 Hm)) as [_ Hrq].
unfold zdisjoint in Hsep. cbn [fst snd] in Hsep. rewrite EF in Hsep. change (fs_frame_bytes 5) with 2048 in Hsep.
assert (HAP : q + seg_spec.cstr_span q s <= p_c v \/ p_c v + seg_spec.SEG_C_SIZE <= q)
  by (destruct Hsep as [Hs|Hs]; [right|left]; lia).
unfold sa_apart_all, seg_spec.refusal_addr, seg_spec.RC_REFUSAL, seg_spec.RC_REFUSAL_LEN,
  seg_spec.RC_REFUSED, seg_spec.SEG_C_SIZE in *.
apply Forall_cons; [cbn [fst snd]; lia|].
apply Forall_cons; [cbn [fst snd]; lia|].
apply Forall_cons; [cbn [fst snd]; lia|].
apply Forall_nil.
Qed.
End d.

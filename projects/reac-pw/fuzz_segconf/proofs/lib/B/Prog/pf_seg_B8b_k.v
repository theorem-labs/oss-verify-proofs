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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 76 of its 115 lines of code are new or changed and 414 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/pf_a8b_d.v; 203 of its 258 lines of code are new or changed and 60 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/pf_a8b_k.v, with its module paths and module names changed; 104 of its 262 lines of code are new or changed and 100 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan): the fact-transport kit of segment B8b of
   reac_segconf_parse_file's walk. The B8b segment lane of the image-B G3 walk owner (ported by a sub-lane), 2026-10-30.
   ADAPTED (port) from a working branch's lib/A/Prog/pf_a8b_k.v: module paths lib.A -> lib.B, names
   pfa8b_ -> pb8b_ (this file's A names carried the prefix pfk_; they are pb8b_ here).
   proves no function (kind: invariant lemma) -- transport lemmas for the B8b segment lane's segment B8b of
   reac_segconf_parse_file; no function of the binary is walked. The lane's rule-24 record is
   the rule-24 lookup record (reuse verdict: none).

   Every call B8b makes (the checked memset, the two snprintf, refuse) returns a keep clause of the shape
   "every byte outside [d, d + L) and outside [lo, hi) reads as before": [d, d + L) is the destination the callee
   writes and [lo, hi) its own stack window. That clause is pb8b_keep below. The lemmas carry each conjunct of
   pf_base's object, slot, saved-register and frame-shadow parts (lib/B/Prog/pf_pieces.v pf_obj, pf_sl,
   pf_saved, pf_fsh, pf_nm) across it:
   - a fact over named bytes needs those bytes apart from both ranges (pb8b_apart);
   - a fact over image bytes (literals, the catalogue, the read-only view) needs no image byte in either range
     (pb8b_noimg): what a destination in a live block or a live side-stack frame and a window above
     alloc_ceiling give;
   - a shadow fact (sa_addr) needs no shadow byte in either range (pb8b_noshadow).
   The facts that do not read the reader (sa_heap, sa_pinned, sa_romtail, sa_img) pass through unchanged.

   Section hypotheses: VRO only (seg_val_relro, for the read-only range RLO_A .. RHI_A being image bytes), and
   only pb8b_relro_img, pb8b_arodata and pb8b_pf_obj carry it. pb8b_arodata is stated at RLO_A / RHI_A (a general
   RLO / RHI range need not be image bytes, so the general form is false); pb8b_arodata_gen is the general form
   with that premise explicit (an image-A segment lane's ruling, 2026-10-30). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec pfA_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require RtFormat RtPFCmd.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList
SegAddr SegPa SegObj SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPaLib PaDenot PaLibG PaLibF PaLibH PaSB
PaCall PaCallRun PaArt PaFx.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import refuse_c reac_segconf_parse_file_c
SegInstB pf_pieces.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(** ** The keep clause and the three separation conditions *)
(* what a call's post keeps: every byte outside the written range [d, d + L) and the callee's window [lo, hi) *)
Definition pb8b_keep (rd rd' : reader) (d L lo hi : Z) : Prop :=
  forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + L) -> ~ (lo <= a < hi) -> rd' a = rd a.
(* the shadow bytes: neither written range holds one (the slack is the hull's rounding to 8) *)
Definition pb8b_noshadow (d L lo hi : Z) : Prop :=
  forall x, kLowMemEnd - 8 <= x < kHighMemBeg + 8 -> ~ (d <= x < d + L) /\ ~ (lo <= x < hi).
(* a range [q, q + n) untouched by both written ranges *)
Definition pb8b_apart (q n d L lo hi : Z) : Prop :=
  (d + L <= q \/ q + n <= d) /\ (hi <= q \/ q + n <= lo).

(* the ASan constants these lemmas compare against (YCbq.asan_consts without its RunCeil part) *)
Lemma pb8b_consts : kHighShadowEnd = 0x10007fff8000 /\ kHighMemBeg = 0x10007fff8000 /\
  kHighMemEnd = 0x800000000000 /\ kLowMemEnd = 0x7fff8000 /\ 2 ^ 64 = 18446744073709551616.
Proof. repeat split; reflexivity. Qed.

Lemma pb8b_keep_at : forall rd rd' d L lo hi a,
  pb8b_keep rd rd' d L lo hi -> 0 <= a < 2 ^ 64 -> pb8b_apart a 1 d L lo hi -> rd' a = rd a.
Proof.
intros rd rd' d L lo hi a K Ha [A1 A2]. unfold pb8b_keep in K.
apply K; [exact Ha | intros ?; lia | intros ?; lia].
Qed.
(* every byte of a range apart from both written ranges reads as before *)
Lemma pb8b_keep_in : forall rd rd' d L lo hi q n a,
  pb8b_keep rd rd' d L lo hi -> pb8b_apart q n d L lo hi -> 0 <= q -> q + n <= 2 ^ 64 -> q <= a < q + n ->
  rd' a = rd a.
Proof.
intros rd rd' d L lo hi q n a K [A1 A2] H0 H1 Ha. unfold pb8b_keep in K.
apply K; [lia | intros ?; lia | intros ?; lia].
Qed.
(* the shadow bytes read as before *)
Lemma pb8b_keep_shadow : forall rd rd' d L lo hi s,
  pb8b_keep rd rd' d L lo hi -> pb8b_noshadow d L lo hi -> kLowMemEnd - 8 <= s < kHighMemBeg + 8 -> rd' s = rd s.
Proof.
intros rd rd' d L lo hi s K NS Hs. destruct (NS s Hs) as [N1 N2].
pose proof pb8b_consts as (_ & E2 & _ & E4 & E64).
unfold pb8b_keep in K. apply K; [lia | exact N1 | exact N2].
Qed.
Lemma pb8b_rdword_eq : forall (rd rd' : reader) a, (forall x, a <= x < a + 8 -> rd' x = rd x) ->
  rdword rd' a = rdword rd a.
Proof.
intros rd rd' a K. unfold rdword.
rewrite (K a), (K (a + 1)), (K (a + 2)), (K (a + 3)), (K (a + 4)), (K (a + 5)), (K (a + 6)), (K (a + 7)) by lia.
reflexivity.
Qed.

(** ** Bytes, words and strings at named addresses *)
Lemma pb8b_rdword : forall rd rd' d L lo hi a,
  pb8b_keep rd rd' d L lo hi -> 0 <= a -> a + 8 <= 2 ^ 64 -> pb8b_apart a 8 d L lo hi ->
  rdword rd' a = rdword rd a.
Proof.
intros rd rd' d L lo hi a K H0 H1 A. apply pb8b_rdword_eq. intros x Hx.
exact (pb8b_keep_in rd rd' d L lo hi a 8 x K A H0 H1 Hx).
Qed.
Lemma pb8b_sa_zs : forall rd rd' d L lo hi p (l : list Z),
  pb8b_keep rd rd' d L lo hi -> sa_zs rd p l -> 0 <= p -> p + Z.of_nat (length l) <= 2 ^ 64 ->
  pb8b_apart p (Z.of_nat (length l)) d L lo hi -> sa_zs rd' p l.
Proof.
intros rd rd' d L lo hi p l K H H0 H1 A i Hi.
rewrite (pb8b_keep_in rd rd' d L lo hi p (Z.of_nat (length l)) (p + Z.of_nat i) K A H0 H1) by lia.
exact (H i Hi).
Qed.
Lemma pb8b_sa_bytes : forall rd rd' d L lo hi p (bs : list byte),
  pb8b_keep rd rd' d L lo hi -> sa_bytes rd p bs -> 0 <= p -> p + Z.of_nat (length bs) <= 2 ^ 64 ->
  pb8b_apart p (Z.of_nat (length bs)) d L lo hi -> sa_bytes rd' p bs.
Proof.
intros rd rd' d L lo hi p bs K H H0 H1 A i Hi.
rewrite (pb8b_keep_in rd rd' d L lo hi p (Z.of_nat (length bs)) (p + Z.of_nat i) K A H0 H1) by lia.
exact (H i Hi).
Qed.
Lemma pb8b_sa_str : forall rd rd' d L lo hi p (l : list Z),
  pb8b_keep rd rd' d L lo hi -> sa_str rd p l -> 0 <= p -> p + Z.of_nat (length l) + 8 <= 2 ^ 64 ->
  pb8b_apart p (Z.of_nat (length l) + 8) d L lo hi -> sa_str rd' p l.
Proof.
intros rd rd' d L lo hi p l K [[Hz Hn] Ht] H0 H1 A. split; [split; [|exact Hn]|].
- intros i Hi. pose proof Hi as Hi'. rewrite length_app in Hi'. cbn [length] in Hi'.
  rewrite (pb8b_keep_in rd rd' d L lo hi p (Z.of_nat (length l) + 8) (p + Z.of_nat i) K A H0 ltac:(lia))
    by lia.
  exact (Hz i Hi).
- intros x Hx. pose proof (Z.mod_pos_bound (p + Z.of_nat (length l)) 8 ltac:(lia)) as M.
  rewrite (pb8b_keep_in rd rd' d L lo hi p (Z.of_nat (length l) + 8) x K A H0 ltac:(lia)) by lia.
  exact (Ht x Hx).
Qed.
Lemma pb8b_sa_ssp : forall rd rd' d L lo hi gotw guard,
  pb8b_keep rd rd' d L lo hi -> sa_ssp rd gotw guard -> 0 <= gotw -> gotw + 8 <= 2 ^ 64 ->
  0 <= guard -> guard + 8 <= 2 ^ 64 ->
  pb8b_apart gotw 8 d L lo hi -> pb8b_apart guard 8 d L lo hi -> sa_ssp rd' gotw guard.
Proof.
intros rd rd' d L lo hi gotw guard K (G1 & g & G2) H0 H1 H2 H3 A1 A2. split.
- rewrite (pb8b_rdword rd rd' d L lo hi gotw K H0 H1 A1). exact G1.
- exists g. rewrite (pb8b_rdword rd rd' d L lo hi guard K H2 H3 A2). exact G2.
Qed.

(** ** Shadow facts *)
(* sa_addr reads only shadow bytes: range_addressable reads SHADOW_OFF + x / 8 for q <= x < q + n, and the hull
   reads [shadow_addr q / 8 * 8, shadow_addr (q + n - 1) / 8 * 8 + 8); both lie in [kLowMemEnd - 8,
   kHighMemBeg + 8) for 0 <= q, q + n < kHighMemEnd (YCbq.shadow_addr_bounds, kHighShadowEnd = kHighMemBeg) *)
Lemma pb8b_sa_addr : forall rd rd' d L lo hi q n,
  pb8b_keep rd rd' d L lo hi -> pb8b_noshadow d L lo hi -> sa_addr rd q n -> 0 <= q -> q + n < kHighMemEnd ->
  sa_addr rd' q n.
Proof.
intros rd rd' d L lo hi q n K NS (A0 & A1 & A2 & A3 & A4) H0 H1.
pose proof pb8b_consts as (E1 & E2 & E3 & E4 & E64).
unfold sa_addr. refine (conj A0 (conj A1 (conj A2 (conj _ _)))).
- intros x Hx. destruct (A3 x Hx) as (s & Es & Ok). exists s. split; [|exact Ok].
  rewrite (pb8b_keep_shadow rd rd' d L lo hi _ K NS); [exact Es|].
  pose proof (YCbq.shadow_addr_bounds x ltac:(lia)) as Bx. unfold shadow_addr in Bx. unfold shadow_of_addr.
  lia.
- intros Hn s Hs. pose proof (A4 Hn s Hs) as Es.
  rewrite (pb8b_keep_shadow rd rd' d L lo hi s K NS); [exact Es|].
  pose proof (YCbq.shadow_addr_bounds q ltac:(lia)) as Bq.
  pose proof (YCbq.shadow_addr_bounds (q + n - 1) ltac:(lia)) as Be.
  pose proof (Z.div_mod (shadow_addr q) 8 ltac:(lia)) as Dq.
  pose proof (Z.mod_pos_bound (shadow_addr q) 8 ltac:(lia)) as Mq.
  pose proof (Z.div_mod (shadow_addr (q + n - 1)) 8 ltac:(lia)) as De.
  pose proof (Z.mod_pos_bound (shadow_addr (q + n - 1)) 8 ltac:(lia)) as Me.
  lia.
Qed.

(** ** The saved registers, the spill slots, the frame's shadow, cur_name *)
Lemma pb8b_pf_sl : forall rd rd' d L lo hi (b : Z) (Lst : list (Z * Z)),
  pb8b_keep rd rd' d L lo hi -> pf_sl rd b Lst ->
  Forall (fun ov => 0 <= b + fst ov /\ b + fst ov + 8 <= 2 ^ 64 /\
                    pb8b_apart (b + fst ov) 8 d L lo hi) Lst ->
  pf_sl rd' b Lst.
Proof.
intros rd rd' d L lo hi b Lst K H HB. unfold pf_sl in *. apply Forall_forall. intros ov Hin. cbv beta.
destruct (proj1 (Forall_forall _ _) HB ov Hin) as (B0 & B1 & BA).
rewrite (pb8b_rdword rd rd' d L lo hi _ K B0 B1 BA). exact (proj1 (Forall_forall _ _) H ov Hin).
Qed.
Lemma pb8b_pf_saved : forall rd rd' d L lo hi (sp0 : Z) (regs : bvmap 5 word),
  pb8b_keep rd rd' d L lo hi -> pf_saved rd sp0 regs -> 0 <= sp0 - 104 -> sp0 <= 2 ^ 64 ->
  pb8b_apart (sp0 - 104) 104 d L lo hi -> pf_saved rd' sp0 regs.
Proof.
intros rd rd' d L lo hi sp0 regs K H H0 H1 A j r Hj.
assert (Hl : (j < length PF_SAVED)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
unfold PF_SAVED in Hl. cbn [length] in Hl. destruct A as [A1 A2].
rewrite (pb8b_rdword rd rd' d L lo hi (sp0 - 8 - 8 * Z.of_nat j) K);
  [exact (H j r Hj) | lia | lia | split; lia].
Qed.
Lemma pb8b_pf_fsh : forall rd rd' d L lo hi (sh : Z) (sc : pf_scope),
  pb8b_keep rd rd' d L lo hi -> pf_fsh rd sh sc -> 0 <= sh -> sh + 144 <= 2 ^ 64 ->
  pb8b_apart sh 144 d L lo hi -> pf_fsh rd' sh sc.
Proof.
intros rd rd' d L lo hi sh sc K H H0 H1 A i Hi.
rewrite (pb8b_keep_in rd rd' d L lo hi sh 144 (sh + i) K A H0 H1) by lia. exact (H i Hi).
Qed.
Lemma pb8b_pf_nm : forall rd rd' d L lo hi (a : Z) (nm : list Z),
  pb8b_keep rd rd' d L lo hi -> pf_nm rd a nm -> 0 <= a -> a + 16 <= 2 ^ 64 ->
  pb8b_apart a 16 d L lo hi -> pf_nm rd' a nm.
Proof.
intros rd rd' d L lo hi a nm K (f & Hb & He) H0 H1 A. exists f. split; [|exact He].
destruct He as [Hl _].
apply (pb8b_sa_bytes rd rd' d L lo hi a f K Hb H0); rewrite Hl; [lia | exact A].
Qed.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
(* the instance's read-only range is .data.rel.ro .. .got (SegObj.v); needed by pb8b_arodata only *)
Hypothesis VRO : seg_val_relro (PI := PI).

(** ** Image facts *)
(* the image bytes: neither written range holds one *)
Definition pb8b_noimg (d L lo hi : Z) : Prop :=
  forall x, in_img SEGS x -> ~ (d <= x < d + L) /\ ~ (lo <= x < hi).

Lemma pb8b_keep_img : forall rd rd' d L lo hi x,
  pb8b_keep rd rd' d L lo hi -> pb8b_noimg d L lo hi -> in_img SEGS x -> rd' x = rd x.
Proof.
intros rd rd' d L lo hi x K NI Hx. destruct (NI x Hx) as [N1 N2].
pose proof (pa_segs_low x Hx) as Hb. pose proof pb8b_consts as (_ & _ & _ & E4 & E64).
unfold pb8b_keep in K. apply K; [lia | exact N1 | exact N2].
Qed.
(* sa_lit: its bytes and NUL are image bytes (sa_img), its slack is ROM (sa_romtail), hence image bytes too;
   sa_pinned, sa_romtail and sa_img do not read the reader *)
Lemma pb8b_sa_lit : forall rd rd' d L lo hi a (s : list Z),
  pb8b_keep rd rd' d L lo hi -> pb8b_noimg d L lo hi -> pb8b_noshadow d L lo hi ->
  sa_lit SEGS B rd a s -> sa_lit SEGS B rd' a s.
Proof.
intros rd rd' d L lo hi a s K NI _ (H0 & ((Hz & Hn) & Ht) & Hp & Hr & Hi).
assert (Ie : in_img SEGS (a + Z.of_nat (length s)))
  by exact (proj1 (Hi (a + Z.of_nat (length s)) ltac:(lia))).
pose proof (pa_segs_low _ Ie) as Re. pose proof pb8b_consts as (_ & _ & _ & E4 & E64).
split; [exact H0|]. split; [|split; [exact Hp | split; [exact Hr | exact Hi]]].
split; [split; [|exact Hn]|].
- intros i Hi'. pose proof Hi' as Hl. rewrite length_app in Hl. cbn [length] in Hl.
  rewrite (pb8b_keep_img rd rd' d L lo hi (a + Z.of_nat i) K NI); [exact (Hz i Hi')|].
  exact (proj1 (Hi (a + Z.of_nat i) ltac:(lia))).
- intros x Hx. pose proof (Z.mod_pos_bound (a + Z.of_nat (length s)) 8 ltac:(lia)) as M.
  rewrite (pb8b_keep_img rd rd' d L lo hi x K NI); [exact (Ht x Hx)|].
  apply (YG0s.seg_rom_in_img SEGS x); [lia | exact (Hr x Hx)].
Qed.
(* sa_cat: the row words lie in the table, an image object (sa_img); the token texts are sa_lit *)
Lemma pb8b_sa_cat : forall rd rd' d L lo hi cat,
  pb8b_keep rd rd' d L lo hi -> pb8b_noimg d L lo hi -> pb8b_noshadow d L lo hi ->
  sa_cat SEGS B rd cat -> sa_cat SEGS B rd' cat.
Proof.
intros rd rd' d L lo hi cat K NI NS (Hp & Hi & Hr). split; [exact Hp|]. split; [exact Hi|].
intros i Hn. destruct (Hr i Hn) as (tp & Ew & Hl). exists tp. split.
- rewrite (pb8b_rdword_eq rd rd' (pin_spec.row_addr cat i)); [exact Ew|].
  intros x Hx. apply (pb8b_keep_img rd rd' d L lo hi x K NI). refine (proj1 (Hi x _)).
  unfold pin_spec.row_addr, pin_spec.CAT_ROW in Hx. unfold pin_spec.CAT_BYTES. unfold pin_spec.CAT_N in Hn.
  lia.
- exact (pb8b_sa_lit rd rd' d L lo hi tp _ K NI NS Hl).
Qed.
(* arodata_okP constrains only in_roP bytes; at RLO_A / RHI_A those are image bytes (VRO) *)
Lemma pb8b_arodata_gen : forall rd rd' d L lo hi RLO RHI,
  pb8b_keep rd rd' d L lo hi -> pb8b_noimg d L lo hi -> (forall a, RLO <= a < RHI -> in_img SEGS a) ->
  arodata_okP SEGS RLO RHI B rd -> arodata_okP SEGS RLO RHI B rd'.
Proof.
intros rd rd' d L lo hi RLO RHI K NI HR H a Ha H1 H2.
rewrite (pb8b_keep_img rd rd' d L lo hi a K NI); [exact (H a Ha H1 H2)|].
destruct Ha as [(sg & Hsg & _ & Hr) | Hr]; [exists sg; split; [exact Hsg | exact Hr] | exact (HR a Hr)].
Qed.
Lemma pb8b_relro_img : forall a, RLO_A <= a < RHI_A -> in_img SEGS a.
Proof.
intros a Ha. destruct VRO as [Hlo Hhi]. apply pa_relro_img. rewrite Hlo, Hhi.
unfold RLO_A, RHI_A, SEG_RLO, SEG_RHI in Ha. lia.
Qed.
Lemma pb8b_arodata : forall rd rd' d L lo hi,
  pb8b_keep rd rd' d L lo hi -> pb8b_noimg d L lo hi ->
  arodata_okP SEGS RLO_A RHI_A B rd -> arodata_okP SEGS RLO_A RHI_A B rd'.
Proof.
intros rd rd' d L lo hi K NI. exact (pb8b_arodata_gen rd rd' d L lo hi RLO_A RHI_A K NI pb8b_relro_img).
Qed.

(** ** The caller's objects (pf_obj), conjunct by conjunct *)
Lemma pb8b_pf_obj : forall v lyc Sc rd rd' d L lo hi,
  pb8b_keep rd rd' d L lo hi -> pb8b_noimg d L lo hi -> pb8b_noshadow d L lo hi ->
  pf_obj B v lyc Sc rd ->
  0 <= p_t v -> p_t v + Z.of_nat (length (p_s v)) + 8 < kHighMemEnd ->
  0 <= p_c v -> p_c v + seg_spec.SEG_C_SIZE < kHighMemEnd ->
  pb8b_apart (p_t v) (Z.of_nat (length (p_s v)) + 8) d L lo hi ->
  pb8b_apart gotwA 8 d L lo hi -> pb8b_apart guardA 8 d L lo hi ->
  pf_obj B v lyc Sc rd'.
Proof.
intros v lyc Sc rd rd' d L lo hi K NI NS (O1 & O2 & O3 & O4 & O5 & O6 & O7 & O8 & O9) T0 T1 C0 C1 AT AG AH.
pose proof pb8b_consts as (_ & _ & EH & _ & E64).
unfold pf_obj. refine (conj _ (conj _ (conj O3 (conj _ (conj O5 (conj _ (conj _ (conj _ _)))))))).
- apply (pb8b_sa_str rd rd' d L lo hi _ _ K O1 T0); [lia | exact AT].
- apply (pb8b_sa_addr rd rd' d L lo hi _ _ K NS O2 T0). unfold pf_len. lia.
- exact (pb8b_sa_addr rd rd' d L lo hi _ _ K NS O4 C0 C1).
- exact (pb8b_sa_cat rd rd' d L lo hi _ K NI NS O6).
- intros x Hx. exact (pb8b_sa_lit rd rd' d L lo hi _ _ K NI NS (O7 x Hx)).
- exact (pb8b_arodata rd rd' d L lo hi K NI O8).
- apply (pb8b_sa_ssp rd rd' d L lo hi _ _ K O9);
    [unfold gotwA; lia | unfold gotwA; lia | unfold guardA; lia | unfold guardA; lia | exact AG | exact AH].
Qed.

End e. End f. End d.

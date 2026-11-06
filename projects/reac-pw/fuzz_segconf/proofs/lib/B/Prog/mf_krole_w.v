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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v; 790 of its 852 lines of code are new or changed and 391 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan-ubsan (image B, pin c3796c0b38f3, 0x86140), segment S_MF_KROLE, piece kr_s_words: the
   words loop of m_key's role branch, 0x86758 .. 0x8679c (lib/B/Prog/mf_krole_m.v KR_WORDS_stmt): pass i of five goes
   to KR_HIT, to the next pass (KR_WORDS at i + 1) or, after word 4, to KR_MISS. A sub-lane of a walk lane
   of the image-B m_file-family owner's G2B. proves no function (kind: segment lemma of m_file's image-B walk, S_MF_KROLE piece
   kr_s_words). Adapted from image A's lib/A/Prog/m_file_s_krole_w.v (a working branch) at image B's
   registers, pcs and numbers.

   THE CODE (listing m_file.fuzz_segconf.asan-ubsan.s lines 392-409), pass i, with s4 = -4 i, s9 = &role[i],
   s5 = s8 = &words[i], s7 = shadow(&words[i]) = SHADOW_OFF + WORDS / 8 + i, s10 = ln, s11 = line + 1:
     0x86758 lbu a0,0(s7); 0x8675c bnez a0 -> 0x86ec0   the instrumented check of words[i] (a load of its shadow
                                                        byte and a compare; the error path is not reached)
     0x86760 ld s6,0(s8); 0x86764 mv a0,s6; 0x86768 jal strlen's wrapper    wp = words[i]
     0x8676c bne a0,s10 -> 0x86784                      |word i| <> ln: the next pass
     0x86770 mv a0,s6; 0x86774 ld a1,144(s1); 0x86778 mv a2,s10; 0x8677c jal bcmp's wrapper   bcmp(wp, low, ln)
     0x86780 beqz a0 -> 0x868c8                         equal: KR_HIT
     0x86784-0x86794 s4 -= 4, s9 += 4, s5 += 8, s7 += 1, s8 += 8; 0x86798 li a0,-20;
     0x8679c bne s4,a0 -> 0x86758 (KR_WORDS, pass i + 1), else 0x867a0 (KR_MISS)
   THE PROOF: one lemma per program point of a pass, KR_WORDS (kw_head_ok), KW_R1 0x8676c (kw_r1_ok), KW_R2 0x86780
   (kw_r2_ok), KW_NEXT 0x86784 (kw_next_ok), each seeded with a light symbolic state (every register its own atom,
   atom 32 one extra value, at most two read-only regions). The check of words[i] is not the shape the token
   executor recognises (s7 is a cursor, not (x >> 3) + s2): its shadow byte is loaded from a one-byte read-only
   region at atom 23 (s7) holding 0, which it is because m_key.words (0xa2040) is 8-aligned and addressable
   (m_file_c.v mf_words' sa_pinned at the current AR, through m_file_k.v mf_words_now); words[i] from an 8-byte
   read-only region at atom 24 (s8). The two wrapper calls are stepped by PaArt.aj_art_at with ASTRLEN
   (kw_strlen_call) and YCbq.aj_bcmp_at with ABCMP (kw_bcmp_call); each returns at the Section's FP state. The cut
   facts are carried across every step by m_file_k.v's mf_keep_win0 (kw_keep). The loop is closed by induction on
   the passes left (kw_all), with mf_krole_m.v's kr_word_go_step / kr_word_go_5 / kr_wtest_iff.
   IMAGE B AGAINST IMAGE A: registers s4 / s9 / s5 = s8 / s7 / s10 / s11 (A: s11 / s7 / s10 / s8 / s4 and line + 1 in
   96(s1)); the shadow region at atom 23 and the words region at atom 24 (A 24 / 26); low at 144(s1) (A 152(s1));
   s1 = sp0 - 320 or sp0 - 336 (A 288 / 304); STK_m_file = 8,592 (A 8,560); WORDS = 0xa2040 (A 0xa1880); mf_cells
   has 16 cells (A 14); kr_regs_b has 7 registers (A 8).
   Section hypotheses (the owner's list): TL (the errno cell's placement aj_art_at reads), ASTRLEN, ABCMP. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0n YI0s YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList SegAddr SegPa.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPaLib PaLibG PaLibH PaSB PaDenot PaLibF PaCall PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaArt.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require RtString.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegObj SegGlob SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import m_file_c m_file_m mf_krole_m m_file_k.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require SegInstB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ===================================== the program points ===================================== *)
Definition KW_R1 : Z := AF_m_file + 0x62c.     (* 0x8676c, strlen's return *)
Definition KW_R2 : Z := AF_m_file + 0x640.     (* 0x86780, bcmp's return *)
Definition KW_NEXT : Z := AF_m_file + 0x644.   (* 0x86784, the next pass *)

(* ===================================== the symbolic states ===================================== *)
(* every register its own atom, atom 32 one extra value, no fact *)
Definition kw_facts : facts := mkFacts [] [] [].
Definition kw_ss (pc : Z) (rs : smem) : sstate := mkSS pc sr_atoms rs None kw_facts.
(* at 0x86758: the shadow byte of words[i] at s7 (0) and words[i] at s8 (atom 32 = wp) *)
Definition kwA_regions : smem :=
[ YP09.mkRegion (Some 23%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 0))];
  YP09.mkRegion (Some 24%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))] ].
(* at 0x8676c: the cell 144(s1) (atom 32 = low = FB + 32) *)
Definition kwB_regions : smem :=
[ YP09.mkRegion (Some 9%nat) 144 152 0 0 [YP09.mkChunk 144 (CVal 8 (SOff 32 0))] ].
(* the shadow base of the token runs: s2 *)
Definition kw_Bx : sv := SOff 18 0.
(* the registers a pass reads and keeps: kr_regs_b's, s10 = ln, s11 = line + 1; and the cursors s4, s5, s7, s8, s9 *)
Definition KW_KEPT : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 26; 27]%bv.
Definition KW_KEPT4 : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 20; 21; 23; 24; 25; 26; 27]%bv.

(* ===================================== pure facts ===================================== *)
Lemma kw_line_len : forall rest, (length (mf_line rest) <= length rest)%nat.
Proof.
intros rest. unfold mf_line. induction rest as [|b r IH]; [cbn; lia|]. cbn [break_nl].
destruct (b =? NL); [cbn; lia|]. destruct (break_nl r) as [l q]. cbn [fst length] in *. lia.
Qed.
(* the value v = the bytes [ov, ov + vl) of the text left has vl bytes *)
Lemma kw_vv_len : forall rest ok kl ov vl k vv, mk_kv rest ok kl ov vl k vv -> length vv = vl.
Proof.
intros rest ok kl ov vl k vv (_ & H2 & _ & H4). subst vv. rewrite length_firstn, length_skipn.
pose proof (kw_line_len rest). lia.
Qed.
Lemma kw_low_len : forall rest ok kl ov vl k vv, mk_kv rest ok kl ov vl k vv -> length (kr_low vv) = kr_ln vl.
Proof. intros rest ok kl ov vl k vv H. rewrite kr_low_length. f_equal. exact (kw_vv_len _ _ _ _ _ _ _ H). Qed.
Lemma kw_ln_le : forall vl, (kr_ln vl <= 63)%nat.
Proof. intros vl. unfold kr_ln. lia. Qed.
(* the five role words: 3 to 6 bytes, each a byte value *)
Lemma kw_words_len : forall i, (i < 5)%nat -> (3 <= length (nth i MF_ROLE_WORDS []) <= 6)%nat.
Proof.
intros i Hi.
do 5 (destruct i as [|i];
  [ lazymatch goal with |- context [length ?x] =>
      let l := eval vm_compute in (length x) in change (length x) with l end; lia
  | ]).
lia.
Qed.
Lemma kw_words_zs : forall i, (i < 5)%nat ->
  seg_spec.zs (seg_spec.zb (nth i MF_ROLE_WORDS [])) = nth i MF_ROLE_WORDS [].
Proof. intros i Hi. do 5 (destruct i as [|i]; [vm_compute; reflexivity|]). lia. Qed.
(* the reader's bytes of two lists of one length agree exactly when the lists are equal *)
Lemma kw_bytes_eq : forall (rd : reader) x y (l1 l2 : list Z),
  length l1 = length l2 -> sa_zs rd x l1 -> sa_zs rd y l2 ->
  ((forall j, 0 <= j < Z.of_nat (length l1) -> rd (x + j) = rd (y + j)) <-> l1 = l2).
Proof.
intros rd x y l1 l2 HL H1 H2. split.
- intros H. apply nth_ext with (d := 0) (d' := 0); [exact HL|].
  intros j Hj. pose proof (H (Z.of_nat j) ltac:(lia)) as E.
  rewrite (H1 j Hj), (H2 j ltac:(lia)) in E. injection E as E. exact E.
- intros <- j Hj. replace j with (Z.of_nat (Z.to_nat j)) by lia.
  rewrite (H1 (Z.to_nat j) ltac:(lia)), (H2 (Z.to_nat j) ltac:(lia)). reflexivity.
Qed.
Lemma kw_zs_prefix : forall (rd : reader) a (l l' : list Z), sa_zs rd a (l ++ l') -> sa_zs rd a l.
Proof.
intros rd a l l' H i Hi. rewrite (H i ltac:(rewrite length_app; lia)). rewrite app_nth1 by lia. reflexivity.
Qed.
(* the shadow byte of words[i]: m_key.words (image B 0xa2040) is 8-aligned, so word i's granule is the shadow byte
   SHADOW_OFF + WORDS / 8 + i, and its last byte WORDS + 8 i + 7 addressable makes that byte 0 *)
Lemma kw_words_shadow : forall (rd : reader) i, (i < 5)%nat ->
  range_addressable rd SHADOW_OFF SegInstB.wordsA 40 ->
  rd (SHADOW_OFF + SegInstB.wordsA / 8 + Z.of_nat i) = Some 0.
Proof.
intros rd i Hi HRA.
assert (HW8 : SegInstB.wordsA / 8 = 82952) by reflexivity.
assert (HWv : SegInstB.wordsA = 663616) by reflexivity.
rewrite HW8. rewrite HWv in HRA.
destruct (HRA (663616 + 8 * Z.of_nat i + 7) ltac:(lia)) as (s & Hs & Hok).
unfold shadow_of_addr in Hs.
replace ((663616 + 8 * Z.of_nat i + 7) / 8) with (82952 + Z.of_nat i) in Hs
  by (apply Z.div_unique with 7; lia).
rewrite Z.add_assoc in Hs.
destruct Hok as [-> | Hlt]; [exact Hs|].
exfalso. replace ((663616 + 8 * Z.of_nat i + 7) mod 8) with 7 in Hlt
  by (apply Z.mod_unique with (82952 + Z.of_nat i); lia). lia.
Qed.
(* a shadow hull of a sub-range *)
Lemma kw_hull_sub : forall (rd : reader) x n m, 0 < n -> n <= m -> 0 <= x ->
  shadow_hull_vis rd x m -> shadow_hull_vis rd x n.
Proof.
intros rd x n m Hn Hm Hx HH s Hs. apply HH. split; [lia|].
assert (shadow_addr (x + n - 1) <= shadow_addr (x + m - 1))
  by (unfold shadow_addr; apply Z.add_le_mono_l; apply Z.div_le_mono; lia).
assert (shadow_addr (x + n - 1) / 8 * 8 <= shadow_addr (x + m - 1) / 8 * 8)
  by (apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; lia).
lia.
Qed.
(* s1 - sp0 (-320 or -336 at image B) is a multiple of 16 *)
Lemma kw_o16 : forall sp0 s1, s1 = sp0 - 320 \/ s1 = sp0 - 336 -> (s1 - sp0) mod 16 = 0.
Proof.
intros sp0 s1 [-> | ->].
- replace (sp0 - 320 - sp0) with (-20 * 16) by lia. apply Z_mod_mult.
- replace (sp0 - 336 - sp0) with (-21 * 16) by lia. apply Z_mod_mult.
Qed.
(* a register value plus a constant *)
Lemma kw_bv_off : forall x c, Z_to_bv 64 (bv_unsigned (Z_to_bv 64 x) + c) = Z_to_bv 64 (x + c).
Proof.
intros x c. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. rewrite Zplus_mod_idemp_l. reflexivity.
Qed.
Lemma kw_pres_reg : forall regs regs' (r : bv 5), aregs_preserved regs regs' -> acallee_saved (bv_unsigned r) ->
  getr regs' r = getr regs r.
Proof. intros regs regs' r HP Hr. rewrite <- (Z_to_bv_bv_unsigned 5 r). exact (HP _ Hr). Qed.
Ltac kw_csav := unfold acallee_saved;
  lazymatch goal with |- context [bv_unsigned ?x] =>
    let z := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with z end; lia.
Lemma kw_ag32 : forall (regs1 : bvmap 5 word) extra E0 E,
  env_agree 32 (Ereg regs1 extra) E0 -> env_agree 34 E0 E -> env_agree 32 (Ereg regs1 extra) E.
Proof. intros regs1 extra E0 E H0 H1. eapply env_agree_trans; [exact H0 | eapply env_agree_le; [|exact H1]; lia]. Qed.
Lemma kw_ag_ew : forall E0 E n x, env_agree 34 E0 E -> (n < 34)%nat -> ew E0 n = x -> ew E n = x.
Proof. intros E0 E n x H Hn H0. rewrite (proj1 H n Hn). exact H0. Qed.

(* a run that writes nothing (every region read-only) keeps every byte's view *)
Ltac kw_awr :=
  lazymatch goal with |- awr_ok _ _ _ ?rs _ _ _ _ _ _ _ _ => let rs' := eval vm_compute in rs in change rs with rs' end;
  repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ seg_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
#[local] Notation WORDS := SegInstB.wordsA.
#[local] Notation ROLES := SegInstB.rolesA.

Lemma kw_keep_step : forall E rs (m0 m m' : word -> option byte) (H : word -> bool),
  frame_of E rs (mrestrict H m) (mrestrict H m') ->
  forallb (fun t => match t with (_, wlo, whi) => whi <=? wlo end) (windows rs) = true ->
  (forall a, 0 <= a < 2 ^ 64 -> aview SEGS H m a = aview SEGS H m0 a) ->
  forall a, 0 <= a < 2 ^ 64 -> aview SEGS H m' a = aview SEGS H m0 a.
Proof.
intros E rs m0 m m' H HFr Hw KM a Ha.
rewrite (kept_of_frame (segs := SEGS) E rs H m m' (fun _ => False) HFr); [exact (KM a Ha) | | exact Ha | intros []].
intros b wlo whi a' Hin Hr. rewrite forallb_forall in Hw. pose proof (Hw _ Hin) as Hb. cbn in Hb.
apply Z.leb_le in Hb. lia.
Qed.

(* after a run: the environment agrees with the seed's E0 below 34 (HAE), the memory keeps every view (KM) *)
Ltac kw_after E0 HAE KM :=
  try (let mdv := fresh "mdv" in set (mdv := with_vm_backing _ _ _) in *; clearbody mdv);
  lazymatch goal with
  | HFr : frame_of ?Eo _ (mrestrict _ _) (mrestrict _ _) |- _ =>
    let HAEn := fresh "HAEn" in let KMn := fresh "KMn" in
    lazymatch goal with
    | HS : st_ok_pi _ _ ?En _ _ |- _ => assert (HAEn : env_agree 34 E0 En) by (env_agree_chain HAE)
    | HS : st_ok _ ?En _ _ |- _ => assert (HAEn : env_agree 34 E0 En) by (env_agree_chain HAE)
    end;
    pose proof (kw_keep_step Eo _ _ _ _ _ HFr ltac:(vm_compute; reflexivity) KM) as KMn;
    clear HFr HAE KM; rename HAEn into HAE; rename KMn into KM;
    repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end
  end.

(* the environment of a seed *)
Definition kw_E (regs1 : bvmap 5 word) (x : Z) : env := Eimg (Ereg regs1 [Z_to_bv 64 x]).
Lemma kw_ew_reg : forall regs1 x n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (kw_E regs1 x) n = getr regs1 r.
Proof.
intros regs1 x n r Hn. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
unfold kw_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn.
Qed.
Lemma kw_ew32 : forall regs1 x, ew (kw_E regs1 x) 32 = Z_to_bv 64 x.
Proof. intros. unfold kw_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs1 _ 0). Qed.
Lemma kw_env_agree : forall regs1 x, env_agree 32 (Ereg regs1 [Z_to_bv 64 x]) (kw_E regs1 x).
Proof. intros. split; [intros n Hn; unfold kw_E; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity]. Qed.

(* the seeds *)
Lemma kw_seed0 : forall (W : world SEGS) regs1 memc pc x,
  st_ok_pi SEGS VAL (kw_E regs1 x) (kw_ss pc [])
    (restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + pc)) memc (seg_rom SEGS))).
Proof.
intros W regs1 memc pc x. rewrite restrict_mkst_fx. unfold kw_ss. apply pa_entry_st_ok_full.
- unfold kw_E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- constructor.
- apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint]. exact I.
- split; [exact I | split; exact I].
Qed.
Lemma kw_seedA : forall (W : world SEGS) regs1 memc i wp, (i < 5)%nat ->
  getr regs1 23 = w64 (SHADOW_OFF + WORDS / 8 + Z.of_nat i) -> getr regs1 24 = w64 (WORDS + 8 * Z.of_nat i) ->
  rdW W memc (SHADOW_OFF + WORDS / 8 + Z.of_nat i) = Some 0 ->
  rdword (rdW W memc) (WORDS + 8 * Z.of_nat i) = Some wp -> 0 <= wp < 2 ^ 64 ->
  st_ok_pi SEGS VAL (kw_E regs1 wp) (kw_ss KR_WORDS kwA_regions)
    (restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + KR_WORDS)) memc (seg_rom SEGS))).
Proof.
intros W regs1 memc i wp Hi R23 R24 Hsh Hw Hwp.
assert (HW8 : WORDS / 8 = 82952) by reflexivity.
assert (HWv : WORDS = 663616) by reflexivity.
assert (E23 : ew (kw_E regs1 wp) 23 = getr regs1 23) by (apply kw_ew_reg; reflexivity).
assert (E24 : ew (kw_E regs1 wp) 24 = getr regs1 24) by (apply kw_ew_reg; reflexivity).
pose proof (kw_ew32 regs1 wp) as E32.
assert (B23 : base_val (kw_E regs1 wp) (Some 23%nat) = SHADOW_OFF + WORDS / 8 + Z.of_nat i)
  by (cbn [base_val]; rewrite E23, R23; unfold w64; apply unsigned_lit_small; rewrite HW8; unfold SHADOW_OFF; lia).
assert (B24 : base_val (kw_E regs1 wp) (Some 24%nat) = WORDS + 8 * Z.of_nat i)
  by (cbn [base_val]; rewrite E24, R24; unfold w64; apply unsigned_lit_small; rewrite HWv; lia).
rewrite restrict_mkst_fx. unfold kw_ss. apply pa_entry_st_ok_full.
- unfold kw_E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold kwA_regions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + rewrite B23. split; [rewrite HW8; unfold SHADOW_OFF; lia|]. split; [rewrite HW8; unfold SHADOW_OFF; lia|].
    split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS (kw_E regs1 wp) _ _ 0 1 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia |].
    rewrite Z.add_0_r. exact (mf_val1_of_aview (w_H W) memc _ 0 Hsh).
  + rewrite B24. split; [rewrite HWv; lia|]. split; [rewrite HWv; lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS (kw_E regs1 wp) _ _ 0 8 (SOff 32 0) wp);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Hw).
- apply pairwise_disjoint_of_extents. unfold kwA_regions, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite B23, B24, HW8, HWv.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold SHADOW_OFF. repeat split; lia.
- split; [exact I | split; exact I].
Qed.
Lemma kw_seedB : forall (W : world SEGS) regs1 memc s1 y,
  getr regs1 9 = w64 s1 -> 0 <= s1 -> s1 + 152 <= 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  val_mem SEGS (mrestrict (w_H W) memc) (s1 + 144) 8 y ->
  st_ok_pi SEGS VAL (kw_E regs1 y) (kw_ss KW_R1 kwB_regions)
    (restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + KW_R1)) memc (seg_rom SEGS))).
Proof.
intros W regs1 memc s1 y R9 Hs0 Hs1 Hy V.
assert (E9 : ew (kw_E regs1 y) 9 = getr regs1 9) by (apply kw_ew_reg; reflexivity).
pose proof (kw_ew32 regs1 y) as E32.
assert (B9 : base_val (kw_E regs1 y) (Some 9%nat) = s1)
  by (cbn [base_val]; rewrite E9, R9; unfold w64; apply unsigned_lit_small; lia).
rewrite restrict_mkst_fx. unfold kw_ss. apply pa_entry_st_ok_full.
- unfold kw_E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold kwB_regions. constructor; [|constructor]. unfold region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite B9.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val SEGS (kw_E regs1 y) _ s1 144 8 (SOff 32 0) y);
    [cbn [sv_denot]; rewrite E32, Z.add_0_r, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia | exact V].
- apply pairwise_disjoint_of_extents. unfold kwB_regions, extent_of_region.
  cbn [map zpairwise_disjoint zall_disjoint]. tauto.
- split; [exact I | split; exact I].
Qed.

(* the C string of a literal in RtDefs' form *)
Lemma kw_astr : forall (W : world SEGS) mem a (s : list byte),
  sa_strz (rdW W mem) a (seg_spec.zs s) -> astr_at SEGS W mem a s.
Proof.
intros W mem a s [Hz Hn]. apply astr_atR_view. split.
- intros k Hk. rewrite length_app in Hk. cbn [length] in Hk.
  assert (Hk' : (k < length (seg_spec.zs s ++ [0%Z]))%nat)
    by (unfold seg_spec.zs; rewrite length_app, length_map; cbn [length]; lia).
  rewrite (Hz k Hk'). f_equal.
  replace (seg_spec.zs s ++ [0]) with (map bv_unsigned (s ++ [Z_to_bv 8 0]))
    by (unfold seg_spec.zs; rewrite map_app; reflexivity).
  rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map, length_app; cbn [length]; lia).
  apply map_nth.
- intros Hin. apply Hn. unfold seg_spec.zs. change 0 with (bv_unsigned (Z_to_bv 8 0)). apply in_map. exact Hin.
Qed.
(* low.i [FB + 32, FB + 32 + n) is addressable: its eight shadow bytes are MF_LOW_ON = 0 *)
Lemma kw_low_ra : forall (Wc : world SEGS) memc F n,
  F mod 32 = 0 -> 0 <= F -> 0 <= n <= 64 ->
  (forall i, 4 <= i < 12 -> val_mem SEGS (mrestrict (w_H Wc) memc) (SHADOW_OFF + F / 8 + i) 1 MF_LOW_ON) ->
  range_addressable (rdW Wc memc) SHADOW_OFF (F + 32) n.
Proof.
intros Wc memc F n HF HF0 Hn VSH x Hx. exists 0. split; [|left; reflexivity].
unfold shadow_of_addr.
pose proof (Z.div_mod F 32 ltac:(lia)) as DF. rewrite HF, Z.add_0_r in DF.
assert (HF8 : F / 8 = 4 * (F / 32)).
{ rewrite DF at 1. replace (32 * (F / 32)) with ((4 * (F / 32)) * 8) by lia. apply Z.div_mul. lia. }
assert (Hx1 : 4 * (F / 32) + 4 <= x / 8) by (apply Z.div_le_lower_bound; lia).
assert (Hx2 : x / 8 < 4 * (F / 32) + 12) by (apply Z.div_lt_upper_bound; lia).
pose proof (VSH (x / 8 - F / 8) ltac:(lia) 0%nat ltac:(lia)) as V.
change (Z.of_nat 0) with 0 in V. rewrite Z.add_0_r in V.
replace (SHADOW_OFF + F / 8 + (x / 8 - F / 8)) with (SHADOW_OFF + x / 8) in V by lia.
unfold aview. rewrite V. reflexivity.
Qed.

Section e.
Variable B : asyms.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Hypothesis TL : PALib B.
Hypothesis ASTRLEN : forall fx0 : YK11.FPState,
  @RtString.astrlen_realizes fx0 rc SEGS B (SIGMA SS___interceptor_trampoline_strlen).
Hypothesis ABCMP : forall fx0 : YK11.FPState, @abcmp_realizes fx0 rc SEGS B (SIGMA SS___interceptor_trampoline_bcmp).
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let errno_low := pal_env B TL.

(* low.i's shadow hull: inside the frame's 16 shadow bytes, which AR maps *)
Lemma kw_low_hull : forall lyc Sc (Wc : world SEGS) memc mdc pos n,
  AR SEGS B lyc Sc Wc memc mdc -> In (1, pos) (frames Sc) -> 0 < n <= 64 ->
  shadow_hull_vis (rdW Wc memc) (frame_addr lyc 1 pos + 32) n.
Proof.
intros lyc Sc Wc memc mdc pos n HAR Hin Hn s Hs.
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 pos HAR Hin) as (HF & _ & _ & HFS).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 1 pos HAR Hin) as (HF4096 & _ & _).
change (fs_frame_bytes 1) with 128 in HFS.
remember (frame_addr lyc 1 pos) as F eqn:EF. clear EF.
pose proof (Z.div_mod F 32 ltac:(lia)) as DF. rewrite HF, Z.add_0_r in DF.
remember (F / 32) as q eqn:Eq.
assert (HF8 : F / 8 = 4 * q).
{ rewrite DF. replace (32 * q) with ((4 * q) * 8) by lia. apply Z.div_mul. lia. }
assert (H1 : (F + 32) / 8 = 4 * q + 4).
{ rewrite DF. replace (32 * q + 32) with ((4 * q + 4) * 8) by lia. apply Z.div_mul. lia. }
assert (H2 : (F + 32 + n - 1) / 8 < 4 * q + 12) by (apply Z.div_lt_upper_bound; lia).
unfold shadow_addr in Hs, HFS. rewrite H1 in Hs. rewrite HF8 in HFS.
remember ((F + 32 + n - 1) / 8) as y eqn:Ey.
pose proof (Z.div_mod (SHADOW_OFF + (4 * q + 4)) 8 ltac:(lia)) as D1.
pose proof (Z.mod_pos_bound (SHADOW_OFF + (4 * q + 4)) 8 ltac:(lia)) as M1.
pose proof (Z.div_mod (SHADOW_OFF + y) 8 ltac:(lia)) as D2.
pose proof (Z.mod_pos_bound (SHADOW_OFF + y) 8 ltac:(lia)) as M2.
apply (aview_some_of_apresent SEGS).
replace s with (SHADOW_OFF + 4 * q + (s - (SHADOW_OFF + 4 * q))) by lia.
apply (proj1 (HFS (s - (SHADOW_OFF + 4 * q)) ltac:(change (128 / 8) with 16; unfold SHADOW_OFF in *; lia))).
Qed.

(* a literal lies in the image, below the allocator's ceiling and the stack *)
Lemma kw_lit_low : forall rd wp w, sa_lit SEGS B rd wp w -> 0 < wp /\ wp + Z.of_nat (length w) + 1 <= kImgEnd.
Proof.
intros rd wp w (H0 & _ & _ & _ & HI). split; [exact H0|].
destruct (HI (wp + Z.of_nat (length w)) ltac:(lia)) as (I1 & _).
pose proof (pa_img_range _ I1). lia.
Qed.
(* a literal at a memory that agrees below lo, lo above the image *)
Lemma kw_lit_keep : forall (Wc : world SEGS) memc mem2 wp w lo,
  sa_lit SEGS B (rdW Wc memc) wp w -> kImgEnd <= lo ->
  (forall a, 0 <= a < lo -> rdW Wc mem2 a = rdW Wc memc a) ->
  sa_lit SEGS B (rdW Wc mem2) wp w.
Proof.
intros Wc memc mem2 wp w lo HL Hlo K.
pose proof (kw_lit_low _ _ _ HL) as [Hw0 Hw1].
destruct HL as (H0 & ((HZ & HN) & HT) & HP & HR & HI).
split; [exact H0|]. split; [|split; [exact HP | split; [exact HR | exact HI]]].
split; [split; [|exact HN] | apply sa_tail_of_romtail; exact HR].
intros j Hj. pose proof Hj as Hj'. rewrite length_app in Hj'. cbn [length] in Hj'.
rewrite K by lia. exact (HZ j Hj).
Qed.

(* the facts of a pass that live in memory: the KDISP facts, low.i and its NUL *)
Definition kw_mem n v lyc Sc Wc memc mdc pos mcc gi line p rest ok kl ov vl k vv : Prop :=
kr_cx B n v lyc Sc Wc memc mdc pos mcc gi line p rest ok kl ov vl k vv /\
kr_low_at lyc pos Wc memc (kr_low vv ++ [0]).
(* the registers of pass i *)
Definition kw_regs (v : mfv) (regs1 : bvmap 5 word) (vl : nat) (line : Z) (i : nat) : Prop :=
kr_regs_b B v regs1 /\ getr regs1 26 = w64 (Z.of_nat (kr_ln vl)) /\ getr regs1 27 = w64 (line + 1) /\
getr regs1 20 = w64 (- (4 * Z.of_nat i)) /\ getr regs1 25 = w64 (ROLES + 4 * Z.of_nat i) /\
getr regs1 21 = w64 (WORDS + 8 * Z.of_nat i) /\ getr regs1 24 = w64 (WORDS + 8 * Z.of_nat i) /\
getr regs1 23 = w64 (SHADOW_OFF + WORDS / 8 + Z.of_nat i).

Lemma kw_regs_b_kept : forall v (regs1 regs2 : bvmap 5 word), kr_regs_b B v regs1 ->
  (forall r, In r KW_KEPT -> getr regs2 r = getr regs1 r) -> kr_regs_b B v regs2.
Proof.
intros v regs1 regs2 (R2 & R3 & R4 & R8 & R9 & R18 & R19) HK.
unfold kr_regs_b. rewrite !HK by (cbv [KW_KEPT In]; tauto). repeat split; assumption.
Qed.
Lemma kw_regs_kept : forall v (regs1 regs2 : bvmap 5 word) vl line i, kw_regs v regs1 vl line i ->
  (forall r, In r KW_KEPT4 -> getr regs2 r = getr regs1 r) -> kw_regs v regs2 vl line i.
Proof.
intros v regs1 regs2 vl line i ((R2 & R3 & R4 & R8 & R9 & R18 & R19) & R26 & R27 & R20 & R25 & R21 & R24 & R23) HK.
unfold kw_regs, kr_regs_b. rewrite !HK by (cbv [KW_KEPT4 In]; tauto). repeat split; assumption.
Qed.
Lemma kw_regs_pres : forall v (regs1 regs2 : bvmap 5 word) vl line i, kw_regs v regs1 vl line i ->
  aregs_preserved regs1 regs2 -> kw_regs v regs2 vl line i.
Proof.
intros v regs1 regs2 vl line i RG HP. apply (kw_regs_kept v regs1 regs2 vl line i RG).
intros r Hr. apply kw_pres_reg; [exact HP|].
cbv [KW_KEPT4 In] in Hr. repeat (destruct Hr as [<- | Hr]; [kw_csav|]). destruct Hr.
Qed.

(* every memory fact of a pass across a step that changes no byte outside a window [wlo, whi) below s1 *)
Lemma kw_keep : forall n v lyc Sc Wc memc mdc pos mcc gi line p rest ok kl ov vl k vv mem2 md2 wlo whi,
  kw_mem n v lyc Sc Wc memc mdc pos mcc gi line p rest ok kl ov vl k vv ->
  ajournal SEGS B SegInstB.STK_m_file (mv_sp v) (M_FILE_FP (mv_c v) (mv_k0 v) (mf_final v)) (mv_ly v) (mv_S v)
    (mv_W v) (mv_mem v) (mv_md v) [(1, pos)] lyc Sc Wc mem2 md2 0 ->
  mv_sp v - SegInstB.STK_m_file <= wlo -> whi <= mf_s1 (mv_sp v) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (wlo <= a < whi) -> rdW Wc mem2 a = rdW Wc memc a) ->
  kw_mem n v lyc Sc Wc mem2 md2 pos mcc gi line p rest ok kl ov vl k vv.
Proof.
intros n v lyc Sc Wc memc mdc pos mcc gi line p rest ok kl ov vl k vv mem2 md2 wlo whi
  (CX & LOW) HJ2 Hlo Hhi K.
destruct CX as (MCX & LS & FRM & CORE & CELLS & Hn & Hr & LOOP & KV & FIN & NP & IEQ).
destruct (mf_keep_win0 B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc (Some gi) Sc Wc mem2 md2 wlo whi MCX CORE CELLS HJ2
  (Permutation_refl _) Hlo ltac:(lia) K) as (CORE2 & CELLS2 & NP2 & LOOP2).
destruct (mf_s1_facts B v MCX) as (Hs1 & _ & Hceil).
destruct (mf_sp0 B v MCX) as (_ & H47 & _).
pose proof CORE as (HJ & _). pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hfin : In (1, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 1 pos HAR Hfin) as (HF4096 & HFceil & _).
change (fs_frame_bytes 1) with 128 in HFceil.
pose proof asan_consts as (C1 & _).
assert (HSTK : SegInstB.STK_m_file = 8592) by (vm_compute; reflexivity).
pose proof (kr_low_length vv) as HLL. pose proof (kw_ln_le (length vv)) as HLn.
split.
- exact (conj MCX (conj LS (conj FRM (conj CORE2 (conj CELLS2 (conj Hn (conj Hr (conj (LOOP2 _ _ _ _ _ LOOP)
    (conj KV (conj FIN (conj (NP2 _ NP) IEQ))))))))))).
- unfold kr_low_at in *. intros j Hj. pose proof Hj as Hj'. rewrite length_app in Hj'. cbn [length] in Hj'.
  rewrite K by lia. exact (LOW j Hj).
Qed.

(* ===================================== the inner points of a pass ===================================== *)
(* 0x86758, pass i (mf_krole_m.v KR_WORDS_stmt at one i) *)
Definition KW_W_i (n i : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (gi : nat) (line p : Z) (rest : list Z) (ok kl ov vl : nat)
  (k vv : list Z),
kr_cx B n v lyc Sc Wc memc mdc pos mcc gi line p rest ok kl ov vl k vv -> kr_regs_b B v regs1 ->
(i < 5)%nat -> kr_low_at lyc pos Wc memc (kr_low vv ++ [0]) ->
word_go (skipn i MF_ROLE_WORDS) (kr_low vv) (Z.of_nat i) = h_role_word (kr_low vv) ->
getr regs1 26 = w64 (Z.of_nat (kr_ln vl)) -> getr regs1 27 = w64 (line + 1) ->
getr regs1 20 = w64 (- (4 * Z.of_nat i)) -> getr regs1 25 = w64 (ROLES + 4 * Z.of_nat i) ->
getr regs1 21 = w64 (WORDS + 8 * Z.of_nat i) -> getr regs1 24 = w64 (WORDS + 8 * Z.of_nat i) ->
getr regs1 23 = w64 (SHADOW_OFF + WORDS / 8 + Z.of_nat i) ->
mf_at B v Wc regs1 memc mdc KR_WORDS.
(* 0x8676c, strlen returned: s6 = wp = words[i], a0 = |word i| *)
Definition KW_R1_i (n i : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (gi : nat) (line p : Z) (rest : list Z) (ok kl ov vl : nat)
  (k vv : list Z) (wp : Z),
kw_mem n v lyc Sc Wc memc mdc pos mcc gi line p rest ok kl ov vl k vv -> kw_regs v regs1 vl line i -> (i < 5)%nat ->
word_go (skipn i MF_ROLE_WORDS) (kr_low vv) (Z.of_nat i) = h_role_word (kr_low vv) ->
sa_lit SEGS B (rdW Wc memc) wp (nth i MF_ROLE_WORDS []) -> getr regs1 22 = w64 wp ->
getr regs1 10 = w64 (Z.of_nat (length (nth i MF_ROLE_WORDS []))) ->
mf_at B v Wc regs1 memc mdc KW_R1.
(* 0x86780, bcmp returned: a0 = 0 exactly when word i is low's ln bytes *)
Definition KW_R2_i (n i : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (gi : nat) (line p : Z) (rest : list Z) (ok kl ov vl : nat)
  (k vv : list Z),
kw_mem n v lyc Sc Wc memc mdc pos mcc gi line p rest ok kl ov vl k vv -> kw_regs v regs1 vl line i -> (i < 5)%nat ->
word_go (skipn i MF_ROLE_WORDS) (kr_low vv) (Z.of_nat i) = h_role_word (kr_low vv) ->
(getr regs1 10 = w64 0 <-> kr_wtest (nth i MF_ROLE_WORDS []) (kr_low vv) = true) ->
mf_at B v Wc regs1 memc mdc KW_R2.
(* 0x86784, word i missed *)
Definition KW_NEXT_i (n i : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (gi : nat) (line p : Z) (rest : list Z) (ok kl ov vl : nat)
  (k vv : list Z),
kw_mem n v lyc Sc Wc memc mdc pos mcc gi line p rest ok kl ov vl k vv -> kw_regs v regs1 vl line i -> (i < 5)%nat ->
word_go (skipn i MF_ROLE_WORDS) (kr_low vv) (Z.of_nat i) = h_role_word (kr_low vv) ->
kr_wtest (nth i MF_ROLE_WORDS []) (kr_low vv) = false ->
mf_at B v Wc regs1 memc mdc KW_NEXT.

(* ===================================== the two wrapper calls ===================================== *)
(* strlen(wp) from its trampoline (0x86768): a0 = |word i| at 0x8676c, every fact kept *)
Lemma kw_strlen_call : forall n i v lyc Sc Wc rg mm mdq pos mcc gi line p rest ok kl ov vl k vv wp,
  KW_R1_i n i ->
  kw_mem n v lyc Sc Wc mm mdq pos mcc gi line p rest ok kl ov vl k vv -> kw_regs v rg vl line i -> (i < 5)%nat ->
  word_go (skipn i MF_ROLE_WORDS) (kr_low vv) (Z.of_nat i) = h_role_word (kr_low vv) ->
  sa_lit SEGS B (rdW Wc mm) wp (nth i MF_ROLE_WORDS []) -> getr rg 22 = w64 wp -> getr rg 10 = w64 wp ->
  getr rg 1 = Z_to_bv 64 (BASE + KW_R1) ->
  SRr SEGS Wc (mkCfg (mkst rg (Z_to_bv 64 (SIGMA SS___interceptor_trampoline_strlen)) mm (seg_rom SEGS)) mdq)
    (MF_POST B v).
Proof.
intros n i v lyc Sc Wc rg mm mdq pos mcc gi line p rest ok kl ov vl k vv wp R1 MEM RG Hi WG HLIT Q22 Q10 Q1.
pose proof MEM as (CX & _).
pose proof CX as (MCX & _ & _ & CORE & _).
pose proof CORE as (HJ & _). pose proof HJ as (HAR & _).
pose proof RG as ((R2 & R3 & R4 & R8 & R9 & R18 & R19) & _).
destruct (mf_s1_facts B v MCX) as (Hs1 & _ & Hceil).
destruct (mf_sp0 B v MCX) as (_ & H47 & H16).
pose proof asan_consts as (C1 & _).
assert (HSTK : SegInstB.STK_m_file = 8592) by (vm_compute; reflexivity).
assert (Hes : ESTACK = 4096) by reflexivity.
pose proof (kw_o16 (mv_sp v) (mf_s1 (mv_sp v)) Hs1) as Ho16.
assert (Hsp : spZ rg = mv_sp v + (mf_s1 (mv_sp v) - mv_sp v))
  by (unfold spZ; rewrite R2; unfold w64; rewrite unsigned_lit_small by lia; lia).
pose proof (kw_words_len i Hi) as HwL.
pose proof (kw_lit_low _ _ _ HLIT) as [Hwp0 Hwp1].
pose proof HLIT as (_ & HSTR & HPIN & HROM & _).
pose proof (HPIN _ _ _ _ _ HAR) as (A0 & A63 & AMR & ARA & AHV).
assert (HAL : astr_len (seg_spec.zb (nth i MF_ROLE_WORDS [])) = Z.of_nat (length (nth i MF_ROLE_WORDS [])))
  by (unfold astr_len, seg_spec.zb; rewrite length_map; reflexivity).
assert (HraT : YK0s.ret_ok (getr rg 1))
  by (rewrite Q1; apply ret_ok_codeptr_v; [unfold KW_R1, AF_m_file; lia | reflexivity]).
assert (P1 : ecall_pre_stk SEGS B ESTACK lyc Sc Wc rg mm mdq)
  by exact (ecall_pre_stk_at SEGS B ESTACK SegInstB.STK_m_file (mv_sp v) _ _ _ _ _ _ _ lyc Sc Wc mm mdq 0 rg
             (mf_s1 (mv_sp v) - mv_sp v) HJ Hsp Ho16 ltac:(lia) ltac:(lia) ltac:(lia) HraT R3 R4).
assert (P4 : astr_at SEGS Wc mm wp (seg_spec.zb (nth i MF_ROLE_WORDS [])))
  by (apply kw_astr; rewrite (kw_words_zs i Hi); exact (proj1 HSTR)).
assert (P5 : aread_ok SEGS ESTACK Wc rg mm wp (astr_len (seg_spec.zb (nth i MF_ROLE_WORDS [])) + 1)).
{ rewrite HAL. unfold aread_ok.
  split; [lia|]. split; [exact A63|]. split; [lia|]. split.
  - intros a Ha. split.
    + pose proof (proj1 (proj1 HSTR)) as HZ.
      replace a with (wp + Z.of_nat (Z.to_nat (a - wp))) by lia.
      rewrite (HZ (Z.to_nat (a - wp)) ltac:(rewrite length_app; cbn [length]; lia)). discriminate.
    + unfold ascratch_stk. rewrite Hsp. unfold kImgEnd in Hwp1. lia.
  - split; [exact AMR|]. split; [exact ARA | exact AHV]. }
assert (P6 : atail_vis SEGS Wc mm (wp + astr_len (seg_spec.zb (nth i MF_ROLE_WORDS []))))
  by (rewrite HAL; exact (sa_tail_of_romtail SEGS (w_H Wc) mm _ HROM)).
pose proof (mf_rom_now B v lyc Sc Wc mm mdq pos MF_LOW_ON mcc MCX CORE) as P7.
eapply SRr_bind.
{ exact (aj_art_at SEGS B LAWS pa_segs_low errno_low ESTACK (fun _ => False) (SIGMA SS___interceptor_trampoline_strlen)
    Wc rg mm SegInstB.STK_m_file (mv_sp v) _ _ _ _ _ _ _ lyc Sc mdq 0 (mf_s1 (mv_sp v) - mv_sp v)
    (Z_to_bv 64 (BASE + KW_R1))
    (fun regs' _ => getr regs' 10 = w64 (astr_len (seg_spec.zb (nth i MF_ROLE_WORDS [])))) HJ Hsp Ho16
    ltac:(lia) ltac:(lia) ltac:(lia) Q1 (fun a (H : False) => False_ind _ H)
    (ASTRLEN fx lyc Sc Wc rg mm mdq wp (seg_spec.zb (nth i MF_ROLE_WORDS [])) P1 Q10 Hwp0 P4 P5 P6 P7)). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Ha0 & HK2).
assert (K2 : forall a, 0 <= a < 2 ^ 64 ->
  ~ (mv_sp v + (mf_s1 (mv_sp v) - mv_sp v) - ESTACK <= a < mv_sp v + (mf_s1 (mv_sp v) - mv_sp v)) ->
  rdW Wc mem2 a = rdW Wc mm a) by (intros a Ha Hw; exact (HK2 a Ha Hw (fun x => x))).
pose proof (kw_keep n v lyc Sc Wc mm mdq pos mcc gi line p rest ok kl ov vl k vv mem2 md2
  (mv_sp v + (mf_s1 (mv_sp v) - mv_sp v) - ESTACK) (mv_sp v + (mf_s1 (mv_sp v) - mv_sp v))
  MEM HJ2 ltac:(lia) ltac:(lia) K2) as MEM2.
apply (R1 v lyc Sc Wc regs2 mem2 md2 pos mcc gi line p rest ok kl ov vl k vv wp MEM2
  (kw_regs_pres v rg regs2 vl line i RG HP2) Hi WG).
- apply (kw_lit_keep Wc mm mem2 wp _ (mv_sp v + (mf_s1 (mv_sp v) - mv_sp v) - ESTACK) HLIT);
    [unfold kImgEnd; lia | intros a Ha; apply K2; lia].
- rewrite (kw_pres_reg rg regs2 22%bv HP2) by kw_csav. exact Q22.
- rewrite Ha0, HAL. reflexivity.
Qed.

(* bcmp(wp, low, ln) from its trampoline (0x8677c): at 0x86780 a0 = 0 exactly when word i is low, every fact kept *)
Lemma kw_bcmp_call : forall n i v lyc Sc Wc rg mm mdq pos mcc gi line p rest ok kl ov vl k vv wp,
  KW_R2_i n i ->
  kw_mem n v lyc Sc Wc mm mdq pos mcc gi line p rest ok kl ov vl k vv -> kw_regs v rg vl line i -> (i < 5)%nat ->
  word_go (skipn i MF_ROLE_WORDS) (kr_low vv) (Z.of_nat i) = h_role_word (kr_low vv) ->
  sa_lit SEGS B (rdW Wc mm) wp (nth i MF_ROLE_WORDS []) ->
  length (nth i MF_ROLE_WORDS []) = kr_ln vl ->
  getr rg 10 = w64 wp -> getr rg 11 = w64 (frame_addr lyc 1 pos + 32) -> getr rg 12 = w64 (Z.of_nat (kr_ln vl)) ->
  getr rg 1 = Z_to_bv 64 (BASE + KW_R2) ->
  SRr SEGS Wc (mkCfg (mkst rg (Z_to_bv 64 (SIGMA SS___interceptor_trampoline_bcmp)) mm (seg_rom SEGS)) mdq)
    (MF_POST B v).
Proof.
intros n i v lyc Sc Wc rg mm mdq pos mcc gi line p rest ok kl ov vl k vv wp R2s MEM RG Hi WG HLIT HLEN Q10 Q11 Q12 Q1.
pose proof MEM as (CX & LOW).
pose proof CX as (MCX & _ & _ & CORE & _ & _ & _ & _ & KV & _).
pose proof CORE as (HJ & _ & _ & VSH & _). pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
pose proof RG as ((R2 & R3 & R4 & R8 & R9 & R18 & R19) & _).
destruct (mf_s1_facts B v MCX) as (Hs1 & _ & Hceil).
destruct (mf_sp0 B v MCX) as (_ & H47 & H16).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HSTK : SegInstB.STK_m_file = 8592) by (vm_compute; reflexivity).
assert (Hes : ESTACK = 4096) by reflexivity.
pose proof (kw_o16 (mv_sp v) (mf_s1 (mv_sp v)) Hs1) as Ho16.
assert (Hsp : spZ rg = mv_sp v + (mf_s1 (mv_sp v) - mv_sp v))
  by (unfold spZ; rewrite R2; unfold w64; rewrite unsigned_lit_small by lia; lia).
assert (Hfin : In (1, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 1 pos HAR Hfin) as (HF4096 & HFceil & HFapp).
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 pos HAR Hfin) as (HFal & _).
change (fs_frame_bytes 1) with 128 in HFceil, HFapp.
pose proof (kw_low_len _ _ _ _ _ _ _ KV) as HLL.
pose proof (kw_ln_le vl) as HLn.
pose proof (kw_words_len i Hi) as HwL.
pose proof (kw_lit_low _ _ _ HLIT) as [Hwp0 Hwp1].
pose proof HLIT as (_ & HSTR & HPIN & _ & _).
pose proof (HPIN _ _ _ _ _ HAR) as (A0 & A63 & AMR & ARA & AHV).
pose proof (proj1 (proj1 HSTR)) as HZW.
unfold kr_low_at in LOW.
unfold kImgEnd in Hwp1.
assert (HraT : YK0s.ret_ok (Z_to_bv 64 (BASE + KW_R2)))
  by (apply ret_ok_codeptr_v; [unfold KW_R2, AF_m_file; lia | reflexivity]).
assert (SRCx : src_ok SEGS Wc rg mm wp (Z.of_nat (kr_ln vl))).
{ intros a Ha. split.
  - replace a with (wp + Z.of_nat (Z.to_nat (a - wp))) by lia.
    rewrite (HZW (Z.to_nat (a - wp)) ltac:(rewrite length_app; cbn [length]; lia)). discriminate.
  - rewrite Hsp. lia. }
assert (SRCy : src_ok SEGS Wc rg mm (frame_addr lyc 1 pos + 32) (Z.of_nat (kr_ln vl))).
{ intros a Ha. split.
  - replace a with (frame_addr lyc 1 pos + 32 + Z.of_nat (Z.to_nat (a - (frame_addr lyc 1 pos + 32)))) by lia.
    rewrite (LOW (Z.to_nat (a - (frame_addr lyc 1 pos + 32))) ltac:(rewrite length_app; cbn [length]; lia)).
    discriminate.
  - rewrite Hsp. lia. }
assert (AMx : amem_range wp (Z.of_nat (kr_ln vl))) by (unfold amem_range in *; lia).
assert (AMy : amem_range (frame_addr lyc 1 pos + 32) (Z.of_nat (kr_ln vl))).
{ unfold amem_range, in_app, kLowShadowBeg, ASAN_CEIL in *. lia. }
assert (RAx : range_addressable (rdW Wc mm) SHADOW_OFF wp (Z.of_nat (kr_ln vl)))
  by (apply (range_addressable_sub _ _ _ _ _ _ ARA); lia).
assert (HUx : 0 < Z.of_nat (kr_ln vl) -> shadow_hull_vis (rdW Wc mm) wp (Z.of_nat (kr_ln vl)))
  by (intros Hn0; apply (kw_hull_sub _ wp _ (Z.of_nat (length (nth i MF_ROLE_WORDS [])) + 1)); [lia | lia | lia | apply AHV; lia]).
assert (RAy : range_addressable (rdW Wc mm) SHADOW_OFF (frame_addr lyc 1 pos + 32) (Z.of_nat (kr_ln vl)))
  by (apply kw_low_ra; [exact HFal | lia | lia | exact VSH]).
assert (HUy : 0 < Z.of_nat (kr_ln vl) -> shadow_hull_vis (rdW Wc mm) (frame_addr lyc 1 pos + 32) (Z.of_nat (kr_ln vl)))
  by (intros Hn0; apply (kw_low_hull lyc Sc Wc mm mdq pos _ HAR Hfin); lia).
(* bcmp's answer 0 is the equality of word i with low (both ln bytes) *)
assert (EQ : (forall j, 0 <= j < Z.of_nat (kr_ln vl) ->
  rdW Wc mm (wp + j) = rdW Wc mm (frame_addr lyc 1 pos + 32 + j)) <-> nth i MF_ROLE_WORDS [] = kr_low vv).
{ rewrite <- HLEN. apply kw_bytes_eq; [lia | apply (kw_zs_prefix _ _ _ [0] HZW) | apply (kw_zs_prefix _ _ _ [0] LOW)]. }
eapply SRr_bind.
{ exact (aj_bcmp_at SEGS B LAWS pa_segs_low (SIGMA SS___interceptor_trampoline_bcmp) (ABCMP fx) Wc rg mm
    SegInstB.STK_m_file (mv_sp v) _ _ _ _ _ _ _ lyc Sc mdq 0 wp (frame_addr lyc 1 pos + 32) (Z.of_nat (kr_ln vl))
    (mf_s1 (mv_sp v) - mv_sp v) (Z_to_bv 64 (BASE + KW_R2)) HJ
    Q10 Q11 Q12 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hsp Ho16 ltac:(lia) ltac:(lia) R3 R4 Q1 HraT
    SRCx SRCy ltac:(intros a Ha; lia) ltac:(intros a Ha; lia) AMx AMy RAx HUx RAy HUy). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v2 & -> & HJ2 & HP2 & Hres & Hcmp & HK2 & _).
pose proof (kw_keep n v lyc Sc Wc mm mdq pos mcc gi line p rest ok kl ov vl k vv mem2 md2
  (mv_sp v + (mf_s1 (mv_sp v) - mv_sp v) - 2 * ESTACK) (mv_sp v + (mf_s1 (mv_sp v) - mv_sp v))
  MEM HJ2 ltac:(lia) ltac:(lia) HK2) as MEM2.
apply (R2s v lyc Sc Wc regs2 mem2 md2 pos mcc gi line p rest ok kl ov vl k vv MEM2
  (kw_regs_pres v rg regs2 vl line i RG HP2) Hi WG).
rewrite Hres. split; intros X.
- apply kr_wtest_iff. apply (proj1 EQ). apply (proj1 Hcmp). exact X.
- apply (proj2 Hcmp). apply (proj2 EQ). apply kr_wtest_iff. exact X.
Qed.

(* ===================================== the four points ===================================== *)
(* KR_WORDS 0x86758 .. the strlen call: the check of words[i] (its shadow byte 0), wp = words[i] *)
Lemma kw_head_ok : forall n i, KW_R1_i n i -> KW_W_i n i.
Proof.
intros n i R1 v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ok kl ov vl k vv
  CX RB Hi LOW WG R26 R27 R20 R25 R21 R24 R23.
pose proof CX as (MCX & _ & _ & CORE & _).
pose proof CORE as (HJ & _). pose proof HJ as (HAR & _).
destruct (mf_s1_facts B v MCX) as (Hs1 & _ & Hceil).
destruct (mf_sp0 B v MCX) as (_ & H47 & _).
pose proof asan_consts as (C1 & _).
assert (HSTK : SegInstB.STK_m_file = 8592) by (vm_compute; reflexivity).
destruct (mf_words_now B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc MCX CORE) as (WPIN & _ & WW).
destruct (WW i Hi) as (wp & Hwp & HLIT).
pose proof (WPIN _ _ _ _ _ HAR) as (_ & _ & _ & WRA & _).
pose proof (kw_words_shadow _ i Hi WRA) as HSH.
pose proof (kw_lit_low _ _ _ HLIT) as [Hwp0 Hwp1].
assert (Hwp64 : 0 <= wp < 2 ^ 64) by (unfold kImgEnd in Hwp1; lia).
pose proof (kw_seedA Wc regs1 memc i wp Hi R23 R24 HSH Hwp Hwp64) as HS.
assert (SHOK : sh_ok SEGS kw_Bx [] (kw_E regs1 wp) (mrestrict (w_H Wc) memc)) by (unfold sh_ok; constructor).
assert (HEI : img_env VAL A_LIM (kw_E regs1 wp)) by (unfold kw_E; apply Eimg_env).
pose proof (kw_env_agree regs1 wp) as HA0.
pose proof (kw_ew32 regs1 wp) as E32.
assert (KM : forall a, 0 <= a < 2 ^ 64 -> rdW Wc memc a = rdW Wc memc a) by (intros; reflexivity).
revert HS SHOK HEI HA0 E32. generalize (kw_E regs1 wp) as E0. intros E0 HS SHOK HEI HA0 E32.
pose proof (env_agree_refl 34 E0) as HAE.
unfold mf_at.
(* the check, the load of words[i], up to strlen's trampoline *)
paj_run_tok RUN HS HJ SHOK Bspan; [kw_awr|].
kw_after E0 HAE KM.
pose proof (regs_kept_of_st_ok SEGS _ _ _ regs1 _ KW_KEPT4 HS (kw_ag32 _ _ _ _ HA0 HAE) ltac:(vm_compute; reflexivity))
  as HK.
cbn [ms_regs restrict] in HK.
prreg HS (10%bv : bv 5) Q10. prreg HS (22%bv : bv 5) Q22. prreg HS (1%bv : bv 5) Q1.
pmkst HS.
apply (kw_strlen_call n i v lyc Sc Wc _ _ _ pos mcc gi line p rest ok kl ov vl k vv wp R1).
- exact (kw_keep n v lyc Sc Wc memc mdc pos mcc gi line p rest ok kl ov vl k vv _ _ (mf_s1 (mv_sp v)) (mf_s1 (mv_sp v))
    (conj CX LOW) HJ ltac:(lia) ltac:(lia) (fun a Ha _ => KM a Ha)).
- exact (kw_regs_kept v regs1 _ vl line i
    (conj RB (conj R26 (conj R27 (conj R20 (conj R25 (conj R21 (conj R24 R23))))))) HK).
- exact Hi.
- exact WG.
- exact (kw_lit_keep Wc memc _ wp _ (2 ^ 64) HLIT ltac:(unfold kImgEnd; lia) (fun a Ha => KM a ltac:(lia))).
- rewrite Q22. first [rewrite E32 | rewrite (kw_ag_ew _ _ 32 _ HAE ltac:(lia) E32)]. reflexivity.
- rewrite Q10. first [rewrite E32 | rewrite (kw_ag_ew _ _ 32 _ HAE ltac:(lia) E32)]. reflexivity.
- rewrite Q1. reflexivity.
Qed.

(* KW_R1 0x8676c: |word i| <> ln, the next pass; else bcmp(wp, low, ln) *)
Lemma kw_r1_ok : forall n i, KW_R2_i n i -> KW_NEXT_i n i -> KW_R1_i n i.
Proof.
intros n i R2s NX v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ok kl ov vl k vv wp
  MEM RG Hi WG HLIT R22 R10.
pose proof MEM as (CX & LOW).
pose proof CX as (MCX & _ & _ & CORE & CELLS & _ & _ & _ & KV & _).
pose proof CORE as (HJ & _). pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
pose proof RG as ((R2 & R3 & R4 & R8 & R9 & R18 & R19) & R26 & R27 & R20 & R25 & R21 & R24 & R23).
pose proof CELLS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & C144).
destruct (mf_s1_facts B v MCX) as (Hs1 & _ & Hceil).
destruct (mf_sp0 B v MCX) as (_ & H47 & _).
pose proof asan_consts as (C1 & _).
assert (HSTK : SegInstB.STK_m_file = 8592) by (vm_compute; reflexivity).
assert (Hfin : In (1, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 1 pos HAR Hfin) as (HF4096 & HFceil & _).
change (fs_frame_bytes 1) with 128 in HFceil.
pose proof (kw_low_len _ _ _ _ _ _ _ KV) as HLL.
pose proof (kw_ln_le vl) as HLn.
pose proof (kw_words_len i Hi) as HwL.
pose proof (kw_lit_low _ _ _ HLIT) as [Hwp0 Hwp1]. unfold kImgEnd in Hwp1.
pose proof (kw_seedB Wc regs1 memc (mf_s1 (mv_sp v)) (frame_addr lyc 1 pos + 32) R9 ltac:(lia) ltac:(lia)
  ltac:(lia) C144) as HS.
assert (SHOK : sh_ok SEGS kw_Bx [] (kw_E regs1 (frame_addr lyc 1 pos + 32)) (mrestrict (w_H Wc) memc))
  by (unfold sh_ok; constructor).
assert (HEI : img_env VAL A_LIM (kw_E regs1 (frame_addr lyc 1 pos + 32))) by (unfold kw_E; apply Eimg_env).
pose proof (kw_env_agree regs1 (frame_addr lyc 1 pos + 32)) as HA0.
pose proof (kw_ew32 regs1 (frame_addr lyc 1 pos + 32)) as E32.
assert (E10 : ew (kw_E regs1 (frame_addr lyc 1 pos + 32)) 10 = Z_to_bv 64 (Z.of_nat (length (nth i MF_ROLE_WORDS []))))
  by (rewrite (kw_ew_reg _ _ 10 10%bv eq_refl); exact R10).
assert (E26 : ew (kw_E regs1 (frame_addr lyc 1 pos + 32)) 26 = Z_to_bv 64 (Z.of_nat (kr_ln vl)))
  by (rewrite (kw_ew_reg _ _ 26 26%bv eq_refl); exact R26).
assert (E22 : ew (kw_E regs1 (frame_addr lyc 1 pos + 32)) 22 = Z_to_bv 64 wp)
  by (rewrite (kw_ew_reg _ _ 22 22%bv eq_refl); exact R22).
assert (KM : forall a, 0 <= a < 2 ^ 64 -> rdW Wc memc a = rdW Wc memc a) by (intros; reflexivity).
revert HS SHOK HEI HA0 E32 E10 E26 E22. generalize (kw_E regs1 (frame_addr lyc 1 pos + 32)) as E0.
intros E0 HS SHOK HEI HA0 E32 E10 E26 E22.
pose proof (env_agree_refl 34 E0) as HAE.
unfold mf_at.
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* bne taken: |word i| <> ln, so word i is not low: the next pass *)
  rewrite branch_ne_U, (U_atom _ 10 _ E10), (U_atom _ 26 _ E26) in Hc by lia.
  apply negb_true_iff, Z.eqb_neq in Hc.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan KW_NEXT; [kw_awr|].
  kw_after E0 HAE KM.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 _ KW_KEPT4 HS (kw_ag32 _ _ _ _ HA0 HAE) ltac:(vm_compute; reflexivity))
    as HK.
  cbn [ms_regs restrict] in HK.
  pmkst HS.
  apply (NX v lyc Sc Wc _ _ _ pos mcc gi line p rest ok kl ov vl k vv).
  + exact (kw_keep n v lyc Sc Wc memc mdc pos mcc gi line p rest ok kl ov vl k vv _ _ (mf_s1 (mv_sp v))
      (mf_s1 (mv_sp v)) MEM HJ ltac:(lia) ltac:(lia) (fun a Ha _ => KM a Ha)).
  + exact (kw_regs_kept v regs1 _ vl line i RG HK).
  + exact Hi.
  + exact WG.
  + unfold kr_wtest. rewrite HLL.
    destruct (Nat.eqb_spec (length (nth i MF_ROLE_WORDS [])) (kr_ln vl)) as [E | E];
      [exfalso; apply Hc; rewrite E; reflexivity | reflexivity].
- (* not taken: |word i| = ln; 0x86770 .. the bcmp call *)
  rewrite branch_ne_U, (U_atom _ 10 _ E10), (U_atom _ 26 _ E26) in Hc by lia.
  apply negb_false_iff, Z.eqb_eq in Hc.
  paj_run_tok RUN HS HJ SHOK Bspan; [kw_awr|].
  kw_after E0 HAE KM.
  pose proof (regs_kept_of_st_ok SEGS _ _ _ regs1 _ KW_KEPT4 HS (kw_ag32 _ _ _ _ HA0 HAE) ltac:(vm_compute; reflexivity))
    as HK.
  cbn [ms_regs restrict] in HK.
  prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
  prreg HS (1%bv : bv 5) Q1.
  pmkst HS.
  apply (kw_bcmp_call n i v lyc Sc Wc _ _ _ pos mcc gi line p rest ok kl ov vl k vv wp R2s).
  + exact (kw_keep n v lyc Sc Wc memc mdc pos mcc gi line p rest ok kl ov vl k vv _ _ (mf_s1 (mv_sp v))
      (mf_s1 (mv_sp v)) MEM HJ ltac:(lia) ltac:(lia) (fun a Ha _ => KM a Ha)).
  + exact (kw_regs_kept v regs1 _ vl line i RG HK).
  + exact Hi.
  + exact WG.
  + exact (kw_lit_keep Wc memc _ wp _ (2 ^ 64) HLIT ltac:(unfold kImgEnd; lia) (fun a Ha => KM a ltac:(lia))).
  + lia.
  + rewrite Q10. first [rewrite E22 | rewrite (kw_ag_ew _ _ 22 _ HAE ltac:(lia) E22)]. reflexivity.
  + rewrite Q11. first [rewrite E32 | rewrite (kw_ag_ew _ _ 32 _ HAE ltac:(lia) E32)]. reflexivity.
  + rewrite Q12. first [rewrite E26 | rewrite (kw_ag_ew _ _ 26 _ HAE ltac:(lia) E26)]. reflexivity.
  + rewrite Q1. reflexivity.
Qed.

(* KW_R2 0x86780: bcmp gave 0, word i is low: KR_HIT; else the next pass *)
Lemma kw_r2_ok : forall n i, KR_HIT_stmt B n -> KW_NEXT_i n i -> KW_R2_i n i.
Proof.
intros n i HIT NX v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ok kl ov vl k vv MEM RG Hi WG HEQ.
pose proof MEM as (CX & LOW).
pose proof CX as (MCX & _ & _ & CORE & _).
pose proof CORE as (HJ & _).
pose proof RG as (RB & R26 & R27 & R20 & R25 & R21 & R24 & R23).
destruct (mf_s1_facts B v MCX) as (Hs1 & _ & Hceil).
assert (HSTK : SegInstB.STK_m_file = 8592) by (vm_compute; reflexivity).
pose proof (kw_seed0 Wc regs1 memc KW_R2 0) as HS.
assert (SHOK : sh_ok SEGS kw_Bx [] (kw_E regs1 0) (mrestrict (w_H Wc) memc)) by (unfold sh_ok; constructor).
assert (HEI : img_env VAL A_LIM (kw_E regs1 0)) by (unfold kw_E; apply Eimg_env).
pose proof (kw_env_agree regs1 0) as HA0.
assert (E10 : ew (kw_E regs1 0) 10 = getr regs1 10) by (apply kw_ew_reg; reflexivity).
assert (KM : forall a, 0 <= a < 2 ^ 64 -> rdW Wc memc a = rdW Wc memc a) by (intros; reflexivity).
revert HS SHOK HEI HA0 E10. generalize (kw_E regs1 0) as E0. intros E0 HS SHOK HEI HA0 E10.
pose proof (env_agree_refl 34 E0) as HAE.
unfold mf_at.
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* beqz taken: a0 = 0, word i is low: KR_HIT *)
  rewrite branch_eq_U, U_SOff, U_SLit, Z.add_0_r, E10 in Hc. apply Z.eqb_eq in Hc.
  rewrite (YP0m.zcanon_small (bv_unsigned (getr regs1 10))) in Hc
    by (pose proof (bv_unsigned_in_range 64 (getr regs1 10)) as Hr; exact Hr).
  assert (H0 : getr regs1 10 = w64 0) by (apply bv_eq; rewrite Hc; reflexivity).
  apply HEQ in H0.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan KR_HIT; [kw_awr|].
  kw_after E0 HAE KM.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 _ KW_KEPT4 HS (kw_ag32 _ _ _ _ HA0 HAE) ltac:(vm_compute; reflexivity))
    as HK.
  cbn [ms_regs restrict] in HK.
  pmkst HS.
  pose proof (kw_keep n v lyc Sc Wc memc mdc pos mcc gi line p rest ok kl ov vl k vv _ _ (mf_s1 (mv_sp v))
    (mf_s1 (mv_sp v)) MEM HJ ltac:(lia) ltac:(lia) (fun a Ha _ => KM a Ha)) as (CX2 & _).
  pose proof (kw_regs_kept v regs1 _ vl line i RG HK) as (RB2 & _ & R272 & R202 & R252 & _).
  apply (HIT v lyc Sc Wc _ _ _ pos mcc gi line p rest ok kl ov vl k vv i CX2 RB2 Hi).
  + rewrite <- WG, (kr_word_go_step i _ Hi), H0. reflexivity.
  + exact R202.
  + exact R252.
  + exact R272.
- (* not taken: a0 <> 0, word i is not low: the next pass *)
  rewrite branch_eq_U, U_SOff, U_SLit, Z.add_0_r, E10 in Hc. apply Z.eqb_neq in Hc.
  assert (Hne : getr regs1 10 <> w64 0) by (intros E; apply Hc; rewrite E; reflexivity).
  assert (Hwt : kr_wtest (nth i MF_ROLE_WORDS []) (kr_low vv) = false).
  { destruct (kr_wtest (nth i MF_ROLE_WORDS []) (kr_low vv)) eqn:X; [|reflexivity].
    exfalso. apply Hne. apply (proj2 HEQ). first [exact X | reflexivity]. }
  paj_run_to_tok RUNTO HS HJ SHOK Bspan KW_NEXT; [kw_awr|].
  kw_after E0 HAE KM.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 _ KW_KEPT4 HS (kw_ag32 _ _ _ _ HA0 HAE) ltac:(vm_compute; reflexivity))
    as HK.
  cbn [ms_regs restrict] in HK.
  pmkst HS.
  exact (NX v lyc Sc Wc _ _ _ pos mcc gi line p rest ok kl ov vl k vv
    (kw_keep n v lyc Sc Wc memc mdc pos mcc gi line p rest ok kl ov vl k vv _ _ (mf_s1 (mv_sp v))
      (mf_s1 (mv_sp v)) MEM HJ ltac:(lia) ltac:(lia) (fun a Ha _ => KM a Ha))
    (kw_regs_kept v regs1 _ vl line i RG HK) Hi WG Hwt).
Qed.

(* KW_NEXT 0x86784: the cursors step; pass i + 1 at KR_WORDS, or after word 4 KR_MISS *)
Lemma kw_next_ok : forall n i, (i < 5)%nat -> KR_MISS_stmt B n -> ((S i < 5)%nat -> KW_W_i n (S i)) -> KW_NEXT_i n i.
Proof.
intros n i Hi0 MISS WS v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ok kl ov vl k vv MEM RG Hi WG HWF.
pose proof MEM as (CX & LOW).
pose proof CX as (MCX & _ & _ & CORE & _).
pose proof CORE as (HJ & _).
pose proof RG as (RB & R26 & R27 & R20 & R25 & R21 & R24 & R23).
destruct (mf_s1_facts B v MCX) as (Hs1 & _ & Hceil).
assert (HSTK : SegInstB.STK_m_file = 8592) by (vm_compute; reflexivity).
pose proof (kw_seed0 Wc regs1 memc KW_NEXT 0) as HS.
assert (SHOK : sh_ok SEGS kw_Bx [] (kw_E regs1 0) (mrestrict (w_H Wc) memc)) by (unfold sh_ok; constructor).
assert (HEI : img_env VAL A_LIM (kw_E regs1 0)) by (unfold kw_E; apply Eimg_env).
pose proof (kw_env_agree regs1 0) as HA0.
assert (E20 : ew (kw_E regs1 0) 20 = w64 (- (4 * Z.of_nat i))) by (rewrite (kw_ew_reg _ _ 20 20%bv eq_refl); exact R20).
assert (E25 : ew (kw_E regs1 0) 25 = w64 (ROLES + 4 * Z.of_nat i)) by (rewrite (kw_ew_reg _ _ 25 25%bv eq_refl); exact R25).
assert (E21 : ew (kw_E regs1 0) 21 = w64 (WORDS + 8 * Z.of_nat i)) by (rewrite (kw_ew_reg _ _ 21 21%bv eq_refl); exact R21).
assert (E24 : ew (kw_E regs1 0) 24 = w64 (WORDS + 8 * Z.of_nat i)) by (rewrite (kw_ew_reg _ _ 24 24%bv eq_refl); exact R24).
assert (E23 : ew (kw_E regs1 0) 23 = w64 (SHADOW_OFF + WORDS / 8 + Z.of_nat i))
  by (rewrite (kw_ew_reg _ _ 23 23%bv eq_refl); exact R23).
assert (KM : forall a, 0 <= a < 2 ^ 64 -> rdW Wc memc a = rdW Wc memc a) by (intros; reflexivity).
revert HS SHOK HEI HA0 E20 E25 E21 E24 E23. generalize (kw_E regs1 0) as E0.
intros E0 HS SHOK HEI HA0 E20 E25 E21 E24 E23.
pose proof (env_agree_refl 34 E0) as HAE.
pose proof (kw_keep n v lyc Sc Wc memc mdc pos mcc gi line p rest ok kl ov vl k vv) as KEEP.
unfold mf_at.
(* s4 -= 4, s9 += 4, s5 += 8, s7 += 1, s8 += 8, a0 = -20, up to `bne s4,a0` *)
paj_run_tok RUN HS HJ SHOK Bspan; [kw_awr|].
kw_after E0 HAE KM.
assert (Hi5 : (i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4)%nat) by lia.
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* bne taken: word i was not the last; pass i + 1 *)
  rewrite branch_ne_U, U_SOff, U_SLit, (kw_ag_ew _ _ 20 _ HAE ltac:(lia) E20) in Hc.
  assert (Hi4 : i <> 4%nat) by (intros ->; vm_compute in Hc; discriminate Hc).
  paj_run_to_tok RUNTO HS HJ SHOK Bspan KR_WORDS; [kw_awr|].
  kw_after E0 HAE KM.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 _ KW_KEPT HS (kw_ag32 _ _ _ _ HA0 HAE) ltac:(vm_compute; reflexivity))
    as HK.
  cbn [ms_regs restrict] in HK.
  prreg HS (20%bv : bv 5) Q20. prreg HS (25%bv : bv 5) Q25. prreg HS (21%bv : bv 5) Q21.
  prreg HS (24%bv : bv 5) Q24. prreg HS (23%bv : bv 5) Q23.
  pmkst HS.
  pose proof (KEEP _ _ (mf_s1 (mv_sp v)) (mf_s1 (mv_sp v)) MEM HJ ltac:(lia) ltac:(lia) (fun a Ha _ => KM a Ha))
    as (CX2 & LOW2).
  apply (WS ltac:(lia) v lyc Sc Wc _ _ _ pos mcc gi line p rest ok kl ov vl k vv CX2 (kw_regs_b_kept v regs1 _ RB HK)
    ltac:(lia) LOW2).
  + rewrite <- WG, (kr_word_go_step i _ Hi), HWF. reflexivity.
  + rewrite HK by (cbv [KW_KEPT In]; tauto). exact R26.
  + rewrite HK by (cbv [KW_KEPT In]; tauto). exact R27.
  + rewrite Q20. first [rewrite E20 | rewrite (kw_ag_ew _ _ 20 _ HAE ltac:(lia) E20)].
    unfold w64. rewrite kw_bv_off. f_equal. lia.
  + rewrite Q25. first [rewrite E25 | rewrite (kw_ag_ew _ _ 25 _ HAE ltac:(lia) E25)].
    unfold w64. rewrite kw_bv_off. f_equal. lia.
  + rewrite Q21. first [rewrite E21 | rewrite (kw_ag_ew _ _ 21 _ HAE ltac:(lia) E21)].
    unfold w64. rewrite kw_bv_off. f_equal. lia.
  + rewrite Q24. first [rewrite E24 | rewrite (kw_ag_ew _ _ 24 _ HAE ltac:(lia) E24)].
    unfold w64. rewrite kw_bv_off. f_equal. lia.
  + rewrite Q23. first [rewrite E23 | rewrite (kw_ag_ew _ _ 23 _ HAE ltac:(lia) E23)].
    unfold w64. rewrite kw_bv_off. f_equal. lia.
- (* not taken: word 4 was the last; KR_MISS *)
  rewrite branch_ne_U, U_SOff, U_SLit, (kw_ag_ew _ _ 20 _ HAE ltac:(lia) E20) in Hc.
  assert (Hi4 : i = 4%nat)
    by (destruct Hi5 as [-> | [-> | [-> | [-> | ->]]]]; try reflexivity; vm_compute in Hc; discriminate Hc).
  subst i.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan KR_MISS; [kw_awr|].
  kw_after E0 HAE KM.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 _ KW_KEPT HS (kw_ag32 _ _ _ _ HA0 HAE) ltac:(vm_compute; reflexivity))
    as HK.
  cbn [ms_regs restrict] in HK.
  pmkst HS.
  pose proof (KEEP _ _ (mf_s1 (mv_sp v)) (mf_s1 (mv_sp v)) MEM HJ ltac:(lia) ltac:(lia) (fun a Ha _ => KM a Ha))
    as (CX2 & _).
  apply (MISS v lyc Sc Wc _ _ _ pos mcc gi line p rest ok kl ov vl k vv CX2 (kw_regs_b_kept v regs1 _ RB HK)).
  + rewrite <- WG, (kr_word_go_step 4 _ Hi), HWF. exact (kr_word_go_5 _).
  + rewrite HK by (cbv [KW_KEPT In]; tauto). exact R27.
Qed.

(* ===================================== the loop ===================================== *)
Lemma kw_all : forall n, KR_HIT_stmt B n -> KR_MISS_stmt B n ->
  forall m i, (i + m = 5)%nat -> (i < 5)%nat -> KW_W_i n i.
Proof.
intros n HIT MISS m. induction m as [|m IH]; intros i Him Hi; [lia|].
assert (NX : KW_NEXT_i n i) by (apply (kw_next_ok n i Hi MISS); intros Hsi; apply IH; lia).
apply kw_head_ok. apply kw_r1_ok; [apply (kw_r2_ok n i HIT NX) | exact NX].
Qed.

Lemma kr_s_words : forall n, KR_HIT_stmt B n -> KR_MISS_stmt B n -> KR_WORDS_stmt B n.
Proof.
intros n HIT MISS v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ok kl ov vl k vv i CX RB Hi.
exact (kw_all n HIT MISS (5 - i) i ltac:(lia) Hi v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ok kl ov vl k vv
  CX RB Hi).
Qed.
End e.
End f.
End d.

About kr_s_words.
Print Assumptions kr_s_words.

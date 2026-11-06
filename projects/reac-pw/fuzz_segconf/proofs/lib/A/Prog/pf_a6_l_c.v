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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 254 of its 296 lines of code are new or changed and 411 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image A (fuzz_segconf.asan): the strspn call of segment A6's LONG walk of
   reac_segconf_parse_file (0x87e2c `mv a0,s9`, 0x87e30 `ld a1,0xa8(s1)`, 0x87e34 `jal` the strspn trampoline,
   pa_sigma SS___interceptor_trampoline_strspn, returning at 0x87e38), as one step lemma from the cut facts
   pf_base at the trampoline's entry to pf_base at the return (segment A6's proof, its LONG walk,
   2026-10-30). The walk lib/A/Prog/pf_a6_l.v applies it.

     a6l_strspn_step   strspn(t + o, " \t\r") through RtString.astrspn_realizes (the interceptor
                       owner's interface row 2)
                       and PaArt.aj_art_at: a0 = strspn_blank (skipn o s) after the call (pf_a6_k.v a6_spn),
                       pf_base again at the call's new memory (pf_a5_k.v a5_move0: strspn writes only its window
                       of 2 * ESTACK below s1), and the bytes below alloc_ceiling and from s1 up kept.

   The premises of astrspn_realizes at the call, from the cut's pf_base alone:
     aguard_ok          pf_obj's last conjunct sa_ssp (the same two rdword facts)
     ecall_pre_stk      PaArt.ecall_pre_stk_at from the cut's journal (o = s1 - sp0 in (-352, -320], a multiple
                        of 16; the window 2 * ESTACK fits STK = 12800)
     the text tail      sa_str of the text at t gives the C string skipn o s at t + o (a6lc_astr_of_zs); its read
                        range by PaArt.aread_ok_of_block from the text's live heap block; its band room from the
                        block's in_app (the 7 bytes of slack fit below kLowMemEnd or kHighMemEnd); its NUL is the
                        text's, so atail_vis is sa_str's sa_tail
     the set " \t\r"    the third literal of PARSE_FILE_LITS at seg_litA_rc [SP; TAB; CR]: pf_obj's sa_lit
                        (a6lc_lit_read)
     rt_rom_view        pf_a5_k.v a5_rom
   No Section hypothesis but TL (the listing's runtime record: the errno cell aj_art_at keeps apart) and STRSPN.

   Copied (renamed a6lc_*, restated over pf_base) from segment A7's proof: w3_view_wrap,
   w3_fi_get and w3_strlen_step (lib/A/Prog/pf_a7_w3_c.v, commit a78dafc7ecfa), a7_astr_of_sa, a7_str_some,
   a7_read_ok_of_addr and a7_lit_read (lib/A/Prog/pf_a7_r.v, commit ebe0b30cca65); from this
   tree: trim_s.v's tr_in_skipn and tr_astr_of_zs, trim_k.v's TrimA.nth_skipn0 and TrimA.bv8_small. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0d_tail.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YC5d YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec strspn_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec pfA_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require RtString.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList
SegAddr SegPa SegObj SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPaLib PaDenot PaLibG PaLibF PaLibH PaCall
PaCallRun PaArt PaFx.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import refuse_c reac_segconf_parse_file_c
SegInstA pf_pieces pf_a5_k pf_a6_k.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* ======================================== pure facts ======================================== *)
(* a reader reads an address modulo 2 ^ 64 (pf_a7_w3_c.v w3_view_wrap) *)
Lemma a6lc_view_wrap : forall segs H mem a, aview segs H mem a = aview segs H mem (a mod 2 ^ 64).
Proof.
  intros segs H mem a. unfold aview, mbyte.
  replace (Z_to_bv 64 (a mod 2 ^ 64)) with (Z_to_bv 64 a); [reflexivity|].
  apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite Zmod_mod. reflexivity.
Qed.

Lemma a6lc_in_skipn : forall {A} (x : A) k l, In x (skipn k l) -> In x l.
Proof. intros A x k l H. rewrite <- (firstn_skipn k l). apply in_or_app. right. exact H. Qed.

Lemma a6lc_nth_skipn : forall (l : list Z) k j, nth j (skipn k l) 0 = nth (k + j) l 0.
Proof.
  induction l as [|x l IH]; intros [|k] j; cbn; try reflexivity.
  - destruct j; reflexivity.
  - apply IH.
Qed.

Lemma a6lc_bv8_small : forall z, 0 <= z < 256 -> bv_unsigned (Z_to_bv 8 z) = z.
Proof.
  intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 8) with 256. lia.
Qed.

(* the bytes of a C string read through a reader of bytes are bytes *)
Lemma a6lc_zs_rng : forall (rd : reader) p s, (forall a x, rd a = Some x -> 0 <= x < 256) ->
  sa_zs rd p (s ++ [0]) -> forall i, (i < length s)%nat -> 0 <= nth i s 0 < 256.
Proof.
  intros rd p s Hr Hz i Hi. apply (Hr (p + Z.of_nat i)).
  rewrite (Hz i) by (rewrite length_app; cbn [length]; lia). rewrite app_nth1 by exact Hi. reflexivity.
Qed.

(* the C string's tail from byte k as the interceptor contracts state a string (trim_s.v tr_astr_of_zs) *)
Lemma a6lc_astr_of_zs : forall (rd : reader) p s k, (forall a x, rd a = Some x -> 0 <= x < 256) ->
  sa_zs rd p (s ++ [0]) -> ~ In 0 s -> (k <= length s)%nat ->
  astr_atR rd (p + Z.of_nat k) (seg_spec.zb (skipn k s)).
Proof.
  intros rd p s k Hrng HZS NZ Hk.
  assert (HV : forall i, (i <= length s)%nat -> rd (p + Z.of_nat i) = Some (nth i s 0)).
  { intros i Hi. rewrite (HZS i) by (rewrite length_app; cbn [length]; lia).
    destruct (Nat.lt_ge_cases i (length s)) as [Hl | Hg].
    - rewrite app_nth1 by exact Hl. reflexivity.
    - assert (i = length s) as -> by lia. rewrite app_nth2 by lia. rewrite Nat.sub_diag. cbn [nth].
      rewrite nth_overflow by lia. reflexivity. }
  assert (HR : forall i, (i < length s)%nat -> 0 <= nth i s 0 < 256)
    by (intros i Hi; exact (Hrng _ _ (HV i ltac:(lia)))).
  unfold seg_spec.zb. split.
  - intros i Hi. rewrite length_app, length_map, length_skipn in Hi. cbn [length] in Hi.
    replace (p + Z.of_nat k + Z.of_nat i) with (p + Z.of_nat (k + i)) by lia.
    rewrite (HV (k + i)%nat) by lia.
    destruct (Nat.lt_ge_cases i (length s - k)) as [Hl | Hg].
    + rewrite app_nth1 by (rewrite length_map, length_skipn; lia).
      rewrite (map_nth (Z_to_bv 8) (skipn k s) 0 i), a6lc_nth_skipn.
      rewrite a6lc_bv8_small by (apply HR; lia). reflexivity.
    + assert (i = length s - k)%nat as -> by lia.
      rewrite app_nth2 by (rewrite length_map, length_skipn; lia).
      rewrite length_map, length_skipn, Nat.sub_diag. cbn [nth].
      replace (k + (length s - k))%nat with (length s) by lia.
      rewrite nth_overflow by lia. reflexivity.
  - intros Hin. apply in_map_iff in Hin as (x & Hx & Hin).
    pose proof (In_nth _ _ 0 (a6lc_in_skipn _ _ _ Hin)) as (i & Hi & Hxi).
    apply NZ. rewrite <- Hxi in Hx. pose proof (HR i Hi) as Hr.
    apply (f_equal bv_unsigned) in Hx. rewrite a6lc_bv8_small in Hx by exact Hr.
    rewrite a6lc_bv8_small in Hx by lia.
    rewrite <- Hx. apply nth_In. exact Hi.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ seg_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* ======================================== the string facts ======================================== *)
(* SegABase's sa_str (list Z, with its slack) as astr_at at seg_spec.zb l, its length and atail_vis
   (pf_a7_r.v a7_astr_of_sa) *)
Lemma a6lc_astr_of_sa : forall (W : world SEGS) mem q l,
  sa_str (rdW W mem) q l ->
  astr_at SEGS W mem q (seg_spec.zb l) /\ astr_len (seg_spec.zb l) = Z.of_nat (length l) /\
  atail_vis SEGS W mem (q + Z.of_nat (length l)).
Proof.
  intros W mem q l [Hz Ht].
  destruct (sa_strz_bytes SEGS (w_H W) mem q l Hz) as (Hb & Hn & _).
  split; [apply astr_atR_view; split; [exact Hb | exact Hn]|].
  split; [unfold astr_len, seg_spec.zb; rewrite length_map; reflexivity|].
  exact Ht.
Qed.

(* every byte of a C string and its NUL is mapped (pf_a7_r.v a7_str_some) *)
Lemma a6lc_str_some : forall (rd : reader) p s a, sa_str rd p s -> p <= a <= p + Z.of_nat (length s) ->
  rd a <> None.
Proof.
  intros rd p s a [[Hz _] _] Ha.
  assert (Hi : (Z.to_nat (a - p) < length (s ++ [0%Z]))%nat) by (rewrite length_app; cbn [length]; lia).
  pose proof (Hz _ Hi) as E. rewrite Z2Nat.id in E by lia.
  replace (p + (a - p)) with a in E by lia. rewrite E. discriminate.
Qed.

(* a range parse_file's memory holds, as aread_ok (pf_a7_r.v a7_read_ok_of_addr) *)
Lemma a6lc_read_ok_of_addr : forall (W : world SEGS) regs mem stk q n,
  sa_addr (rdW W mem) q n -> 0 <= n < 2 ^ 32 ->
  (forall a, q <= a < q + n -> rdW W mem a <> None) -> q + n <= spZ regs - stk ->
  aread_ok SEGS stk W regs mem q n.
Proof.
  intros W regs mem stk q n (A0 & A1 & A2 & A3 & A4) Hn Hm Hw.
  split; [exact A0|]. split; [exact A1|]. split; [exact Hn|].
  split; [|split; [exact A2 | split; [exact A3 | exact A4]]].
  intros a Ha. split; [exact (Hm a Ha)|]. unfold ascratch_stk. lia.
Qed.

Section e.
Variable B : asyms.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
(* the listing's runtime record: the errno cell aj_art_at keeps apart *)
Hypothesis TL : PALib B.
(* the interceptor owner's interface row 2 at the listing's strspn trampoline (pf_pieces.v:669) *)
Hypothesis STRSPN : forall fx0 : YK11.FPState,
  @RtString.astrspn_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_strspn) gotwA guardA.

(* the registers of pf_fi at a call (pf_rg states them at Z_to_bv 5 r, the code at the bv literal;
   pf_a7_w3_c.v w3_fi_get) *)
Lemma a6lc_fi_get : forall v rX, pf_rg rX (a5_FI B v) ->
  getr rX 2 = w64 (pf_s1 v) /\ getr rX 3 = w64 (as_gp B) /\
  getr rX 4 = w64 (as_tp B) /\ getr rX 8 = w64 (pf_sp0 v).
Proof.
  intros v rX H.
  pose proof (a5_rg_get rX _ 2 _ H ltac:(unfold a5_FI; cbn [In]; tauto)) as E2.
  pose proof (a5_rg_get rX _ 3 _ H ltac:(unfold a5_FI; cbn [In]; tauto)) as E3.
  pose proof (a5_rg_get rX _ 4 _ H ltac:(unfold a5_FI; cbn [In]; tauto)) as E4.
  pose proof (a5_rg_get rX _ 8 _ H ltac:(unfold a5_FI; cbn [In]; tauto)) as E8.
  assert (Q2 : Z_to_bv 5 2 = (2%bv : bv 5)) by (apply bv_eq; reflexivity).
  assert (Q3 : Z_to_bv 5 3 = (3%bv : bv 5)) by (apply bv_eq; reflexivity).
  assert (Q4 : Z_to_bv 5 4 = (4%bv : bv 5)) by (apply bv_eq; reflexivity).
  assert (Q8 : Z_to_bv 5 8 = (8%bv : bv 5)) by (apply bv_eq; reflexivity).
  rewrite Q2 in E2. rewrite Q3 in E3. rewrite Q4 in E4. rewrite Q8 in E8.
  exact (conj E2 (conj E3 (conj E4 E8))).
Qed.

(* a literal of PARSE_FILE_LITS at a call whose window lies above alloc_ceiling: pf_obj's sa_lit (sa_pinned,
   the image range, the bytes) gives what an interceptor asks of a C string argument (pf_a7_r.v a7_lit_read, at
   the whole string and its NUL) *)
Lemma a6lc_lit_read : forall v pos lyc Sc Wc rX memc mdc sc regsc stk s,
  pf_base B v pos lyc Sc Wc rX memc mdc sc ->
  In s PARSE_FILE_LITS -> alloc_ceiling <= spZ regsc - stk ->
  0 < seg_litA_rc s /\
  astr_at SEGS Wc memc (seg_litA_rc s) (seg_spec.zb s) /\ astr_len (seg_spec.zb s) = Z.of_nat (length s) /\
  aread_ok SEGS stk Wc regsc memc (seg_litA_rc s) (Z.of_nat (length s) + 1) /\
  amem_range (seg_litA_rc s) (Z.of_nat (length s) + 8) /\
  atail_vis SEGS Wc memc (seg_litA_rc s + Z.of_nat (length s)).
Proof.
  intros v pos lyc Sc Wc rX memc mdc sc regsc stk s HB Hin Hw.
  pose proof (a5_geo B v pos lyc Sc Wc rX memc mdc sc HB) as (HAR & _).
  destruct HB as (_ & _ & Hobj & _).
  destruct Hobj as (_ & _ & _ & _ & _ & _ & HL & _).
  destruct (HL s Hin) as (Ha & Hstr & Hp & _ & Hi).
  destruct (a6lc_astr_of_sa Wc memc _ s Hstr) as (HA & HLn & HT).
  pose proof (Hp lyc Sc Wc memc mdc HAR) as HP.
  pose proof (proj1 (Hi (seg_litA_rc s + Z.of_nat (length s)) ltac:(lia))) as Himg.
  pose proof (pa_img_range _ Himg) as Hrg.
  pose proof asan_consts as (C1 & _ & _ & _ & C5). unfold kImgEnd in Hrg.
  split; [exact Ha|]. split; [exact HA|]. split; [exact HLn|].
  split; [|split].
  - apply a6lc_read_ok_of_addr; [exact HP | lia | | lia].
    intros a Ha'. apply (a6lc_str_some _ _ _ a Hstr). lia.
  - unfold amem_range. left. rewrite C5. lia.
  - exact HT.
Qed.

(* ======================================== strspn(t + o, " \t\r") at 0x87e34 ======================================== *)
Lemma a6l_strspn_step : forall v pos lyc Sc Wc (regsc : bvmap 5 word) memc mdc raw o
  (Q : world SEGS -> config -> Prop),
  pf_base B v pos lyc Sc Wc regsc memc mdc PF_SC_LINE ->
  (o < length (p_s v))%nat ->
  getr regsc 1 = raw -> YK0s.ret_ok raw ->
  getr regsc 10 = w64 (p_t v + Z.of_nat o) ->
  getr regsc 11 = w64 (seg_litA_rc [SP; TAB; CR]) ->
  (forall regs2 mem2 md2,
     pf_base B v pos lyc Sc Wc regs2 mem2 md2 PF_SC_LINE ->
     aregs_preserved regsc regs2 ->
     getr regs2 10 = w64 (Z.of_nat (strspn_blank (skipn o (p_s v)))) ->
     (forall a, 0 <= a < 2 ^ 64 -> a < alloc_ceiling \/ pf_s1 v <= a -> rdW Wc mem2 a = rdW Wc memc a) ->
     SRr SEGS Wc (mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2) Q) ->
  SRr SEGS Wc (mkCfg (mkst regsc (Z_to_bv 64 (SIG SS___interceptor_trampoline_strspn)) memc (seg_rom SEGS)) mdc) Q.
Proof.
  intros v pos lyc Sc Wc regsc memc mdc raw o Q HB Ho R1 Hraw R10 R11 KC.
  pose proof (a5_geo B v pos lyc Sc Wc regsc memc mdc PF_SC_LINE HB) as (HAR & _ & _ & G & _).
  pose proof (a5_fi_regs B v pos lyc Sc Wc regsc memc mdc PF_SC_LINE HB) as HRG.
  destruct (a6lc_fi_get v regsc HRG) as (R2 & R3 & R4 & R8).
  pose proof G as (G1 & G2 & G3 & G4 & _).
  pose proof (a6_s1 (pf_sp0 v) G3) as (S1a & S1b & S1c & S1d). rewrite <- a6_s1_eq in S1a, S1b, S1c, S1d.
  pose proof STK_values as (_ & _ & _ & SPF & _).
  pose proof HB as (_ & (HJ & _) & HOBJ & _ & HFSH).
  pose proof HOBJ as (_ & _ & _ & _ & _ & _ & _ & _ & SSP).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  rewrite SPF in G1.
  assert (Hsp1 : spZ regsc = pf_s1 v) by (unfold spZ; rewrite R2; apply a6_w64_u; lia).
  assert (Hsp : spZ regsc = pf_sp0 v + (pf_s1 v - pf_sp0 v)) by lia.
  (* the window [s1 - 2 * ESTACK, s1): above alloc_ceiling, inside parse_file's own window *)
  assert (Hwin : alloc_ceiling <= spZ regsc - 2 * ESTACK) by (rewrite Hsp1; unfold ESTACK; lia).
  assert (Hbud : 2 * ESTACK - (pf_s1 v - pf_sp0 v) <= STK_reac_segconf_parse_file)
    by (rewrite SPF; unfold ESTACK; lia).
  (* the text and its tail from o *)
  destruct (a5_text B v pos lyc Sc Wc regsc memc mdc PF_SC_LINE HB) as (HN0 & _ & HSTR & _ & HHT & _).
  pose proof HHT as (bt & mt & Hbt & Hbt1 & Hbt2).
  destruct (a6_heap_bounds B lyc Sc Wc memc mdc (p_t v) (pf_len v) HAR HHT ltac:(unfold pf_len; lia))
    as (b2 & m2 & _ & Hb21 & Hb22 & Hb23 & Hb24 & Happ2).
  unfold pf_len in Hbt2, Hb22.
  assert (Hrng : forall a x, rdW Wc memc a = Some x -> 0 <= x < 256)
    by (intros a x Hx; destruct (aview_byte SEGS (w_H Wc) memc a x Hx) as (_ & _ & _ & Hr); exact Hr).
  assert (HSTRx : astr_at SEGS Wc memc (p_t v + Z.of_nat o) (seg_spec.zb (skipn o (p_s v)))).
  { apply astr_atR_view. apply (a6lc_astr_of_zs _ (p_t v) (p_s v) o Hrng (proj1 (proj1 HSTR)) HN0). lia. }
  assert (HLt : astr_len (seg_spec.zb (skipn o (p_s v))) = Z.of_nat (length (p_s v)) - Z.of_nat o)
    by (unfold astr_len, seg_spec.zb; rewrite length_map, length_skipn; lia).
  assert (Hx0 : 0 < p_t v + Z.of_nat o) by lia.
  assert (RDx : aread_ok SEGS (2 * ESTACK) Wc regsc memc (p_t v + Z.of_nat o)
    (astr_len (seg_spec.zb (skipn o (p_s v))) + 1)).
  { rewrite HLt. apply (aread_ok_of_block SEGS B LAWS (2 * ESTACK) lyc Sc Wc regsc memc mdc bt mt);
      [exact HAR | exact Hbt | lia | lia | lia | exact Hwin]. }
  assert (AMx : amem_range (p_t v + Z.of_nat o) (astr_len (seg_spec.zb (skipn o (p_s v))) + 8)).
  { rewrite HLt. unfold amem_range. unfold in_app in Happ2.
    destruct Happ2 as [_ [Hl | [Hh1 _]]].
    - left. unfold kLowShadowBeg, kLowMemEnd in *. lia.
    - right. unfold YG0f.kHighMemBeg, kHighMemEnd in *. lia. }
  assert (TVx : atail_vis SEGS Wc memc (p_t v + Z.of_nat o + astr_len (seg_spec.zb (skipn o (p_s v))))).
  { rewrite HLt. replace (p_t v + Z.of_nat o + (Z.of_nat (length (p_s v)) - Z.of_nat o))
      with (p_t v + Z.of_nat (length (p_s v))) by lia.
    exact (proj2 HSTR). }
  assert (HNZt : ~ In 0 (skipn o (p_s v))) by (intros Hx; exact (HN0 (a6lc_in_skipn _ _ _ Hx))).
  assert (HRt : Forall (fun x => 0 <= x < 256) (skipn o (p_s v))).
  { apply Forall_forall. intros x Hx. apply a6lc_in_skipn in Hx.
    pose proof (In_nth _ _ 0 Hx) as (i & Hi & Hxi). rewrite <- Hxi.
    exact (a6lc_zs_rng (rdW Wc memc) (p_t v) (p_s v) Hrng (proj1 (proj1 HSTR)) i Hi). }
  (* the set " \t\r": the third literal of PARSE_FILE_LITS *)
  assert (HINs : In [SP; TAB; CR] PARSE_FILE_LITS)
    by (unfold PARSE_FILE_LITS; apply in_or_app; left; do 2 right; left; reflexivity).
  destruct (a6lc_lit_read v pos lyc Sc Wc regsc memc mdc PF_SC_LINE regsc (2 * ESTACK) [SP; TAB; CR] HB HINs Hwin)
    as (Ly0 & LyA & LyL & LyR & LyM & LyT).
  assert (RDy : aread_ok SEGS (2 * ESTACK) Wc regsc memc (seg_litA_rc [SP; TAB; CR])
    (astr_len (seg_spec.zb [SP; TAB; CR]) + 1)) by (rewrite LyL; exact LyR).
  assert (AMy : amem_range (seg_litA_rc [SP; TAB; CR]) (astr_len (seg_spec.zb [SP; TAB; CR]) + 8))
    by (rewrite LyL; exact LyM).
  assert (TVy : atail_vis SEGS Wc memc (seg_litA_rc [SP; TAB; CR] + astr_len (seg_spec.zb [SP; TAB; CR])))
    by (rewrite LyL; exact LyT).
  (* the runtime-call pre-state with strspn's window, the read-only view *)
  assert (PRE : ecall_pre_stk SEGS B (2 * ESTACK) lyc Sc Wc regsc memc mdc).
  { apply (ecall_pre_stk_at SEGS B (2 * ESTACK) STK_reac_segconf_parse_file (pf_sp0 v)
      (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v) (p_mem v) (p_md v) [(5, pos)] lyc Sc Wc memc mdc 0
      regsc (pf_s1 v - pf_sp0 v) HJ Hsp S1d);
      [lia | unfold ESTACK; lia | exact Hbud | rewrite R1; exact Hraw | exact R3 | exact R4]. }
  pose proof (a5_rom B v pos lyc Sc Wc regsc memc mdc PF_SC_LINE HB) as ROM.
  (* the call *)
  eapply SRr_bind.
  { apply (aj_art_at SEGS B LAWS pa_segs_low (pal_env B TL) (2 * ESTACK) (fun _ => False)
      (SIG SS___interceptor_trampoline_strspn) Wc regsc memc STK_reac_segconf_parse_file (pf_sp0 v)
      (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v) (p_mem v) (p_md v) [(5, pos)] lyc Sc mdc 0
      (pf_s1 v - pf_sp0 v) raw
      (fun regs' _ => getr regs' 10 =
         w64 (Z.of_nat (strspn_c.spn_len (seg_spec.zb [SP; TAB; CR]) (seg_spec.zb (skipn o (p_s v))))))
      HJ Hsp S1d ltac:(lia) ltac:(unfold ESTACK; lia) Hbud R1 (fun a (H : False) => False_ind _ H)).
    exact (STRSPN fx lyc Sc Wc regsc memc mdc (p_t v + Z.of_nat o) (seg_litA_rc [SP; TAB; CR])
      (seg_spec.zb (skipn o (p_s v))) (seg_spec.zb [SP; TAB; CR]) SSP PRE R10 R11 Hx0 Ly0 HSTRx LyA
      RDx AMx RDy AMy TVx TVy ROM). }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Ha02 & HK2).
  (* what strspn kept: every byte off its window [s1 - 2 * ESTACK, s1) *)
  assert (HK0 : forall a, 0 <= a < 2 ^ 64 -> ~ (pf_s1 v - 2 * ESTACK <= a < pf_s1 v) ->
    rdW Wc mem2 a = rdW Wc memc a).
  { intros a Ha Hw. apply HK2; [exact Ha | | tauto]. intros Hw'. apply Hw. lia. }
  assert (HKW : forall sl shw a, 0 <= a < 2 ^ 64 -> ~ a5_Wrx v pos sl shw a -> rdW Wc mem2 a = rdW Wc memc a).
  { intros sl shw a Ha HW. apply HK0; [exact Ha|]. intros Hw. apply HW. left. rewrite SPF. unfold ESTACK in *.
    lia. }
  (* every mapped byte stays mapped: the window by the journal, the rest kept *)
  assert (HV : forall a, rdW Wc memc a <> None -> rdW Wc mem2 a <> None).
  { assert (HV0 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc memc a <> None -> rdW Wc mem2 a <> None).
    { intros a Ha Hs.
      destruct (Z_lt_le_dec a (pf_s1 v - 2 * ESTACK)) as [Hlo | Hlo];
        [|destruct (Z_lt_le_dec a (pf_s1 v)) as [Hhi | Hhi]].
      - rewrite (HK0 a Ha ltac:(lia)). exact Hs.
      - pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
        apply (aview_some_of_apresent SEGS). apply Hpres. rewrite SPF. unfold ESTACK in *. lia.
      - rewrite (HK0 a Ha ltac:(lia)). exact Hs. }
    intros a Hs. rewrite a6lc_view_wrap. rewrite a6lc_view_wrap in Hs.
    apply HV0; [apply Z.mod_pos_bound; lia | exact Hs]. }
  assert (HRG2 : pf_rg regs2 (a5_FI B v)) by exact (a5_rg_pres regsc regs2 _ HP2 (a5_FI_cs B v) HRG).
  assert (HFSH2 : pf_fsh (rdW Wc mem2) (pf_SH v pos) PF_SC_LINE)
    by exact (a5_keep_fsh v pos _ _ true PF_SC_LINE G (HKW true false) HFSH).
  assert (HSf : exists f, Sc = set_fs f Sc) by (exists (st_fs Sc); destruct Sc; reflexivity).
  pose proof (a5_move0 B v pos lyc Sc Wc regsc memc mdc PF_SC_LINE Sc Wc regs2 mem2 md2 PF_SC_LINE HB HJ2 HSf
    (Permutation_refl _) (HKW true true) HV HRG2 HFSH2) as HB2.
  apply (KC regs2 mem2 md2 HB2 HP2).
  - rewrite Ha02. do 2 f_equal. exact (a6_spn (skipn o (p_s v)) HNZt HRt).
  - intros a Ha Hlo. apply HK0; [exact Ha|]. unfold ESTACK in *. lia.
Qed.
End e.
End f.
End d.

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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 883 of its 935 lines of code are new or changed and 401 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/pf_a9_s1.v, with its module paths, module names and numbers changed; 392 of its 606 lines of code are new or changed and 721 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca): stretch SB9_2 of
   segment B9 of reac_segconf_parse_file's walk (lib/B/Prog/pf_seg_B9_d.v): J1 0x88404 -> REF3 0x882b4 (no '=') or
   J2 0x88428 (the NUL store at the '=' and trim(line)). A B9 sub-lane of the image-B G3 walk owner, 2026-10-30.
   proves no function (kind: segment lemma of reac_segconf_parse_file's walk: stretch SB9_2 of segment B9).
   ADAPTED from a working branch's lib/A/Prog/pf_a9_s1.v (A9's stretch SA9_A: its no-'=' arm s1_none, the
   buf strings after the NUL store and after trim, s1_prefix_str / s1_suffix_str / s1_key_str / s1_wbyte) and
   lib/A/Prog/pf_a9_s2.v (the trim call by PaNoChain.cl_callS_wide, the transport across it), re-derived on image B's
   code with image B's B9 kit (pf_seg_B9_k.v b9_move0 / b9_keep_*, pf_seg_B9_c.v b9_st, pf_seg_B9_cs.v
   b9_trim_site_ok) and the store-with-check form of lib/B/Prog/trim_f.v.

   THE CODE (reac_segconf_parse_file.fuzz_segconf.asan-ubsan.s; reac_segconf.c:215-221):
     0x88404 beqz a0,0x884ac                      strchr's answer r (INV_J1)
     r = None (s2_none; the seed pins a0 to 0 and holds c's slot s1 + 0xc8 as a read-only region on atom 9):
       0x884ac auipc a0; 0x884b0 addi a2,a0,500   a2 = 0x216a0 = seg_litA_rc F_neither (listing object 40)
       0x884b4 ld a0,200(s1)                      a0 = c
       0x884b8 mv a1,s6; 0x884bc mv a3,s7          a1 = lineno = ln + 1, a3 = lp (the line)
       0x884c0 j 0x882b4                          REF3, closed by H_REF3 with f = F_neither, args = [AS line],
                                                  cur' = the line's cur; r_key's no-'=' branch is b9_rkey_none
     r = Some ei (s2_found; the seed holds the byte eq = lp + ei as a writable one-byte region on atom 10 = a0,
       atom 10 in [4096, 2 ^ 47 - 1] (so `beqz` is decided), and the shadow base s4 = atom 20 = SHADOW_OFF):
       0x88408 mv s8,a0                           s8 = eq
       0x8840c .. 0x88418 check B#9               srli / add s4 / lb / bnez: store1 at eq, decided by the
                                                  token executor from the shadow entry of eq (buf's shadow is
                                                  0 under PF_SC_LINE: b9_addr_buf); slow path 0x88f84-0x88f8c and
                                                  error call 0x89264-0x89268 (errpath_store1) not reached
       0x8841c sb zero,0(s8)                      the '=' becomes the NUL (awr_ok: a byte of buf, the own
                                                  class-5 frame)
       0x88420 mv a0,s7; 0x88424 jal trim         trim(line), the string at lp now firstn ei line; stepped by
                                                  PaNoChain.cl_callS_wide with TRIM (its footprint, the NUL at
                                                  trim_end_addr, is a byte of the own frame); premises from
                                                  pf_seg_B9_cs.v b9_trim_site_ok; return 0x88428 = J2
     At J2: kp = lp + trim_lead K (K = firstn ei line), the key r_trim K at kp (trim's post bytes and
     lib/Prog/pfA_facts.v L_trim_holds, s2_key_str), kp + |key| <= lp + ei (L_trim_holds), the rest
     skipn (S ei) line at lp + ei + 1 (above both writes: eq and trim's NUL at or below eq), s8 = eq, a0 = kp.
   Instructions: 0x88404 - 0x88424 (9), 0x884ac - 0x884c0 (6) walked; 0x88f84 - 0x88f8c and 0x89264 - 0x89268 (5,
   check B#9's slow path and error call) excluded by the check: 20. Check B#9 discharged; no UBSan trap.
   SECTION HYPOTHESES: TRIM (trim_contract at BASE + AF_trim), SIGP (trim's call target), OBJ (the F_neither
   literal's listing object). *)
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
PaCallRun PaArt PaNoChain PaSB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import trim_c refuse_c reac_segconf_parse_file_c
  SegInstB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require reac_segconf_parse.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import pf_pieces pf_seg_B9_d pf_seg_B9_f
  pf_seg_B9_k pf_seg_B9_c pf_seg_B9_cs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ============================== small tools ============================== *)
Lemma s2_bvr : forall rr (r : bv 5) k v, bv_unsigned r = k -> getr rr (Z_to_bv 5 k) = v -> getr rr r = v.
Proof. intros rr r k v Hr H. subst k. rewrite Z_to_bv_bv_unsigned in H. exact H. Qed.
Lemma s2_bvr' : forall rr (r : bv 5) k v, bv_unsigned r = k -> getr rr r = v -> getr rr (Z_to_bv 5 k) = v.
Proof. intros rr r k v Hr H. subst k. rewrite Z_to_bv_bv_unsigned. exact H. Qed.
Lemma s2_m16 : forall a b, a mod 32 = 0 -> b mod 16 = 0 -> (a - b) mod 16 = 0.
Proof.
intros a b Ha Hb. pose proof (Z.div_mod a 32 ltac:(lia)) as Da. pose proof (Z.div_mod b 16 ltac:(lia)) as Db.
rewrite Ha in Da. rewrite Hb in Db.
replace (a - b) with ((2 * (a / 32) - b / 16) * 16) by lia. apply Z_mod_mult.
Qed.
(* a reader at a reads the byte at a mod 2 ^ 64 (mbyte goes through Z_to_bv 64) *)
Lemma s2_aview_mod : forall segs H m a, aview segs H m a = aview segs H m (a mod 2 ^ 64).
Proof.
intros segs H m a. unfold aview, mbyte.
replace (Z_to_bv 64 (a mod 2 ^ 64)) with (Z_to_bv 64 a); [reflexivity|].
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N]. rewrite Zmod_mod. reflexivity.
Qed.
(* a register list carried to a register file that agrees on every register it names *)
Lemma s2_rg_eq : forall (rX rX' : bvmap 5 word) L,
  (forall r v, In (r, v) L -> getr rX' (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)) -> pf_rg rX L -> pf_rg rX' L.
Proof.
intros rX rX' L HE H. unfold pf_rg in *. rewrite Forall_forall in *. intros [r v] Hin. cbn [fst snd] in *.
rewrite (HE r v Hin). exact (H (r, v) Hin).
Qed.
Ltac s2_in := cbn [In app]; repeat first [left; reflexivity | right].

(* ============================== C strings over readers (A9's pf_a9_s1_k.v / pf_a9_s1.v) ============================== *)
Lemma s2_str_some : forall (rd : reader) p s a, sa_str rd p s -> p <= a <= p + Z.of_nat (length s) ->
  rd a <> None.
Proof.
intros rd p s a [[Hz _] _] Ha.
assert (Hi : (Z.to_nat (a - p) < length (s ++ [0%Z]))%nat) by (rewrite length_app; cbn [length]; lia).
pose proof (Hz _ Hi) as E. rewrite Z2Nat.id in E by lia.
replace (p + (a - p)) with a in E by lia. rewrite E. discriminate.
Qed.
Lemma s2_str_nth : forall (rd : reader) p s i, sa_str rd p s -> (i <= length s)%nat ->
  rd (p + Z.of_nat i) = Some (nth i (s ++ [0]) 0).
Proof. intros rd p s i [[Hz _] _] Hi. apply Hz. rewrite length_app. cbn [length]. lia. Qed.
(* the mapped span of a C string at p: its bytes, its NUL and the slack to the next 8-byte boundary *)
Definition s2_span (p : Z) (s : list Z) : Z := p + Z.of_nat (length s) - (p + Z.of_nat (length s)) mod 8 + 8.
Lemma s2_span_some : forall (rd : reader) p s y, sa_str rd p s -> p <= y < s2_span p s -> rd y <> None.
Proof.
intros rd p s y Hs Hy. unfold s2_span in Hy.
destruct (Z_le_gt_dec y (p + Z.of_nat (length s))) as [H1 | H1].
- exact (s2_str_some rd p s y Hs ltac:(lia)).
- destruct Hs as [_ Ht]. apply Ht. lia.
Qed.
Lemma s2_span_mono : forall p s e, p <= e <= p + Z.of_nat (length s) -> e - e mod 8 + 8 <= s2_span p s.
Proof.
intros p s e He. unfold s2_span.
pose proof (Z.div_mod e 8 ltac:(lia)). pose proof (Z.mod_pos_bound e 8 ltac:(lia)).
pose proof (Z.div_mod (p + Z.of_nat (length s)) 8 ltac:(lia)).
pose proof (Z.mod_pos_bound (p + Z.of_nat (length s)) 8 ltac:(lia)).
assert (e / 8 <= (p + Z.of_nat (length s)) / 8) by (apply Z.div_le_mono; lia). lia.
Qed.
(* a C string out of its bytes, the NUL and a mapped slack *)
Lemma s2_sa_str_of : forall (rd : reader) q l,
  (forall i, (i < length l)%nat -> rd (q + Z.of_nat i) = Some (nth i l 0)) ->
  rd (q + Z.of_nat (length l)) = Some 0 -> ~ In 0 l ->
  (forall y, q + Z.of_nat (length l) < y < q + Z.of_nat (length l) - (q + Z.of_nat (length l)) mod 8 + 8 ->
     rd y <> None) ->
  sa_str rd q l.
Proof.
intros rd q l Hb H0 Hn Ht. split; [split|].
- intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
  destruct (Nat.lt_ge_cases i (length l)) as [Hl | Hl].
  + rewrite app_nth1 by exact Hl. exact (Hb i Hl).
  + assert (i = length l) as -> by lia. rewrite app_nth2 by lia. rewrite Nat.sub_diag. exact H0.
- exact Hn.
- intros y Hy. exact (Ht y Hy).
Qed.
(* the store of a NUL at p + k into the C string s at p leaves its first k bytes a C string *)
Lemma s2_prefix_str : forall (rd rd' : reader) p s k,
  sa_str rd p s -> (k <= length s)%nat ->
  (forall a, p <= a < s2_span p s -> a <> p + Z.of_nat k -> rd' a = rd a) ->
  rd' (p + Z.of_nat k) = Some 0 ->
  sa_str rd' p (firstn k s).
Proof.
intros rd rd' p s k Hs Hk HK H0.
pose proof Hs as [[Hz Hn] Ht].
assert (Lk : length (firstn k s) = k) by (rewrite length_firstn; lia).
pose proof (Z.div_mod (p + Z.of_nat (length s)) 8 ltac:(lia)).
pose proof (Z.mod_pos_bound (p + Z.of_nat (length s)) 8 ltac:(lia)).
pose proof (s2_span_mono p s (p + Z.of_nat k) ltac:(lia)) as Hm.
apply s2_sa_str_of.
- intros i Hi. rewrite Lk in Hi. rewrite HK; [| unfold s2_span; lia | lia].
  rewrite (s2_str_nth rd p s i Hs ltac:(lia)). rewrite app_nth1 by lia. rewrite nth_firstn.
  replace ((i <? k)%nat) with true by (symmetry; apply Nat.ltb_lt; lia). reflexivity.
- rewrite Lk. exact H0.
- intros Hin. apply Hn. exact (b9_in_firstn k s 0 Hin).
- intros y Hy. rewrite Lk in Hy. rewrite HK; [| lia | lia].
  apply (s2_span_some rd p s y Hs). lia.
Qed.
(* the bytes of the C string s from k on, at p + k, when the reader agrees there *)
Lemma s2_suffix_str : forall (rd rd' : reader) p s k,
  sa_str rd p s -> (k <= length s)%nat ->
  (forall a, p + Z.of_nat k <= a < s2_span p s -> rd' a = rd a) ->
  sa_str rd' (p + Z.of_nat k) (skipn k s).
Proof.
intros rd rd' p s k Hs Hk HK.
pose proof Hs as [[Hz Hn] Ht].
assert (Lk : length (skipn k s) = (length s - k)%nat) by (rewrite length_skipn; lia).
pose proof (Z.div_mod (p + Z.of_nat (length s)) 8 ltac:(lia)).
pose proof (Z.mod_pos_bound (p + Z.of_nat (length s)) 8 ltac:(lia)).
apply s2_sa_str_of.
- intros i Hi. rewrite Lk in Hi. rewrite HK by (unfold s2_span; lia).
  replace (p + Z.of_nat k + Z.of_nat i) with (p + Z.of_nat (k + i)) by lia.
  rewrite (s2_str_nth rd p s (k + i) Hs ltac:(lia)). rewrite app_nth1 by lia.
  rewrite nth_skipn_add. reflexivity.
- rewrite Lk. rewrite HK by (unfold s2_span; lia).
  replace (p + Z.of_nat k + Z.of_nat (length s - k)) with (p + Z.of_nat (length s)) by lia.
  rewrite (s2_str_nth rd p s (length s) Hs ltac:(lia)). rewrite app_nth2 by lia. rewrite Nat.sub_diag.
  reflexivity.
- intros Hin. apply Hn. exact (b9_in_skipn k s 0 Hin).
- intros y Hy. rewrite Lk in Hy.
  replace (p + Z.of_nat k + Z.of_nat (length s - k)) with (p + Z.of_nat (length s)) in Hy by lia.
  rewrite HK by (unfold s2_span; lia). exact (Ht y Hy).
Qed.

(* ============================== the seeds (pure data) ============================== *)
(* r = None: a0 pinned to 0 (the run reads it at `beqz`), c's slot s1 + 0xc8 a read-only region on s1's atom 9
   whose chunk is the extra atom 32 = c *)
Definition s2_rN : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0xc8 0xd0 0 0 [YP09.mkChunk 0xc8 (CVal 8 (SOff 32 0))].
Definition s2_ssN : sstate :=
  mkSS B9_J1 (sr_set sr_atoms (Z_to_bv 5 10) (SLit 0)) [s2_rN] None (mkFacts [] [] []).
(* r = Some ei: the byte eq (a0's atom 10) writable, eq's range (so `beqz a0` is decided) and the shadow base
   s4 = atom 20 = SHADOW_OFF (pf_fi) for the token executor *)
Definition s2_rF : smem := [YP09.mkRegion (Some 10%nat) 0 1 0 1 []].
Definition s2_fF : facts := mkFacts [(10%nat, mkAF 4096 (2 ^ 47 - 1) 0); (20%nat, mkAF SB SB 0)] [] [].
Definition s2_ssF : sstate := mkSS B9_J1 sr_atoms s2_rF None s2_fF.
Definition s2_SH : list shent := [mkSHE 10 0 1].

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ seg_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* the byte a run wrote into a one-byte written region, at a call stop (pf_a9_s1.v s1_wbyte) *)
Lemma s2_wbyte : forall E ss ms (H : word -> bool) (n i : nat) Pz v,
  st_ok SEGS E ss (restrict H ms) ->
  nth_error (ss_mem ss) i = Some (YP09.mkRegion (Some n) 0 1 0 1 [YP09.mkChunk 0 (CVal 1 v)]) ->
  bv_unsigned (ew E n) = Pz ->
  aview SEGS H (ms_mem ms) Pz = Some (bv_unsigned (sv_denot E v) mod 256).
Proof.
intros E ss ms H n i Pz v HS Hn HP.
pose proof (st_ok_region_nth E ss (restrict H ms) i _ HS Hn) as Hr.
pose proof (field_of_region_any E _ n Pz _ 0 1 0 1 0 1%N v Hr HP (or_introl eq_refl) ltac:(lia)) as V.
cbn [ms_mem restrict] in V. rewrite Z.add_0_r in V. change (2 ^ (8 * Z.of_N 1)) with 256 in V.
apply aview_of_val_mem1; [exact V | apply Z.mod_pos_bound; lia].
Qed.

(* trim's answer at p: the C string at p + trim_lead K is r_trim K (trim_c.v's post bytes and pfA_facts.v
   L_trim_holds; pf_a9_s1.v s1_key_str) *)
Lemma s2_key_str : forall (W W2 : world SEGS) mem mem2 p K,
  sa_str (rdW W mem) p K ->
  sa_bytes (rdW W2 mem2) p
    (seg_spec.zb (firstn (seg_spec.trim_lead K + length (r_trim K)) K) ++ [seg_spec.ZERO]) ->
  (forall a, rdW W mem a <> None -> rdW W2 mem2 a <> None) ->
  sa_str (rdW W2 mem2) (p + Z.of_nat (seg_spec.trim_lead K)) (r_trim K).
Proof.
intros W W2 mem mem2 p K Hs HBY HV.
pose proof Hs as [[Hz Hn] Ht].
pose proof (L_trim_holds K Hn) as (L1 & L2 & L3).
set (ld := seg_spec.trim_lead K) in *. set (rt := r_trim K) in *.
assert (HR : forall j, (j < length K)%nat -> 0 <= nth j K 0 < 256).
{ intros j Hj. pose proof (s2_str_nth _ p K j Hs ltac:(lia)) as E. rewrite app_nth1 in E by exact Hj.
  exact (sa_aview_rng SEGS _ _ _ _ E). }
assert (HLB : length (seg_spec.zb (firstn (ld + length rt) K)) = (ld + length rt)%nat)
  by (unfold seg_spec.zb; rewrite length_map, length_firstn; lia).
assert (HNTH : forall i, (i < length rt)%nat -> nth i rt 0 = nth (ld + i) K 0).
{ intros i Hi. rewrite L2, nth_firstn.
  replace ((i <? length rt)%nat) with true by (symmetry; apply Nat.ltb_lt; exact Hi).
  rewrite nth_skipn_add. reflexivity. }
apply s2_sa_str_of.
- intros i Hi.
  replace (p + Z.of_nat ld + Z.of_nat i) with (p + Z.of_nat (ld + i)) by lia.
  rewrite (HBY (ld + i)%nat) by (rewrite length_app, HLB; cbn [length]; lia). f_equal.
  rewrite app_nth1 by (rewrite HLB; lia). unfold seg_spec.zb, ZB0.
  rewrite (map_nth (Z_to_bv 8) (firstn (ld + length rt) K) 0 (ld + i)).
  rewrite nth_firstn. replace ((ld + i <? ld + length rt)%nat) with true by (symmetry; apply Nat.ltb_lt; lia).
  rewrite HNTH by exact Hi.
  rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 8) with 256. apply HR. lia.
- replace (p + Z.of_nat ld + Z.of_nat (length rt)) with (p + Z.of_nat (ld + length rt)) by lia.
  rewrite (HBY (ld + length rt)%nat) by (rewrite length_app, HLB; cbn [length]; lia).
  rewrite app_nth2 by (rewrite HLB; lia). rewrite HLB, Nat.sub_diag. reflexivity.
- exact L3.
- intros y Hy. apply HV.
  replace (p + Z.of_nat ld + Z.of_nat (length rt)) with (p + Z.of_nat (ld + length rt)) in Hy by lia.
  apply (s2_span_some _ p K y Hs).
  pose proof (s2_span_mono p K (p + Z.of_nat (ld + length rt)) ltac:(lia)) as Hm. lia.
Qed.

Variable B : asyms.
(* trim (lib/B/Prog/trim_c.v) at image B's numbers, at every FP state *)
Hypothesis TRIM : forall fx0 : YK11.FPState, trim_contract (fx := fx0) SEGS B (BASE + AF_trim) STK_trim RLO_A RHI_A.
(* the listing's facts over the abstract instance (B's SegObj.v): call targets, object values *)
Hypothesis SIGP : seg_sig_prog (PI := PI).
Hypothesis OBJ : seg_val_objs (PI := PI).

(* the F_neither literal's atom: listing object 40 (0x216a0, B's SegAddr.v seg_objs) *)
Lemma s2_neither_atom : forall E, img_env VAL A_LIM E -> ew E 281%nat = w64 (seg_litA_rc F_neither).
Proof.
intros E HE. rewrite (img_env_atomP E 281%nat HE) by (unfold A_TEXT, A_LIM; lia).
change 281%nat with (A_OBJ 40). rewrite (OBJ 40%nat ltac:(apply Nat.ltb_lt; vm_compute; reflexivity)).
unfold w64; f_equal; vm_compute; reflexivity.
Qed.

Ltac s2_kept HS EE :=
  lazymatch goal with |- getr _ (Z_to_bv 5 ?r) = getr _ (Z_to_bv 5 ?r) =>
    let H := fresh "Hk" in prreg HS (Z_to_bv 5 r) H; rewrite H; apply EE; reflexivity end.

Section x.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUN := paj_run (fx := fx) B LAWS.
Let RUNTO := paj_run_to (fx := fx) B LAWS.

(* ---------- r = None: 0x88404 beqz (taken) .. 0x884ac .. 0x884c0 j REF3 ---------- *)
Lemma s2_none : forall n x lyc Sc Wc rX memc mdc,
  INV_J1 B n x None lyc Sc Wc rX memc mdc -> H_REF3 B n ->
  SRr SEGS Wc (cfg_at SEGS (BASE + B9_J1) rX memc mdc) (b9_goal B x).
Proof.
intros n x lyc Sc Wc rX memc mdc HI HR3.
destruct HI as (HC & (HSTR & HINB) & HNONE & HRG).
pose proof HC as (HB & HMID & HST & HLEN & HD0 & HDL).
pose proof (b9_geo B _ _ _ _ _ _ _ _ _ HB) as (HAR & Hly & Hin & G & HFP & HSP).
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
pose proof HB as (HCX & HFI & HOBJ & HSL & HFSH).
pose proof HFI as (HJ & _ & _ & _ & _ & _ & _ & _ & HSLC & HRG0).
pose proof HCX as (_ & _ & _ & Hc64 & _).
pose proof STK_values as (STR & _ & _ & SPF & _).
pose proof asan_consts as (C1 & _).
rewrite SPF in G1.
pose proof HINB as [Hib1 Hib2]. unfold b9_buf, PF_O_BUF in Hib1, Hib2.
unfold B9_R, PF_RL, PF_RM in HRG.
assert (WC8 : rdword (rdW Wc memc) (pf_s1 (y_v x) + 0xc8) = Some (p_c (y_v x)))
  by exact (proj1 (Forall_forall _ _) HSLC (0xc8, p_c (y_v x)) (or_introl eq_refl)).
assert (R9 : getr rX (Z_to_bv 5 9) = w64 (pf_s1 (y_v x))) by (apply (b9_rg_get _ _ 9 _ HRG0); s2_in).
assert (R10 : getr rX (Z_to_bv 5 10) = w64 0) by (apply (b9_rg_get _ _ 10 _ HRG); s2_in).
assert (R22 : getr rX (Z_to_bv 5 22) = w64 (y_ln x + 1)) by (apply (b9_rg_get _ _ 22 _ HRG); s2_in).
assert (R23 : getr rX (Z_to_bv 5 23) = w64 (y_lp x)) by (apply (b9_rg_get _ _ 23 _ HRG); s2_in).
(* the seed *)
set (E := Eimg (Ereg rX [w64 (p_c (y_v x))])).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr rX r)
  by (intros k r Hk; subst E; apply ew_Eimg_Ereg_nat; exact Hk).
assert (E32 : ew E 32 = w64 (p_c (y_v x)))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 0)).
assert (U9 : bv_unsigned (ew E 9) = pf_s1 (y_v x))
  by (rewrite (EE 9%nat (Z_to_bv 5 9) eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
assert (HS : st_ok_pi SEGS VAL E s2_ssN
  (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + B9_J1)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx.
  assert (HS1 : st_ok_pi SEGS VAL E (mkSS B9_J1 sr_atoms [s2_rN] None (mkFacts [] [] []))
    (mkst rX (Z_to_bv 64 (BASE + B9_J1)) (mrestrict (w_H Wc) memc) (seg_rom SEGS))).
  { apply pa_entry_st_ok_full.
    - subst E. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - apply Forall_cons; [|apply Forall_nil]. unfold region_ok, s2_rN.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U9.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E _ (pf_s1 (y_v x)) 0xc8 8 (SOff 32 0) (p_c (y_v x)));
        [cbn [sv_denot]; rewrite E32, Z.add_0_r; unfold w64; rewrite unsigned_lit_small by lia; reflexivity
        | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | lia |].
      exact (val_mem_of_rdword SEGS (w_H Wc) memc _ _ WC8).
    - cbn [pairwise_disjoint all_disjoint]. split; exact I.
    - split; [exact I | split; exact I]. }
  exact (st_ok_pi_pin_reg' E _ _ (Z_to_bv 5 10) 0 HS1 R10 eq_refl). }
clearbody E.
assert (SHOK : sh_ok SEGS (SOff 20 0) [] E (mrestrict (w_H Wc) memc)) by constructor.
unfold cfg_at. change (w64 (BASE + B9_J1)) with (Z_to_bv 64 (BASE + B9_J1)).
(* 0x88404 beqz a0 (a0 = 0, taken) .. 0x884c0 j 0x882b4 *)
paj_run_to_tok RUNTO HS HJ SHOK Bspan PF_REF3.
{ lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr0 lyx own) end.
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
assert (KM1 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
{ intros a Ha. apply (kept_of_frame (segs := SEGS) E _ (w_H Wc) memc (ms_mem ms) (fun _ => False) HFr);
    [|exact Ha | tauto].
  intros b wlo whi a' Hin' Hrr. vm_compute in Hin'.
  repeat (destruct Hin' as [Hq | Hin']; [injection Hq as <- <- <-; cbn [base_val] in Hrr; lia |]). destruct Hin'. }
assert (KV : forall a, rdW Wc memc a <> None -> rdW Wc (ms_mem ms) a <> None)
  by (intros a Hv; exact (aview_keeps_vis SEGS (w_H Wc) memc (ms_mem ms) a HG Hv)).
clear HFr HG HF.
set (mdv := with_vm_backing _ _ _) in *; clearbody mdv.
prreg HS (Z_to_bv 5 10) Q10. prreg HS (Z_to_bv 5 11) Q11. prreg HS (Z_to_bv 5 12) Q12.
prreg HS (Z_to_bv 5 13) Q13.
assert (QK : forall r, In r [2; 3; 4; 8; 9; 20; 18; 21; 26; 25; 22] ->
    getr (ms_regs ms) (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)).
{ intros r Hr. cbn [In] in Hr.
  repeat (destruct Hr as [<- | Hr]; [s2_kept HS EE |]). destruct Hr. }
pmkst HS.
(* the cut's frame state at REF3: nothing was written *)
assert (KW : forall a, 0 <= a < 2 ^ 64 -> ~ b9_Wrx (y_v x) (y_pos x) true a -> rdW Wc (ms_mem ms) a = rdW Wc memc a)
  by (intros a Ha _; exact (KM1 a Ha)).
assert (HFI1 : pf_rg (ms_regs ms) (b9_FI B (y_v x))).
{ unfold b9_FI, pf_rg. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
    (rewrite QK; [apply (b9_rg_get rX _ _ _ HRG0); s2_in | s2_in]). }
assert (HB1 : pf_base B (y_v x) (y_pos x) lyc Sc Wc (ms_regs ms) (ms_mem ms) mdv PF_SC_LINE).
{ eapply (b9_move0 B (y_v x) (y_pos x) lyc Sc Wc rX memc mdc PF_SC_LINE Sc Wc (ms_regs ms) (ms_mem ms) mdv
    PF_SC_LINE HB HJ);
    [exists (st_fs Sc); destruct Sc; reflexivity | apply Permutation_refl | exact KW | exact KV | exact HFI1 |].
  eapply b9_keep_fsh; [exact G | exact KW | exact HFSH]. }
assert (HC5 : sa_heap B lyc Sc (p_c (y_v x)) seg_spec.SEG_C_SIZE)
  by (destruct HOBJ as (_ & _ & _ & _ & H5 & _); exact H5).
assert (HLp0 : 0 <= y_lp x) by lia.
assert (HLp1 : y_lp x + Z.of_nat (length (b9_line x)) < alloc_ceiling) by lia.
assert (HSTR1 : sa_str (rdW Wc (ms_mem ms)) (y_lp x) (b9_line x)).
{ apply (reac_segconf_parse.sa_str_low _ _ _ _ HSTR HLp0 HLp1). intros a Ha. apply KM1. lia. }
(* REF3 with f = F_neither, args = [AS line], a3 = lp, cur' = the line's cur *)
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg (Z_to_bv 64 (_ + ?k)) ?mm ?rom) ?mdx) _ =>
  change (mkCfg (mkst rg (Z_to_bv 64 (BASE + k)) mm rom) mdx) with (cfg_at SEGS (BASE + PF_REF3) rg mm mdx) end.
unfold b9_goal. rewrite (b9_rkey_none (y_cf x) (y_cur x) (y_nm x) (y_ln x + 1) (b9_line x) HNONE).
apply (HR3 (y_v x) (y_pos x) lyc Sc Wc (ms_regs ms) (ms_mem ms) mdv (y_cf x) (y_cur x) (y_nm x) (y_o x)
  (y_ln x) (y_d x) F_neither (seg_litA_rc F_neither) [AS (b9_line x)] (y_lp x)).
split; [exact HB1|]. split; [exact HMID|].
split.
{ change (length (skipn (y_o x) (p_s (y_v x)))) with (b9_k x).
  eapply b9_keep_st; eassumption. }
split.
{ right. split; [reflexivity|]. split; [reflexivity|]. exists (b9_line x). split; [reflexivity|].
  split; [exact HSTR1 | exact HINB]. }
unfold pf_rg, PF_RL, PF_RM. cbn [app].
repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
- rewrite QK; [apply (b9_rg_get rX _ _ _ HRG); s2_in | s2_in].
- rewrite QK; [apply (b9_rg_get rX _ _ _ HRG); s2_in | s2_in].
- rewrite QK; [apply (b9_rg_get rX _ _ _ HRG); s2_in | s2_in].
- rewrite QK; [apply (b9_rg_get rX _ _ _ HRG); s2_in | s2_in].
- rewrite QK; [apply (b9_rg_get rX _ _ _ HRG); s2_in | s2_in].
- rewrite Q10, E32. reflexivity.
- rewrite Q11, (EE 22%nat (Z_to_bv 5 22) eq_refl). exact R22.
- rewrite Q12. exact (s2_neither_atom E HEI).
- rewrite Q13, (EE 23%nat (Z_to_bv 5 23) eq_refl). exact R23.
Qed.

(* ---------- r = Some ei: 0x88404 beqz (not taken) .. check B#9, sb zero,0(s8), trim(line) .. J2 0x88428 ---------- *)
Lemma s2_found : forall n x ei lyc Sc Wc rX memc mdc,
  INV_J1 B n x (Some ei) lyc Sc Wc rX memc mdc -> from_J2 B n ->
  SRr SEGS Wc (cfg_at SEGS (BASE + B9_J1) rX memc mdc) (b9_goal B x).
Proof.
intros n x ei lyc Sc Wc rX memc mdc HI FJ2.
unfold from_J2, b9_from in FJ2.
destruct HI as (HC & (HSTR & HINB) & HCH & HRG).
pose proof HC as (HB & HMID & HST & HLEN & HD0 & HDL).
pose proof (b9_geo B _ _ _ _ _ _ _ _ _ HB) as (HAR & Hly & Hin & G & HFP & HSP).
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
pose proof (b9_st_of_base B _ _ _ _ _ _ _ _ HB) as HST0.
pose proof HB as (HCX & HFI & HOBJ & HSL & HFSH).
pose proof HFI as (HJ & _ & _ & _ & _ & _ & _ & _ & _ & HRG0).
pose proof STK_values as (STR & _ & _ & SPF & _).
pose proof asan_consts as (C1 & _).
pose proof pa_B_ok as (HB0 & HB40 & _).
rewrite SPF in G1.
pose proof HINB as [Hib1 Hib2]. unfold b9_buf, PF_O_BUF in Hib1, Hib2.
destruct (b9_strchr_lt _ _ _ HCH) as (Hei & _).
assert (HNZ : ~ In 0 (b9_line x)) by (destruct HSTR as ((_ & H0) & _); exact H0).
assert (HKlen : length (firstn ei (b9_line x)) = ei) by (rewrite length_firstn; lia).
assert (HNZK : ~ In 0 (firstn ei (b9_line x))) by (intros Hk; apply HNZ; exact (b9_in_firstn _ _ _ Hk)).
pose proof (L_trim_holds _ HNZK) as (HLT & _ & _).
rewrite HKlen in HLT.
assert (HTE : y_lp x <= trim_end_addr (y_lp x) (firstn ei (b9_line x)) <= y_lp x + Z.of_nat ei)
  by (unfold trim_end_addr; lia).
unfold B9_R, PF_RL, PF_RM in HRG.
assert (R10 : getr rX (Z_to_bv 5 10) = w64 (y_lp x + Z.of_nat ei)) by (apply (b9_rg_get _ _ 10 _ HRG); s2_in).
assert (R20 : getr rX (Z_to_bv 5 20) = w64 SHADOW_OFF) by (apply (b9_rg_get _ _ 20 _ HRG0); s2_in).
assert (R23 : getr rX (Z_to_bv 5 23) = w64 (y_lp x)) by (apply (b9_rg_get _ _ 23 _ HRG); s2_in).
(* the seed *)
set (E := Eimg (Ereg rX [])).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr rX r)
  by (intros k r Hk; subst E; apply ew_Eimg_Ereg_nat; exact Hk).
assert (U10 : bv_unsigned (ew E 10) = y_lp x + Z.of_nat ei)
  by (rewrite (EE 10%nat (Z_to_bv 5 10) eq_refl), R10; unfold w64; apply unsigned_lit_small; lia).
assert (U20 : bv_unsigned (ew E 20) = SB)
  by (rewrite (EE 20%nat (Z_to_bv 5 20) eq_refl), R20; unfold w64, SB, SHADOW_OFF; apply unsigned_lit_small; lia).
assert (HS : st_ok_pi SEGS VAL E s2_ssF
  (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + B9_J1)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold s2_ssF. apply pa_entry_st_ok_full.
  - subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - unfold s2_rF. apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U10. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. assert (o = 0) as -> by lia. rewrite Z.add_0_r. apply (apresent_writable SEGS). apply HFP. lia.
  - cbn. tauto.
  - split; [|split; exact I]. cbn [s2_fF f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U10, U20. rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SB. repeat split; lia. }
(* the shadow entry of eq (check B#9): buf's shadow is 0 under PF_SC_LINE *)
assert (SHOK : sh_ok SEGS (SOff 20 0) s2_SH E (mrestrict (w_H Wc) memc)).
{ unfold sh_ok, s2_SH. apply Forall_cons; [|apply Forall_nil].
  pose proof (b9_addr_buf B (y_v x) (y_pos x) lyc Sc Wc memc mdc (y_lp x + Z.of_nat ei) 1 HST0
    ltac:(unfold b9_bufp, PF_O_BUF; lia) ltac:(lia) ltac:(unfold b9_bufp, PF_O_BUF; lia)) as (_ & _ & _ & HRAe & _).
  assert (UB : U E (SOff 20 0) = SHADOW_OFF)
    by (apply U_atom; [rewrite (EE 20%nat (Z_to_bv 5 20) eq_refl); exact R20 | unfold SHADOW_OFF; lia]).
  assert (UE : U E (SOff 10 0) = y_lp x + Z.of_nat ei)
    by (apply U_atom; [rewrite (EE 10%nat (Z_to_bv 5 10) eq_refl); exact R10 | lia]).
  eapply (shent_ok_of_range SEGS (w_H Wc) memc E (SOff 20 0) 10%nat (y_lp x + Z.of_nat ei) 1
    (y_lp x + Z.of_nat ei) 0 1 HRAe UB UE); [lia | lia |].
  intros y Hy. change (Z.min 0 1) with 0 in Hy. change (Z.max 0 1) with 1 in Hy.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in G9. unfold SHADOW_OFF. lia. }
clearbody E.
unfold cfg_at. change (w64 (BASE + B9_J1)) with (Z_to_bv 64 (BASE + B9_J1)).
(* 0x88404 beqz a0 (not taken: eq >= 4096) .. check B#9 .. 0x8841c sb zero,0(s8) .. 0x88424 jal trim *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr0 lyx own) end.
  eapply awr_ok_cons_gen with (n := 10%nat) (b := y_lp x + Z.of_nat ei); [reflexivity | exact U10 | | apply awr_ok_nil].
  intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha.
  right; right; right; left. exists 5, (y_pos x). split; [left; reflexivity|].
  left. unfold in_zr. cbn [fst snd]. rewrite Hly.
  change (frame_addr (p_ly (y_v x)) 5 (y_pos x)) with (pf_F (y_v x) (y_pos x)).
  change (fs_frame_bytes 5) with 2048. lia. }
(* the bytes the run kept: all but eq; eq holds the NUL *)
assert (KM : forall a, 0 <= a < 2 ^ 64 -> a <> y_lp x + Z.of_nat ei -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
{ intros a Ha Hne.
  apply (kept_of_frame (segs := SEGS) E _ (w_H Wc) memc (ms_mem ms) (fun a' => a' = y_lp x + Z.of_nat ei) HFr);
    [|exact Ha | exact Hne].
  intros b wlo whi a' Hin' Hrr. vm_compute in Hin'.
  destruct Hin' as [Hq | []]; injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite U10 in Hrr; lia. }
assert (HW0 : rdW Wc (ms_mem ms) (y_lp x + Z.of_nat ei) = Some 0).
{ pose proof (s2_wbyte _ _ _ _ 10%nat 0%nat (y_lp x + Z.of_nat ei) (SLit 0) HS ltac:(vm_compute; reflexivity)) as V.
  rewrite V; [reflexivity|]. cbn [extK ewset ew]. exact U10. }
assert (KV : forall a, rdW Wc memc a <> None -> rdW Wc (ms_mem ms) a <> None)
  by (intros a Hv; exact (aview_keeps_vis SEGS (w_H Wc) memc (ms_mem ms) a HG Hv)).
clear HFr HG HF.
set (mdv := with_vm_backing _ _ _) in *; clearbody mdv.
(* the registers at the call *)
prreg HS (1%bv : bv 5) Q1. prreg HS (Z_to_bv 5 10) Q10. prreg HS (Z_to_bv 5 24) Q24.
assert (QK : forall r v, In (r, v) (b9_FI B (y_v x) ++ B9_R x ++ [(23, y_lp x)]) ->
    getr (ms_regs ms) (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)).
{ intros r v Hr. unfold b9_FI, B9_R, PF_RL, PF_RM in Hr. cbn [In app] in Hr.
  repeat (destruct Hr as [Hr | Hr]; [injection Hr as <- _; s2_kept HS EE |]). destruct Hr. }
pmkst HS.
assert (RG1 : pf_rg rX (b9_FI B (y_v x) ++ B9_R x ++ [(23, y_lp x)])).
{ apply b9_rg_app. split; [exact HRG0|].
  unfold B9_R, PF_RL, PF_RM.
  eapply b9_rg_incl; [|exact HRG].
  intros rv Hrv. cbn [In app] in Hrv |- *. tauto. }
pose proof (s2_rg_eq _ _ _ QK RG1) as RGm.
assert (HFI1 : pf_rg (ms_regs ms) (b9_FI B (y_v x)))
  by (exact (proj1 (proj1 (b9_rg_app _ _ _) RGm))).
assert (RGR1 : pf_rg (ms_regs ms) (B9_R x)).
{ apply (b9_rg_incl _ (b9_FI B (y_v x) ++ B9_R x ++ [(23, y_lp x)])); [|exact RGm].
  intros rv Hrv. apply in_or_app. right. apply in_or_app. left. exact Hrv. }
assert (C2 : getr (ms_regs ms) 2 = w64 (pf_s1 (y_v x))).
{ apply (s2_bvr _ 2%bv 2); [reflexivity|]. apply (b9_rg_get _ _ 2 _ HFI1). unfold b9_FI; s2_in. }
assert (C3 : getr (ms_regs ms) 3 = w64 (as_gp B)).
{ apply (s2_bvr _ 3%bv 3); [reflexivity|]. apply (b9_rg_get _ _ 3 _ HFI1). unfold b9_FI; s2_in. }
assert (C4 : getr (ms_regs ms) 4 = w64 (as_tp B)).
{ apply (s2_bvr _ 4%bv 4); [reflexivity|]. apply (b9_rg_get _ _ 4 _ HFI1). unfold b9_FI; s2_in. }
assert (C8 : getr (ms_regs ms) 8 = w64 (pf_sp0 (y_v x))).
{ apply (s2_bvr _ 8%bv 8); [reflexivity|]. apply (b9_rg_get _ _ 8 _ HFI1). unfold b9_FI; s2_in. }
assert (C1r : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + B9_J2)) by (rewrite Q1; reflexivity).
assert (C10 : getr (ms_regs ms) 10 = w64 (y_lp x)).
{ apply (s2_bvr _ 10%bv 10); [reflexivity|]. rewrite Q10, (EE 23%nat (Z_to_bv 5 23) eq_refl). exact R23. }
assert (C24 : getr (ms_regs ms) (Z_to_bv 5 24) = w64 (y_lp x + Z.of_nat ei)).
{ rewrite Q24, (EE 10%nat (Z_to_bv 5 10) eq_refl). exact R10. }
assert (Csp : spZ (ms_regs ms) = pf_sp0 (y_v x) + (pf_s1 (y_v x) - pf_sp0 (y_v x))).
{ unfold spZ. rewrite C2. unfold w64. rewrite unsigned_lit_small by lia. lia. }
assert (Ho16 : (pf_s1 (y_v x) - pf_sp0 (y_v x)) mod 16 = 0) by (apply s2_m16; [exact G5 | exact G3]).
(* the cut's frame state at the call: only eq (a byte of buf) was written *)
assert (KW1 : forall a, 0 <= a < 2 ^ 64 -> ~ b9_Wrx (y_v x) (y_pos x) true a ->
    rdW Wc (ms_mem ms) a = rdW Wc memc a).
{ intros a Ha Hw. apply KM; [exact Ha|]. intros ->. apply Hw. right; right. unfold PF_O_BUF. lia. }
assert (HB1 : pf_base B (y_v x) (y_pos x) lyc Sc Wc (ms_regs ms) (ms_mem ms) mdv PF_SC_LINE).
{ eapply (b9_move0 B (y_v x) (y_pos x) lyc Sc Wc rX memc mdc PF_SC_LINE Sc Wc (ms_regs ms) (ms_mem ms) mdv
    PF_SC_LINE HB HJ);
    [exists (st_fs Sc); destruct Sc; reflexivity | apply Permutation_refl | exact KW1 | exact KV | exact HFI1 |].
  eapply b9_keep_fsh; [exact G | exact KW1 | exact HFSH]. }
pose proof (b9_st_of_base B _ _ _ _ _ _ _ _ HB1) as HST1.
(* the string trim reads: the line cut at the '=' *)
assert (HKS : sa_str (rdW Wc (ms_mem ms)) (y_lp x) (firstn ei (b9_line x))).
{ apply (s2_prefix_str (rdW Wc memc) _ (y_lp x) (b9_line x) ei HSTR ltac:(lia)); [|exact HW0].
  intros a Ha Hne. apply KM; [|exact Hne]. unfold s2_span in Ha.
  pose proof (Z.mod_pos_bound (y_lp x + Z.of_nat (length (b9_line x))) 8 ltac:(lia)). lia. }
assert (HKI : pf_inb (pf_F (y_v x) (y_pos x) + PF_O_BUF) (y_lp x) (firstn ei (b9_line x)))
  by (unfold pf_inb, PF_O_BUF; rewrite HKlen; lia).
pose proof (b9_trim_site_ok B (y_v x) (y_pos x) lyc Sc Wc (ms_mem ms) mdv (ms_regs ms) (y_lp x)
  (firstn ei (b9_line x)) HST1 C10 HKS HKI) as HTC.
unfold b9_trim_call in HTC. destruct HTC as (ROD & C10' & Hp64 & TPRE & TEV).
destruct (b9_chain B _ _ _ _ _ _ _ _ _ HB1) as [ch1 HCH1].
rewrite (SIGP SS_trim ltac:(unfold seg_prog_syms; cbn [In]; repeat (first [left; reflexivity | right]))).
replace (seg_af SS_trim) with AF_trim by (vm_compute; reflexivity).
(* the call trim(line) at 0x88424, return 0x88428 = J2 *)
eapply SRr_bind.
{ eapply (cl_callS_wide B LAWS Wc (ms_regs ms) (ms_mem ms) _ STK_reac_segconf_parse_file (pf_sp0 (y_v x))
    (seg_spec.RC_PARSE_W (p_c (y_v x))) (p_ly (y_v x)) (p_S (y_v x)) (p_W (y_v x)) (p_mem (y_v x)) (p_md (y_v x))
    [(5, y_pos x)] lyc Sc mdv 0 STK_trim
    [(trim_end_addr (y_lp x) (firstn ei (b9_line x)), trim_end_addr (y_lp x) (firstn ei (b9_line x)) + 1)] EV_trim
    (pf_s1 (y_v x) - pf_sp0 (y_v x)) (Z_to_bv 64 (BASE + B9_J2)) ch1
    (fun ly' S' W' regs' mem' md' =>
       getr regs' 10 = w64 (y_lp x + Z.of_nat (seg_spec.trim_lead (firstn ei (b9_line x)))) /\
       sa_bytes (aview SEGS (w_H W') mem') (y_lp x)
         (seg_spec.zb (firstn (seg_spec.trim_lead (firstn ei (b9_line x)) +
                               length (SegModel.r_trim (firstn ei (b9_line x)))) (firstn ei (b9_line x))) ++
          [seg_spec.ZERO]) /\
       sa_kept SEGS Wc (ms_mem ms) W' mem' (ms_regs ms) STK_trim
         (fun a => a = trim_end_addr (y_lp x) (firstn ei (b9_line x))) /\
       sa_noalloc B lyc Sc ly' S') HJ).
  - exact Csp.
  - exact Ho16.
  - lia.
  - rewrite STR. lia.
  - rewrite STR, SPF. lia.
  - exact C3.
  - exact C4.
  - exact C1r.
  - apply ret_ok_codeptr_v; [unfold B9_J2, AF_reac_segconf_parse_file; lia | vm_compute; reflexivity].
  - unfold B9_J2, AF_reac_segconf_parse_file. rewrite unsigned_lit_small by lia. lia.
  - replace (pf_sp0 (y_v x) + (pf_s1 (y_v x) - pf_sp0 (y_v x))) with (pf_s1 (y_v x)) by lia.
    unfold s0Z. rewrite C8. unfold w64. rewrite unsigned_lit_small by lia. exact HCH1.
  - intros HPRE1. eapply SRr_mono.
    { exact (TRIM fx lyc Sc Wc (ms_regs ms) (ms_mem ms) mdv ch1 (y_lp x) (firstn ei (b9_line x)) HPRE1 ROD C10'
        Hp64 TPRE TEV). }
    cbv beta. intros W' c' _ (ly' & S' & regs' & mem' & md' & -> & HJ' & HP' & HK').
    exists ly', S', regs', mem', md'. split; [rewrite C1r; reflexivity|].
    split; [exact HJ'|]. split; [exact HP' | exact HK'].
  - intros a Ha. apply inFP_cons in Ha as [Ha | Ha]; [|exfalso; exact (inFP_nil a Ha)].
    try (cbn [fst snd] in Ha).
    right; right; right; left. exists 5, (y_pos x). split; [left; reflexivity|].
    left. unfold in_zr. cbn [fst snd]. rewrite Hly.
    change (frame_addr (p_ly (y_v x)) 5 (y_pos x)) with (pf_F (y_v x) (y_pos x)).
    change (fs_frame_bytes 5) with 2048. lia.
  - intros ly2 S2 W2 regs2 mem2 md2 _ a Ha Hw Hn.
    apply inFP_cons in Ha as [Ha | Ha]; [|exfalso; exact (inFP_nil a Ha)].
    try (cbn [fst snd] in Ha). exfalso. rewrite SPF in Hw. lia. }
(* back at 0x88428 = J2, at the same FP state *)
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJc2 & HP2 & (Ha02 & HBY2 & HKT2 & HNA2)).
destruct HNA2 as (HPm2 & Hly2 & HSf2). subst ly2.
replace (0 + EV_trim) with 0 in HJ2 by (unfold EV_trim; lia).
unfold sa_kept in HKT2. cbv beta in HKT2.
(* every byte off trim's window and its NUL is the call state's *)
assert (KT : forall a, 0 <= a < 2 ^ 64 -> ~ (pf_s1 (y_v x) - STK_trim <= a < pf_s1 (y_v x)) ->
    a <> trim_end_addr (y_lp x) (firstn ei (b9_line x)) -> rdW W2 mem2 a = rdW Wc (ms_mem ms) a).
{ intros a Ha Hw He. apply HKT2; [exact Ha | rewrite Csp; intros Hc; apply Hw; lia | exact He]. }
assert (HTEV : rdW W2 mem2 (trim_end_addr (y_lp x) (firstn ei (b9_line x))) <> None).
{ unfold trim_end_addr.
  rewrite (HBY2 (seg_spec.trim_lead (firstn ei (b9_line x)) + length (r_trim (firstn ei (b9_line x))))%nat);
    [discriminate|].
  unfold seg_spec.zb. rewrite length_app, length_map, length_firstn. cbn [length]. lia. }
assert (KV12 : forall a, rdW Wc (ms_mem ms) a <> None -> rdW W2 mem2 a <> None).
{ intros a0 Hv0. rewrite s2_aview_mod in Hv0 |- *.
  pose proof (Z.mod_pos_bound a0 (2 ^ 64) ltac:(lia)) as Ha.
  remember (a0 mod 2 ^ 64) as a eqn:Ea. clear Ea. rename Hv0 into Hv.
  destruct (Z.eq_dec a (trim_end_addr (y_lp x) (firstn ei (b9_line x)))) as [He | He]; [rewrite He; exact HTEV|].
  destruct (Z_lt_le_dec a (pf_s1 (y_v x) - STK_trim)) as [Hlo | Hlo];
    [|destruct (Z_lt_le_dec a (pf_s1 (y_v x))) as [Hhi | Hhi]].
  - rewrite KT; [exact Hv | exact Ha | lia | exact He].
  - pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
    apply (aview_some_of_apresent SEGS). apply Hpres2. rewrite SPF. rewrite STR in Hlo. lia.
  - rewrite KT; [exact Hv | exact Ha | lia | exact He]. }
assert (KV2 : forall a, rdW Wc memc a <> None -> rdW W2 mem2 a <> None) by (intros a Hv; exact (KV12 a (KV a Hv))).
assert (KW2 : forall a, 0 <= a < 2 ^ 64 -> ~ b9_Wrx (y_v x) (y_pos x) true a -> rdW W2 mem2 a = rdW Wc memc a).
{ intros a Ha Hw. rewrite KT; [exact (KW1 a Ha Hw) | exact Ha | |].
  - intros Hc. apply Hw. left. rewrite SPF. rewrite STR in Hc. lia.
  - intros ->. apply Hw. right; right. unfold PF_O_BUF. lia. }
assert (HFI2 : pf_rg regs2 (b9_FI B (y_v x))) by exact (b9_rg_pres _ _ _ HP2 (b9_FI_cs B _) HFI1).
assert (HB2 : pf_base B (y_v x) (y_pos x) lyc S2 W2 regs2 mem2 md2 PF_SC_LINE).
{ eapply (b9_move0 B (y_v x) (y_pos x) lyc Sc Wc rX memc mdc PF_SC_LINE S2 W2 regs2 mem2 md2 PF_SC_LINE HB HJ2
    HSf2 HPm2 KW2 KV2 HFI2).
  eapply b9_keep_fsh; [exact G | exact KW2 | exact HFSH]. }
assert (HC5 : sa_heap B lyc Sc (p_c (y_v x)) seg_spec.SEG_C_SIZE)
  by (destruct HOBJ as (_ & _ & _ & _ & H5 & _); exact H5).
assert (HST2 : pf_st (y_v x) (y_pos x) (rdW W2 mem2) (y_cf x) (y_cur x) (y_nm x) (b9_k x))
  by (eapply b9_keep_st; eassumption).
(* the key at kp = lp + trim_lead K, and the rest of the line above the '=' *)
assert (HKEY : sa_str (rdW W2 mem2) (y_lp x + Z.of_nat (seg_spec.trim_lead (firstn ei (b9_line x)))) (b9_key x ei))
  by (unfold b9_key; exact (s2_key_str Wc W2 (ms_mem ms) mem2 (y_lp x) (firstn ei (b9_line x)) HKS HBY2 KV12)).
assert (HREST : sa_str (rdW W2 mem2) (y_lp x + Z.of_nat ei + 1) (skipn (S ei) (b9_line x))).
{ replace (y_lp x + Z.of_nat ei + 1) with (y_lp x + Z.of_nat (S ei)) by lia.
  apply (s2_suffix_str (rdW Wc memc) _ (y_lp x) (b9_line x) (S ei) HSTR ltac:(lia)).
  intros a Ha. unfold s2_span in Ha.
  pose proof (Z.mod_pos_bound (y_lp x + Z.of_nat (length (b9_line x))) 8 ltac:(lia)).
  rewrite KT; [| lia | rewrite STR; lia | lia]. apply KM; lia. }
(* the registers at J2: B9_R and s8 = eq kept by trim, a0 = kp *)
assert (RG2 : pf_rg regs2 (B9_R x ++ [(24, y_lp x + Z.of_nat ei)])).
{ apply (b9_rg_pres (ms_regs ms) regs2 _ HP2).
  - unfold B9_R, PF_RL, PF_RM. cbn [app]. repeat apply Forall_cons; try apply Forall_nil; cbn [fst];
      unfold acallee_saved; lia.
  - apply b9_rg_app. split; [exact RGR1|]. apply Forall_cons; [|apply Forall_nil]. exact C24. }
change (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + B9_J2)) mem2 (seg_rom SEGS)) md2)
  with (cfg_at SEGS (BASE + B9_J2) regs2 mem2 md2).
apply (FJ2 x ei (y_lp x + Z.of_nat (seg_spec.trim_lead (firstn ei (b9_line x)))) lyc S2 W2 regs2 mem2 md2).
unfold INV_J2, b9_core, b9_inbuf.
split.
{ split; [exact HB2|]. split; [exact HMID|]. split; [exact HST2|]. split; [exact HLEN|].
  split; [exact HD0 | exact HDL]. }
split; [exact HCH|].
split.
{ split; [exact HKEY|]. unfold b9_buf, pf_inb, PF_O_BUF, b9_key. lia. }
split; [unfold b9_key; lia|].
split.
{ split; [exact HREST|]. unfold b9_buf, pf_inb, PF_O_BUF. rewrite length_skipn. lia. }
replace (B9_R x ++ [(24, y_lp x + Z.of_nat ei); (10, y_lp x + Z.of_nat (seg_spec.trim_lead (firstn ei (b9_line x))))])
  with ((B9_R x ++ [(24, y_lp x + Z.of_nat ei)]) ++
        [(10, y_lp x + Z.of_nat (seg_spec.trim_lead (firstn ei (b9_line x))))])
  by (rewrite <- app_assoc; reflexivity).
apply b9_rg_app. split; [exact RG2|].
apply Forall_cons; [|apply Forall_nil]. cbn [fst snd].
apply (s2_bvr' _ 10%bv 10); [reflexivity | exact Ha02].
Qed.

(** ** Stretch SB9_2: from REF3 and J2, the walk reaches B9's goal from J1 *)
Lemma b9_s2 : SB9_2 B.
Proof.
unfold SB9_2, from_J1, b9_from.
intros n HR3 FJ2 x r lyc Sc Wc rX memc mdc HI.
destruct r as [ei|].
- exact (s2_found n x ei lyc Sc Wc rX memc mdc HI FJ2).
- exact (s2_none n x lyc Sc Wc rX memc mdc HI HR3).
Qed.
End x.
End d.

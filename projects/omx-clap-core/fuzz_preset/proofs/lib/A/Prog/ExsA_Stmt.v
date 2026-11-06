(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset, image A' (#102 pin asan 1be0f53d96cb, facts 8f3e7e1a07f1), ex_string
   (fuzz_preset.c :185-239, A_prog_sigma AS_ex_string = 0x84034, 318 instructions to 0x8452c): the STATEMENTS of its walk
   against the kit's tex_string_specX (lib/A/PRH_FnEx.v), instantiated at image A'. This file proves nothing about the program.
   PORTED from lib/B/Prog/ExsB_Stmt.v (a Theorem Labs lane's B' walk): es_e, ES_PRE, ES_Q, ES_POST, ES_RES and ESG are the donor's
   texts at image A's segments; ESB, ESK and the cut statements are RE-DERIVED from the A' listing, whose register
   allocation differs from B' (A' keeps o in s3, p in s4, the next p in s5, in->end CACHED in s6 from the entry on, the
   shadow base in s7, q + 8's shadow address in s8, the high surrogate in s1, and SPILLS q's shadow address at 8(sp)):
   - es_e, the entry record; ES_PRE (tex_string_specX's premises at the record), ES_Q / ES_POST (its post);
   - ESB, the base invariant at every cut after the prologue, and ESG, the grammar invariant of the loop;
   - the CUTS of the walk, by offset from the entry (DERIVED: A' address minus 0x84034):
       LH    0x0dc (0x84110)  loop head: one input byte per pass (plain byte, simple escape, `\u`)
       ESC   0x104 (0x84138)  a backslash at p with p + 1 before the end: the escape byte's dispatch
       HEX1  0x138 (0x8416c)  `\u`: four digits remain, ex_hex4 into 36(sp)
       HEX1R 0x150 (0x84184)  ex_hex4 returned: the cp tests, then UTF8 or HEX2
       HEX2  0x174 (0x841a8)  high surrogate (in s1): `\u` + four digits, ex_hex4 into 32(sp)
       HEX2R 0x1c4 (0x841f8)  the second ex_hex4 returned: the pair into 36(sp), then UTF8
       UTF8  0x1f4 (0x84228)  the code point at 36(sp) through ex_utf8
       UTF8R 0x200 (0x84234)  ex_utf8 returned: o += n, the ESK constants again, then CONT
       CONT  0x344 (0x84378)  after a byte is stored: q + 8's shadow, s6 = in->end reloaded, p := s5, s5 >= end exits,
                              else back to LH
       FAIL  0x3f8 (0x8442c)  return -1 (li a0,-1, epilogue)
       QUOTE 0x400 (0x84434)  the closing quote: NUL stored, in->p = p + 1, epilogue, return 0
   Numerals: register numbers (WORD); 144 (LENGTH: frame), 160 (DERIVED: STK_ex_string at prh_img_A), slot offsets
   0, 8, 16, 24, 32, 36, 40 .. 136 (LENGTH, A's code); 0xd800, 0xdc00, 0xfffffffffca02400 (WORD: the constants A'
   0x840ec-0x8410c spills); cut offsets (DERIVED). No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0s YK0o YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YCbqG YP0b YPsym YC4aP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnEx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Img Img0 Listing_prog PAImg_prog.
Import ListNotations.
Local Open Scope Z_scope.

#[local] Existing Instance prh_img_A.

(* the callee-saved registers ex_string saves (A 0x84038-0x84068), offset from the frame base (entry sp - 144) *)
Definition es_saved : list (Z * Z) :=
  [(136, 1); (128, 8); (120, 9); (112, 18); (104, 19); (96, 20); (88, 21); (80, 22); (72, 23); (64, 24);
   (56, 25); (48, 26); (40, 27)].
(* the 64-bit constant A 0x84104 / 0x84108 spills at 0(sp): 0x10000 - 0xd800 * 0x400 - 0xdc00, two's complement *)
Definition ES_C8 : Z := 2 ^ 64 - 0x35fdc00.

(* ---- the entry record: every quantified name of tex_string_specX ---- *)
Record es_e : Type := MkEs {
  e_ly : alayout; e_S : astate; e_Hp : list Z; e_W : world rsegs;
  e_regs : bvmap 5 word; e_mem : word -> option byte; e_md : Model; e_ch : list (Z * Z * Z);
  e_q : Z; e_x0 : Z; e_i0 : Z; e_scr : Z; e_d : Z; e_x : list Z;
  e_Lam : list (Z * Z); e_peak : Z; e_cnt : Z; e_fail : Z; e_ran : Z; e_most : Z; e_own : Z }.

Definition es_len (E : es_e) : Z := Z.of_nat (length (e_x E)).
Definition es_xs (E : es_e) : list Z := skipn (Nat.succ (Z.to_nat (e_i0 E))) (e_x E).
Definition es_FP (E : es_e) : list (Z * Z) :=
  [(e_scr E, e_scr E + es_len E + 1); (e_q E, e_q E + 8)].
Definition es_sp (E : es_e) : Z := spZ (e_regs E).
Definition es_SP (E : es_e) : Z := es_sp E - 144.
Definition es_pc (off : Z) : Z := A_prog_sigma AS_ex_string + off.
(* the input byte at position a (0 past the text) *)
Definition es_byte (E : es_e) (a : Z) : Z := nth (Z.to_nat (a - e_x0 E)) (e_x E) 0.
(* the text from position a on *)
Definition es_rest (E : es_e) (a : Z) : list Z := skipn (Z.to_nat (a - e_x0 E)) (e_x E).

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {cp : CfParams} {RL : PrhRoomLive}.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world rsegs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* tex_string_specX's premises at the record (PRH_FnEx.v:258-266, in order) *)
Definition ES_PRE (E : es_e) : Prop :=
  let len := es_len E in
  let ly := e_ly E in let S := e_S E in let Hp := e_Hp E in let W := e_W E in let regs := e_regs E in
  let mem := e_mem E in let md := e_md E in
  let q := e_q E in let x0 := e_x0 E in let i0 := e_i0 E in let scr := e_scr E in let d := e_d E in
  fpre B ARx STK_ex_string ly S Hp W regs mem md (e_ch E) /\
  getr regs 10 = w64 q /\
  val_mem rsegs (rdW W mem) q 8 (x0 + i0) /\ val_mem rsegs (rdW W mem) (q + 8) 8 (x0 + len) /\
  val_mem rsegs (rdW W mem) (q + 24) 8 scr /\ q mod 8 = 0 /\
  spZ regs <= q /\ q + 32 <= spZ regs + d /\ fwin ly W regs mem d /\
  src_rd W mem x0 (e_x E) /\ prhex_inblk B ly S Hp x0 len /\ len <= 3 * 2 ^ 20 /\ 0 <= i0 < len /\
  wdest_ok B STK_ex_string ly S W regs mem scr (len + 1) /\ prhex_inblk B ly S Hp scr (len + 1) /\
  (scr + len + 1 <= x0 \/ x0 + len <= scr) /\ (scr + len + 1 <= q \/ q + 40 <= scr) /\
  prh_ledger B ly S Hp W mem (e_Lam E) (e_peak E) (e_cnt E) (e_fail E) (e_ran E) (e_most E) (e_own E).

(* tex_string_specX's post (PRH_FnEx.v:267-278): fpostWm over its Q, verbatim at the record *)
Definition ES_Q (E : es_e) : alayout -> astate -> list Z -> world rsegs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
  fun ly' S' Hp' W' regs' mem' md' =>
    (room_live_cf (e_S E) -> room_live_cf S') /\ Hp' = e_Hp E /\ S' = e_S E /\
    ablocks B ly' S' = ablocks B (e_ly E) (e_S E) /\
    prh_ledger B ly' S' Hp' W' mem' (e_Lam E) (e_peak E) (e_cnt E) (e_fail E) (e_ran E) (e_most E) (e_own E) /\
    match fst (fst (PjGrammar.jr_string (es_xs E) [])) with
    | None => getr regs' 10 = w64 (-1) /\ prhex_same (e_W E) (e_mem E) W' mem' (e_q E) 8
    | Some (s, rest) => getr regs' 10 = w64 0 /\
        (exists c, PjGrammar.scan (es_xs E) = Some c /\ rest = skipn (Nat.succ c) (es_xs E) /\
           val_mem rsegs (rdW W' mem') (e_q E) 8 (e_x0 E + e_i0 E + Z.of_nat c + 2)) /\
        bytes_at W' mem' (e_scr E) (s ++ [0])
    end.
Definition ES_POST (E : es_e) : world rsegs -> config -> Prop :=
  fpostWm B ARx SK STK_ex_string (e_d E) (es_FP E) (e_regs E) (e_ly E) (e_S E) (e_Hp E) (e_W E) (e_mem E) (e_md E)
    (ES_Q E).

(* the functional part of the post at a state (W', mem') with result r (what the exit cuts carry) *)
Definition ES_RES (E : es_e) (W' : world rsegs) (mem' : word -> option byte) (r : Z) : Prop :=
  match fst (fst (PjGrammar.jr_string (es_xs E) [])) with
  | None => r = -1 /\ prhex_same (e_W E) (e_mem E) W' mem' (e_q E) 8
  | Some (s, rest) => r = 0 /\
      (exists c, PjGrammar.scan (es_xs E) = Some c /\ rest = skipn (Nat.succ c) (es_xs E) /\
         val_mem rsegs (rdW W' mem') (e_q E) 8 (e_x0 E + e_i0 E + Z.of_nat c + 2)) /\
      bytes_at W' mem' (e_scr E) (s ++ [0])
  end.

(* ---- the base invariant at every cut after the prologue (current state lyc Sc Hpc memc mdc k, registers regs) ---- *)
Definition ESB (E : es_e) (lyc : alayout) (Sc : astate) (Hpc : list Z) (regs : bvmap 5 word)
  (memc : word -> option byte) (mdc : Model) (k : Z) : Prop :=
  let W := e_W E in let q := e_q E in let SP := es_SP E in
  (* the journal from the entry, at the caller-window width *)
  ajournal_x (SK := SK) rsegs B prh_pst ARx (STK_ex_string + e_d E) (es_sp E + e_d E) (es_FP E)
    (e_ly E) (e_S E) (e_Hp E) W (e_mem E) (e_md E) [] lyc Sc Hpc W memc mdc k /\
  (* the caller's window outside FP unchanged, and in->p unchanged so far *)
  (forall a, es_sp E <= a < es_sp E + e_d E -> ~ inFP (es_FP E) a ->
     aview rsegs (w_H W) memc a = aview rsegs (w_H W) (e_mem E) a) /\
  (forall a, q <= a < q + 8 -> aview rsegs (w_H W) memc a = aview rsegs (w_H W) (e_mem E) a) /\
  Hpc = e_Hp E /\ ablocks B lyc Sc = ablocks B (e_ly E) (e_S E) /\ (room_live_cf (e_S E) -> room_live_cf Sc) /\
  prh_ledger B lyc Sc Hpc W memc (e_Lam E) (e_peak E) (e_cnt E) (e_fail E) (e_ran E) (e_most E) (e_own E) /\
  (* the frame: the saved registers, the spilled constants and q's spilled shadow address (A 0x840b4) *)
  (forall o r, In (o, r) es_saved ->
     val_mem rsegs (rdW W memc) (SP + o) 8 (bv_unsigned (getr (e_regs E) (Z_to_bv 5 r)))) /\
  val_mem rsegs (rdW W memc) SP 8 ES_C8 /\ val_mem rsegs (rdW W memc) (SP + 8) 8 (SHADOW_OFF + q / 8) /\
  val_mem rsegs (rdW W memc) (SP + 16) 8 0xd800 /\ val_mem rsegs (rdW W memc) (SP + 24) 8 0xdc00 /\
  (* the registers every cut has *)
  getr regs 2 = w64 SP /\ getr regs 8 = w64 q /\ getr regs 18 = w64 (q + 8) /\
  getr regs 22 = w64 (e_x0 E + es_len E) /\ getr regs 23 = w64 SHADOW_OFF /\
  getr regs 24 = w64 (SHADOW_OFF + (q + 8) / 8) /\
  getr regs 25 = w64 34 /\ getr regs 26 = w64 32 /\ getr regs 27 = w64 92 /\
  getr regs 3 = getr (e_regs E) 3 /\ getr regs 4 = getr (e_regs E) 4 /\
  (* no allocator call: the allocator state is the entry's; the memory stays normal if it was (fQmn's keep) *)
  Sc = e_S E /\ (YAkMemnorm.memnorm rsegs (e_mem E) -> YAkMemnorm.memnorm rsegs memc).

(* the caller-saved constants the loop keeps in a3 .. a6 (A 0x840dc-0x840e8, re-set at A 0x84238-0x84244) *)
Definition ESK (regs : bvmap 5 word) : Prop :=
  getr regs 13 = w64 101 /\ getr regs 14 = w64 91 /\ getr regs 15 = w64 113 /\ getr regs 16 = w64 114.

(* ---- the grammar invariant of the loop: p the next byte, acc the bytes the grammar has emitted so far (the cuts
   say separately which of them are stored at the scratch) ---- *)
Definition ESG (E : es_e) (p : Z) (acc : list Z) : Prop :=
  e_x0 E + e_i0 E + 1 <= p <= e_x0 E + es_len E /\
  Z.of_nat (length acc) <= p - (e_x0 E + e_i0 E + 1) /\
  PjGrammar.decode (es_xs E) = PjGrammar.emit acc (PjGrammar.decode (es_rest E p)).

(* ---- the cut statements; LH_AT E p is the loop head at p, every other cut takes it at its p' ---- *)
Definition LH_AT (E : es_e) (p : Z) : Prop :=
  forall lyc Sc Hpc regs memc mdc k acc,
  ES_PRE E -> ESB E lyc Sc Hpc regs memc mdc k -> ESK regs -> ESG E p acc -> p < e_x0 E + es_len E ->
  garr8 rsegs (rdW (e_W E) memc) (e_scr E) acc ->
  getr regs 19 = w64 (e_scr E + Z.of_nat (length acc)) -> getr regs 20 = w64 p ->
  SRr rsegs (e_W E) (cfg_at rsegs (es_pc 0xdc) regs memc mdc) (ES_POST E).

(* A 0x84378: s3 = the new output position, s5 = the new p *)
Definition CUT_CONT (E : es_e) (p : Z) : Prop :=
  forall lyc Sc Hpc regs memc mdc k acc,
  ES_PRE E -> ESB E lyc Sc Hpc regs memc mdc k -> ESK regs -> ESG E p acc ->
  garr8 rsegs (rdW (e_W E) memc) (e_scr E) acc ->
  getr regs 19 = w64 (e_scr E + Z.of_nat (length acc)) -> getr regs 21 = w64 p ->
  SRr rsegs (e_W E) (cfg_at rsegs (es_pc 0x344) regs memc mdc) (ES_POST E).

(* A 0x84228: the code point cp at 36(sp), s3 = the output position, s5 = the next p; acc ++ utf8 cp is what the
   grammar emits for the escape *)
Definition CUT_UTF8 (E : es_e) (p : Z) : Prop :=
  forall lyc Sc Hpc regs memc mdc k acc cp,
  ES_PRE E -> ESB E lyc Sc Hpc regs memc mdc k -> ESG E p (acc ++ PjGrammar.utf8 cp) ->
  0 < cp < 2 ^ 21 ->
  garr8 rsegs (rdW (e_W E) memc) (e_scr E) acc ->
  val_mem rsegs (rdW (e_W E) memc) (es_SP E + 36) 4 cp ->
  getr regs 19 = w64 (e_scr E + Z.of_nat (length acc)) -> getr regs 21 = w64 p ->
  SRr rsegs (e_W E) (cfg_at rsegs (es_pc 0x1f4) regs memc mdc) (ES_POST E).

(* A 0x84138: a backslash at p with p + 1 before the end (s4 = p, s5 = p + 1) *)
Definition CUT_ESC (E : es_e) (p : Z) : Prop :=
  forall lyc Sc Hpc regs memc mdc k acc,
  ES_PRE E -> ESB E lyc Sc Hpc regs memc mdc k -> ESK regs -> ESG E p acc ->
  garr8 rsegs (rdW (e_W E) memc) (e_scr E) acc ->
  p + 1 < e_x0 E + es_len E -> es_byte E p = 92 ->
  getr regs 19 = w64 (e_scr E + Z.of_nat (length acc)) -> getr regs 20 = w64 p -> getr regs 21 = w64 (p + 1) ->
  SRr rsegs (e_W E) (cfg_at rsegs (es_pc 0x104) regs memc mdc) (ES_POST E).

(* A 0x8416c: `\u` at p (s4 = p, s5 = p + 2) *)
Definition CUT_HEX1 (E : es_e) (p : Z) : Prop :=
  forall lyc Sc Hpc regs memc mdc k acc,
  ES_PRE E -> ESB E lyc Sc Hpc regs memc mdc k -> ESG E p acc ->
  garr8 rsegs (rdW (e_W E) memc) (e_scr E) acc ->
  p + 1 < e_x0 E + es_len E -> es_byte E p = 92 -> es_byte E (p + 1) = 117 ->
  getr regs 19 = w64 (e_scr E + Z.of_nat (length acc)) -> getr regs 20 = w64 p -> getr regs 21 = w64 (p + 2) ->
  SRr rsegs (e_W E) (cfg_at rsegs (es_pc 0x138) regs memc mdc) (ES_POST E).

(* A 0x84184: ex_hex4 returned for the four bytes after `\u` at p: a0 its result, 36(sp) its value *)
Definition CUT_HEX1R (E : es_e) (p : Z) : Prop :=
  forall lyc Sc Hpc regs memc mdc k acc,
  ES_PRE E -> ESB E lyc Sc Hpc regs memc mdc k -> ESG E p acc ->
  garr8 rsegs (rdW (e_W E) memc) (e_scr E) acc ->
  p + 6 <= e_x0 E + es_len E -> es_byte E p = 92 -> es_byte E (p + 1) = 117 ->
  match PjGrammar.hex4 (es_rest E (p + 2)) with
  | Some h => getr regs 10 = w64 0 /\ val_mem rsegs (rdW (e_W E) memc) (es_SP E + 36) 4 h
  | None => getr regs 10 = w64 (-1)
  end ->
  getr regs 19 = w64 (e_scr E + Z.of_nat (length acc)) -> getr regs 20 = w64 p -> getr regs 21 = w64 (p + 2) ->
  SRr rsegs (e_W E) (cfg_at rsegs (es_pc 0x150) regs memc mdc) (ES_POST E).

(* A 0x841a8: a high surrogate hi in s1 from the four digits after `\u` at p (s4 = p, s5 = p + 6) *)
Definition CUT_HEX2 (E : es_e) (p : Z) : Prop :=
  forall lyc Sc Hpc regs memc mdc k acc hi,
  ES_PRE E -> ESB E lyc Sc Hpc regs memc mdc k -> ESG E p acc ->
  garr8 rsegs (rdW (e_W E) memc) (e_scr E) acc ->
  p + 6 <= e_x0 E + es_len E -> es_byte E p = 92 -> es_byte E (p + 1) = 117 ->
  PjGrammar.hex4 (es_rest E (p + 2)) = Some hi -> 55296 <= hi < 56320 ->
  getr regs 9 = w64 hi ->
  getr regs 19 = w64 (e_scr E + Z.of_nat (length acc)) -> getr regs 20 = w64 p -> getr regs 21 = w64 (p + 6) ->
  SRr rsegs (e_W E) (cfg_at rsegs (es_pc 0x174) regs memc mdc) (ES_POST E).

(* A 0x841f8: ex_hex4 returned for the four bytes after the second `\u` (at p + 6): a0 its result, 32(sp) its value *)
Definition CUT_HEX2R (E : es_e) (p : Z) : Prop :=
  forall lyc Sc Hpc regs memc mdc k acc hi,
  ES_PRE E -> ESB E lyc Sc Hpc regs memc mdc k -> ESG E p acc ->
  garr8 rsegs (rdW (e_W E) memc) (e_scr E) acc ->
  p + 12 <= e_x0 E + es_len E -> es_byte E p = 92 -> es_byte E (p + 1) = 117 ->
  PjGrammar.hex4 (es_rest E (p + 2)) = Some hi -> 55296 <= hi < 56320 ->
  getr regs 9 = w64 hi ->
  es_byte E (p + 6) = 92 -> es_byte E (p + 7) = 117 ->
  match PjGrammar.hex4 (es_rest E (p + 8)) with
  | Some lo => getr regs 10 = w64 0 /\ val_mem rsegs (rdW (e_W E) memc) (es_SP E + 32) 4 lo
  | None => getr regs 10 = w64 (-1)
  end ->
  getr regs 19 = w64 (e_scr E + Z.of_nat (length acc)) -> getr regs 20 = w64 p -> getr regs 21 = w64 (p + 6) ->
  SRr rsegs (e_W E) (cfg_at rsegs (es_pc 0x1c4) regs memc mdc) (ES_POST E).

(* A 0x84234: ex_utf8 returned the byte count n of the code point it wrote at o = s3 *)
Definition CUT_UTF8R (E : es_e) (p : Z) : Prop :=
  forall lyc Sc Hpc regs memc mdc k acc cp,
  ES_PRE E -> ESB E lyc Sc Hpc regs memc mdc k -> ESG E p (acc ++ PjGrammar.utf8 cp) ->
  garr8 rsegs (rdW (e_W E) memc) (e_scr E) (acc ++ PjGrammar.utf8 cp) ->
  getr regs 10 = w64 (Z.of_nat (length (PjGrammar.utf8 cp))) ->
  getr regs 19 = w64 (e_scr E + Z.of_nat (length acc)) -> getr regs 21 = w64 p ->
  SRr rsegs (e_W E) (cfg_at rsegs (es_pc 0x200) regs memc mdc) (ES_POST E).

(* the exits: A 0x8442c (return -1) and A 0x84434 (the closing quote at p) *)
Definition CUT_FAIL (E : es_e) : Prop :=
  forall lyc Sc Hpc regs memc mdc k,
  ES_PRE E -> ESB E lyc Sc Hpc regs memc mdc k ->
  PjGrammar.decode (es_xs E) = None ->
  SRr rsegs (e_W E) (cfg_at rsegs (es_pc 0x3f8) regs memc mdc) (ES_POST E).
Definition CUT_QUOTE (E : es_e) : Prop :=
  forall lyc Sc Hpc regs memc mdc k p acc,
  ES_PRE E -> ESB E lyc Sc Hpc regs memc mdc k -> ESG E p acc ->
  garr8 rsegs (rdW (e_W E) memc) (e_scr E) acc ->
  p < e_x0 E + es_len E -> es_byte E p = 34 ->
  getr regs 19 = w64 (e_scr E + Z.of_nat (length acc)) -> getr regs 20 = w64 p ->
  SRr rsegs (e_W E) (cfg_at rsegs (es_pc 0x400) regs memc mdc) (ES_POST E).
End c.

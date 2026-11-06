(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the contracts of the string entries that plugin-hostd/fuzz_command calls and cgif_file_fuzzer does not (strlen, strcmp, strncmp, strspn, strcspn, strcat and musl's strtok_r), in the form cgif_file_fuzzer's lib/YG0d.v states its memcmp, bcmp, memchr and strnlen contracts; the value each one returns is the one fuzz_command's own plain proof states for the same entry. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Rt/RtString.v, with its module paths, module names and numbers changed; 93 of its 155 lines of code are new or changed and 119 lines of the source are left out. *)
(* The NEW interceptor contracts of reac-pw/fuzz_segconf's ASan+UBSan image B (fuzz_segconf.asan-ubsan): the image-B
   twin of lib/A/Rt/RtSeg.v (commit 80d098bd1905, sha256 ce2e38d10fc0, rows 3 and 6-12 of
   proofs/reac-pw/fuzz_segconf/provenance/evidence/interceptors/INTERFACE-A-interceptors.md (commit 7068323e2626)), in the form
   fuzz_command states its string and number entries (lib/A/Rt/RtString.v, lib/A/Rt/RtNumber.v at
   origin/ossv/recipes 501c0d516c69): the premises are RtDefs.v's parts (ecall_pre_stk, aread_ok, awrite_ok,
   astr_at, atail_vis, rt_rom_view, aguard_ok) and the conclusion is RtDefs.v's art_post. Statements only; no walk,
   no proof.

   Every image number is a parameter of its Definition (pc, and gotw / guard for strtol and strstr), so the text is
   image-independent: every Definition below is the A file's, word for word; only the module paths (lib.B.Rt) and the
   addresses in the comments differ. The addresses named in the comments are image B's, each the A address's twin
   by symbol + offset in the image-B twin's .symtab (fuzz_segconf.asan-ubsan.debug sha256 80e82127e8ca; the stack-
   protector GOT word 0xa3e98 read from B's .got and from the auipc / ld pair at 0x9b9e0 / 0x9b9e4); they are
   information for the reader, not part of any statement.

   The answers carry fuzz_manifest's posts (lib/A/FMH_Rt.v:115, :133, :160, :170). A string is a byte list here,
   as in RtString.v, and the answer is stated over its byte values [ZS s]. The pure models below are FMH_Rt.v:20-32
   with the same names and the same bodies, so a bridge from fuzz_manifest's form reads each post unchanged; a file
   that imports both modules names them qualified. [last_at] (strrchr) and [alnum_b] (isalnum) are new: [alnum_b]
   has the body of segconf's plain lib/Prog/isalnum_c.v:9-10 (= fuzz_manifest's ManifestModel.is_alnum and
   A/Prog/isalnum_c.v alnum_b). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require RtString.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require __intscan_c.
Import ListNotations.
Open Scope Z_scope.

Module PIS := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog.__intscan_c.

(* ---- pure models of the answers ---- *)
(* the first index of c in l (FMH_Rt.v:21-22) *)
Definition first_at (l : list Z) (c : Z) (j : nat) : Prop :=
  (j < length l)%nat /\ nth j l 0 = c /\ ~ In c (firstn j l).
(* the last index of c in l: c is at j and nowhere after it *)
Definition last_at (l : list Z) (c : Z) (j : nat) : Prop :=
  (j < length l)%nat /\ nth j l 0 = c /\ ~ In c (skipn (S j) l).
(* sanitizer_common's ToLower (ASCII) (FMH_Rt.v:26) *)
Definition lc (c : Z) : Z := if (65 <=? c) && (c <=? 90) then c + 32 else c.
(* strncasecmp (s1, s2, k) = 0: the first k bytes of each string with its NUL agree under lc (FMH_Rt.v:27-28) *)
Definition strncase_eq (k : nat) (l1 l2 : list Z) : Prop :=
  map lc (firstn k (l1 ++ [0])) = map lc (firstn k (l2 ++ [0])).
(* w occurs in t at j (FMH_Rt.v:30-32) *)
Definition occ_at (t w : list Z) (j : nat) : Prop := (j + length w <= length t)%nat /\ firstn (length w) (skipn j t) = w.
Definition first_occ (t w : list Z) (j : nat) : Prop := occ_at t w j /\ forall j', (j' < j)%nat -> ~ occ_at t w j'.
Definition no_occ (t w : list Z) : Prop := forall j, ~ occ_at t w j.
(* musl isalnum's class on a byte value: a digit, an upper-case or a lower-case ASCII letter *)
Definition alnum_b (c : Z) : bool :=
  ((48 <=? c) && (c <=? 57)) || ((65 <=? c) && (c <=? 90)) || ((97 <=? c) && (c <=? 122)).

(* the byte values of a byte list *)
#[local] Abbreviation ZS s := (map (fun b : byte => bv_unsigned b) s).

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section c.
Variable segs : list Segment.
Variable B : asyms.

Local Notation PRE stk := (ecall_pre_stk segs B stk).
Local Notation RD stk := (aread_ok segs stk).
Local Notation WR stk := (awrite_ok segs B stk).
Local Notation STR := (astr_at segs).
Local Notation POST stk := (art_post segs B stk).

(* Row 6. strchr(x, c), 0 < c < 256. Image B: trampoline 0x43ab4 -> wrapper 0x45b70 (736 B) -> musl strchr 0x9b180.
   Template: the premises of RtString.v:121 astrncmp_realizes for one string, with the read over the whole string
   and its NUL (the wrapper checks (r ? r - x : strlen x) + 1 bytes, at most len + 1); the post of FMH_Rt.v:115.
   The window is 2 * ESTACK, fuzz_manifest's STK_RT_STR for the same wrapper (FMH_Base.v:91). musl's strchr reads
   the string a word at a time, so the bytes after the NUL up to the word's end are asked visible (atail_vis). *)
Definition astrchr_realizes (pc : Z) : Prop :=
forall ly S W regs mem md x c s,
PRE (2 * ESTACK) ly S W regs mem md ->
getr regs 10 = w64 x -> getr regs 11 = w64 c -> 0 < c < 256 -> 0 < x ->
STR W mem x s ->
RD (2 * ESTACK) W regs mem x (astr_len s + 1) ->
(* 8 bytes of band room past the string: the kit's chk_ok needs region_in_mem p 8 (lib/A/Bz/A/I_consts.v:20-21) *)
amem_range x (astr_len s + 8) ->
atail_vis segs W mem (x + astr_len s) ->
rt_rom_view segs B W mem ->
SRr segs W (cfg_at segs pc regs mem md)
(POST (2 * ESTACK) ly S W regs mem md (fun _ => False)
(fun regs' _ =>
(getr regs' 10 = w64 0 /\ ~ In c (ZS s)) \/
(exists j, first_at (ZS s) c j /\ getr regs' 10 = w64 (x + Z.of_nat j)))).

(* Row 7. strncasecmp(x, y, n). Image B: trampoline 0x43aac -> wrapper 0x45088 (1464 B), which compares the bytes
   itself and checks min (i + 1, n) bytes of each string (i the index where the comparison stopped; with the
   strict-string flag set, min (len + 1, n)). Template: RtString.v:121 astrncmp_realizes, premise for premise; the
   post of FMH_Rt.v:133. *)
Definition astrncasecmp_realizes (pc : Z) : Prop :=
forall ly S W regs mem md x y n sx sy,
PRE (2 * ESTACK) ly S W regs mem md ->
getr regs 10 = w64 x -> getr regs 11 = w64 y -> getr regs 12 = w64 n -> 0 <= n < 2 ^ 32 -> 0 < x -> 0 < y ->
STR W mem x sx -> STR W mem y sy ->
RD (2 * ESTACK) W regs mem x (Z.min n (astr_len sx + 1)) ->
(* 8 bytes of band room past the string: the kit's chk_ok needs region_in_mem p 8 (lib/A/Bz/A/I_consts.v:20-21) *)
amem_range x (astr_len sx + 8) ->
RD (2 * ESTACK) W regs mem y (Z.min n (astr_len sy + 1)) ->
(* 8 bytes of band room past the string: the kit's chk_ok needs region_in_mem p 8 (lib/A/Bz/A/I_consts.v:20-21) *)
amem_range y (astr_len sy + 8) ->
atail_vis segs W mem (x + astr_len sx) -> atail_vis segs W mem (y + astr_len sy) ->
rt_rom_view segs B W mem ->
SRr segs W (cfg_at segs pc regs mem md)
(POST (2 * ESTACK) ly S W regs mem md (fun _ => False)
(fun regs' _ => getr regs' 10 = w64 0 <-> strncase_eq (Z.to_nat n) (ZS sx) (ZS sy))).

(* Row 8. strstr(x, y). Image B: trampoline 0x43ab0 -> wrapper 0x45644 (220 B) -> musl strstr 0x9b7ac (which calls
   the strchr wrapper, and for a needle of 5 bytes or more twoway_strstr 0x9b99c, which calls the memcmp and memchr
   wrappers), then StrstrCheck: it checks (r ? r - x + len y : len x + 1) bytes of the haystack and len y + 1 of the
   needle. Template: RtString.v:121's premise shape for two strings, read over each whole string and its NUL; the
   post of FMH_Rt.v:160 (fuzz_manifest's call is inside its poison window, this one is not, so the post is the
   plain art_post). twoway_strstr reads the stack-protector cells (0x9b9e4 `ld s3, [0xa3e98]`, 0x9b9e8 `ld a0, 0(s3)`,
   stored as a canary at 0x9b9fc), so the row takes gotw / guard and asks aguard_ok, in the form of RtString.v:139
   astrspn_realizes (the image-A owner's finding, 2026-10-30 16:08Z). *)
Definition astrstr_realizes (pc gotw guard : Z) : Prop :=
forall ly S W regs mem md x y st sw,
aguard_ok segs W mem gotw guard ->
PRE (2 * ESTACK) ly S W regs mem md ->
getr regs 10 = w64 x -> getr regs 11 = w64 y -> 0 < x -> 0 < y ->
STR W mem x st -> STR W mem y sw ->
RD (2 * ESTACK) W regs mem x (astr_len st + 1) ->
(* 8 bytes of band room past the string: the kit's chk_ok needs region_in_mem p 8 (lib/A/Bz/A/I_consts.v:20-21) *)
amem_range x (astr_len st + 8) ->
RD (2 * ESTACK) W regs mem y (astr_len sw + 1) ->
(* 8 bytes of band room past the string: the kit's chk_ok needs region_in_mem p 8 (lib/A/Bz/A/I_consts.v:20-21) *)
amem_range y (astr_len sw + 8) ->
atail_vis segs W mem (x + astr_len st) -> atail_vis segs W mem (y + astr_len sw) ->
rt_rom_view segs B W mem ->
SRr segs W (cfg_at segs pc regs mem md)
(POST (2 * ESTACK) ly S W regs mem md (fun _ => False)
(fun regs' _ =>
(getr regs' 10 = w64 0 /\ no_occ (ZS st) (ZS sw)) \/
(exists j, first_occ (ZS st) (ZS sw) j /\ getr regs' 10 = w64 (x + Z.of_nat j)))).

(* Row 9. musl isalnum(c), called directly (no wrapper). Image B: 0x9094c (28 B, a leaf: no stack, no memory).
   Template: FMH_Rt.v:170 (registers only), with its window ESTACK (fuzz_manifest's STK_RT_ISALNUM, FMH_Base.v:92)
   and RtDefs.v's art_post. *)
Definition aisalnum_realizes (pc : Z) : Prop :=
forall ly S W regs mem md c,
PRE (ESTACK) ly S W regs mem md ->
getr regs 10 = w64 c -> 0 <= c < 256 ->
SRr segs W (cfg_at segs pc regs mem md)
(POST (ESTACK) ly S W regs mem md (fun _ => False)
(fun regs' _ => getr regs' 10 <> w64 0 <-> alnum_b c = true)).

(* Row 10. strcasecmp(x, y). Image B: trampoline 0x43aa8 -> wrapper 0x44b84 (1280 B), which compares the bytes itself
   and checks i + 1 bytes of each string (i the index where the comparison stopped; with the strict-string flag set,
   len + 1). Template: row 7 without n, so each read is over the whole string and its NUL (as RtString.v:108
   astrcmp_realizes reads); the post is FMH_Rt.v:133's with no bound: the strings and their NULs agree under lc. *)
Definition astrcasecmp_realizes (pc : Z) : Prop :=
forall ly S W regs mem md x y sx sy,
PRE (2 * ESTACK) ly S W regs mem md ->
getr regs 10 = w64 x -> getr regs 11 = w64 y -> 0 < x -> 0 < y ->
STR W mem x sx -> STR W mem y sy ->
RD (2 * ESTACK) W regs mem x (astr_len sx + 1) ->
(* 8 bytes of band room past the string: the kit's chk_ok needs region_in_mem p 8 (lib/A/Bz/A/I_consts.v:20-21) *)
amem_range x (astr_len sx + 8) ->
RD (2 * ESTACK) W regs mem y (astr_len sy + 1) ->
(* 8 bytes of band room past the string: the kit's chk_ok needs region_in_mem p 8 (lib/A/Bz/A/I_consts.v:20-21) *)
amem_range y (astr_len sy + 8) ->
atail_vis segs W mem (x + astr_len sx) -> atail_vis segs W mem (y + astr_len sy) ->
rt_rom_view segs B W mem ->
SRr segs W (cfg_at segs pc regs mem md)
(POST (2 * ESTACK) ly S W regs mem md (fun _ => False)
(fun regs' _ => getr regs' 10 = w64 0 <-> map lc ((ZS sx) ++ [0]) = map lc ((ZS sy) ++ [0]))).

(* Row 11. strrchr(x, c), 0 < c < 256. Image B: trampoline 0x43ab8 -> wrapper 0x45e50 (736 B), which checks len + 1
   bytes, -> musl strrchr 0x9b678, which calls the strlen wrapper (0x9b690) and then musl memrchr 0x9afa4 over
   len + 1 bytes. Template: row 6, premise for premise; the post names the LAST index of c. The window 2 * ESTACK
   holds the wrapper's 2144 bytes, strrchr's 32 and the strlen wrapper's ESTACK (RtString.v:80). *)
Definition astrrchr_realizes (pc : Z) : Prop :=
forall ly S W regs mem md x c s,
PRE (2 * ESTACK) ly S W regs mem md ->
getr regs 10 = w64 x -> getr regs 11 = w64 c -> 0 < c < 256 -> 0 < x ->
STR W mem x s ->
RD (2 * ESTACK) W regs mem x (astr_len s + 1) ->
(* 8 bytes of band room past the string: the kit's chk_ok needs region_in_mem p 8 (lib/A/Bz/A/I_consts.v:20-21) *)
amem_range x (astr_len s + 8) ->
atail_vis segs W mem (x + astr_len s) ->
rt_rom_view segs B W mem ->
SRr segs W (cfg_at segs pc regs mem md)
(POST (2 * ESTACK) ly S W regs mem md (fun _ => False)
(fun regs' _ =>
(getr regs' 10 = w64 0 /\ ~ In c (ZS s)) \/
(exists j, last_at (ZS s) c j /\ getr regs' 10 = w64 (x + Z.of_nat j)))).

(* Row 12. strncpy(d, x, n). Image B: trampoline 0x43b40 -> wrapper 0x4b188 (1328 B): from_size = min (n,
   strnlen (x, n) + 1) (musl strnlen 0x9b634 through the memchr wrapper), the overlap check of [d, d + from_size) and
   [x, x + from_size), the check of from_size bytes at x and of n bytes at d, then musl strncpy 0x9b4fc ->
   stpncpy 0x9b524, which copies a word at a time when x and d share their alignment and pads through the memset
   wrapper. Template: RtString.v:214 astrcpy_realizes, with the read over min (n, len + 1) bytes as
   RtString.v:121's, the write over [d, d + n), and the post: the first min (n, len) bytes of the string, then NUL
   bytes up to n. The window is 2 * ESTACK (the program calls it directly; astrcpy's ESTACK is for strcat's nested
   call, RtString.v:210-213). *)
Definition astrncpy_realizes (pc : Z) : Prop :=
forall ly S W regs mem md d x n s,
PRE (2 * ESTACK) ly S W regs mem md ->
getr regs 10 = w64 d -> getr regs 11 = w64 x -> getr regs 12 = w64 n -> 0 <= n < 2 ^ 32 -> 0 < d -> 0 < x ->
STR W mem x s ->
RD (2 * ESTACK) W regs mem x (Z.min n (astr_len s + 1)) ->
(* 8 bytes of band room past the source string: the kit's chk_ok needs region_in_mem p 8 (lib/A/Bz/A/I_consts.v:20-21) *)
amem_range x (astr_len s + 8) ->
WR (2 * ESTACK) ly S W regs mem d n ->
(* 8 bytes of band room past the written range: the kit's chk_ok needs region_in_mem p 8 (lib/A/Bz/A/I_consts.v:20-21) *)
amem_range d (n + 8) ->
(* the written range holds no read-only image byte (as for strcpy, RtString.v:225-226) *)
(forall a, d <= a < d + n -> a < kLowMemEnd -> ~ in_rom segs a) ->
atail_vis segs W mem (x + astr_len s) ->
(* the destination lies below the source, or at or past the end of the word that holds the source's last read
   byte (RtString.aword_end; the wrapper's overlap check needs at least the two from_size ranges apart) *)
(d + n <= x \/ RtString.aword_end x (Z.min n (astr_len s + 1)) <= d) ->
rt_rom_view segs B W mem ->
SRr segs W (cfg_at segs pc regs mem md)
(POST (2 * ESTACK) ly S W regs mem md (fun a => d <= a < d + n)
(fun regs' mem' => getr regs' 10 = w64 d /\
abytes_at segs W mem' d (firstn (Z.to_nat n) s ++ repeat (Z_to_bv 8 0) (Z.to_nat n - length s)%nat))).

(* Row 3. strtol(x, NULL, 10). Image B: trampoline 0x43b44 -> wrapper 0x4b6b8 (196 B) -> musl __strtol_internal
   0x9a9e8 (stack protector: 0x9aa14 `ld s3, [0xa3e98]`, 0x9aa18 `ld a0, 0(s3)`), then StrtolFixAndCheck, which with
   endptr NULL writes no end pointer and checks (end - x) + 1 bytes of the string. Template: RtNumber.v:81
   astrtol_realizes with a1 = 0 in place of `getr regs 11 = w64 e /\ 0 < e`: no end-pointer premise and no
   end-pointer write; a0 and the errno cell as astrtol_realizes states them, the written range the errno cell
   alone (as RtNumber.v:60 aatoi_realizes). *)
Definition astrtol0_realizes (pc gotw guard : Z) : Prop :=
forall ly S W regs mem md x str ev,
aguard_ok segs W mem gotw guard ->
PRE (3 * ESTACK) ly S W regs mem md ->
getr regs 10 = w64 x -> getr regs 11 = w64 0 -> getr regs 12 = w64 10 -> 0 < x ->
STR W mem x str -> x + astr_len str + 1 < 2 ^ 64 ->
RD (3 * ESTACK) W regs mem x (astr_len str + 1) ->
(* 8 bytes of band room past the string: the kit's chk_ok needs region_in_mem p 8 (lib/A/Bz/A/I_consts.v:20-21) *)
amem_range x (astr_len str + 8) ->
atail_vis segs W mem (x + astr_len str) ->
(* the string does not hold the errno cell (as RtNumber.v:103-104) *)
(as_errno B + 4 <= x \/ x + astr_len str + 1 <= as_errno B) ->
rd32 (aview segs (w_H W) mem) (as_errno B) ev ->
rt_rom_view segs B W mem ->
SRr segs W (cfg_at segs pc regs mem md)
(POST (3 * ESTACK) ly S W regs mem md (aerrno_cell B)
(fun regs' mem' => getr regs' 10 = w64 (PIS.s10_val str) /\
rd32 (aview segs (w_H W) mem') (as_errno B) (bv_unsigned (PIS.s10_errno str (Z_to_bv 64 ev))))).

End c.
End b.

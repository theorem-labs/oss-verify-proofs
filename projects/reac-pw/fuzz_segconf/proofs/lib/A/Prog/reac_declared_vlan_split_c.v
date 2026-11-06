(* reac_declared_vlan_split (reac_declared_vlan.c:32-62; fuzz_segconf.asan 0x89b8c, 460 bytes, 115 instructions;
   frame 64 bytes, no side-stack frame): the contract of the ASan build's code, in plugin-hostd/fuzz_command's
   lib/A/Prog form (afn_pre at the entry, SRr of apost_base at the return).
   Functional content: the plain contract lib/Prog/reac_declared_vlan_split_c.v:12-129 (split_copy :59-70,
   split_pre :93-103, split_W :106-109, the return value :118, the post :122-127), restated over the ASan reader.
   What the code does (objdump of fuzz_segconf.asan, 0x89b8c-0x89d54): 0 when segment, parent, cap or vid is 0
   (four beqz, 0x89bb8-0x89bd0; the premise excludes them); dot = strrchr(segment, 0x2e) (jal 0x89be8); 0 when dot
   is NULL or dot = segment; lbu of dot[1] at 0x89c10, 0 when it is the NUL; the digit loop (0x89c24 .. bnez
   0x89c48, lbu at 0x89c3c) returns 0 at a byte with byte - 0x30 >u 9; strtol(dot + 1, NULL, 10) (jal 0x89c68,
   li a2, 10 at 0x89c60 and li a1, 0 at 0x89c64); v outside [1, 4094] returns 0 (bgeu 0x89c80); plen = dot -
   segment, 0 when plen + 1 >u cap or plen + 1 >u 16 (bltu 0x89cbc, 0x89cc4); strlen(segment) (jal 0x89ccc), 0 when
   it is >= 16 (bltu 0x89cd8); memcpy(parent, segment, plen) through the checked __asan_memcpy (jal 0x89ce8) and
   parent[plen] = 0 (sb 0x89d00); name_ok(parent) (jal 0x89d08) = 0 returns 0; else the vid cell gets v (sh
   0x89d20) and it returns 1. The branches are the plain build's, so the plain post holds: a0 = 1 and parent / vid
   hold SegModel.vlan_split s when it is Some, a0 = 0 when it is None.
   What it reads: the shadow base (the GOT word as_got_shadow B, image A 0xa2a50, loaded at 0x89bd8; AR's const
   law); the segment's bytes, its NUL and the slack to the next 8-byte boundary (strrchr and strlen run musl's
   word-at-a-time loops); through strtol, the errno cell and the stack-protector cells. What it writes outside its
   stack window: parent[0 .. plen] when it reaches the memcpy (split_copy), and the vid cell when it returns 1.
   FOOTPRINT: split_W below is the plain write list (:106-109) without its first two ranges. The first,
   [sp - SPLIT_STACK, sp), is the stack window, which apost_base keeps by STK_reac_declared_vlan_split. The second,
   the errno cell [tp - 164, tp - 160), is as_errno B here, which the kit treats as runtime scratch (ascratch,
   lib/Reusable/YG0d.v:216-217): the journal exempts it and does not keep it (lib/Reusable/YCbq.v:479, :487), and a
   range of it in the footprint would break every caller's composition, because awr_byte admits a callee's
   footprint byte only in a block, a frame, the caller's real stack or a program static (YCbq.v:594-603, :962).
   ERRNO: the plain post keeps the errno cell at ev (:122). The A post has no errno conjunct of its own: its sa_kept
   gives it, because the errno cell is an image byte (api_env, YCbq.v:1100-1101), outside the stack window and off
   both footprint ranges (parent and vid lie in a side-stack frame, a heap block or the real stack above sp, and no
   image byte is any of these). The walk proves it kept: strtol runs only on a tail of 1 to 13 digits (dot[1] is a
   digit, every tail byte is a digit, length s < 16 and di >= 1), so __intscan sets neither EINVAL nor ERANGE, and
   row 3's errno value, its template's s10_errno str ev (fuzz_command lib/A/Rt/RtNumber.v:81-104), is ev (the plain
   build's argument, CMD's __intscan_c.v: s10_errno str ev = ev when s10_nd str <> 0 and s10_inrange str); strrchr,
   strlen and the checked memcpy keep every byte outside their windows and destinations, name_ok by its own
   sa_kept. The plain errno_ok premise (:85-87) goes: row 3's template asks rd32 of the errno cell at the call,
   which the walk gets from the kit's AR_errno_present (YCbq.v:1126) under errno_rom segs B (YCbq.v:1103-1104), an
   image fact the walk takes as a Section hypothesis, as the kit's own Section d0 takes api_env (YCbq.v:1152).
   strtol's string does not hold the errno cell (row 3's template asks it): every arm of sa_loc keeps the segment
   off it.
   No abort site (provenance/evidence/image-tables/program.asan.tsv line 31).
   ASAN FACTS ADDED over the plain contract (rd = aview segs (w_H W) mem):
   - inline check 1, load1 of dot[1] at 0x89c10 (shadow test 0x89c00-0x89c0c, slow path 0x89d2c, error arm
     __asan_report_load1 at 0x89d34), and inline check 2, load1 of each later byte of the tail at 0x89c3c (shadow
     test 0x89c2c-0x89c38, slow path 0x89c50, error arm __asan_report_load1 at 0x89c5c): dot lies in the segment
     and the loop stops at its NUL, so both are killed by sa_addr rd segment (length s + 1).
   - inline check 3, store1 of parent[plen] at 0x89d00 (shadow test 0x89cf0-0x89cfc, slow path 0x89d38, error arm
     __asan_report_store1 at 0x89d40): plen <= 15, killed by sa_addr rd parent 16.
   - inline check 4, store2 of the vid cell at 0x89d20 (shadow test 0x89d10-0x89d1c, slow path 0x89d44, error arm
     __asan_report_store2 at 0x89d54): killed by sa_addr rd vid 2.
   - interceptor ranges: strrchr and strlen read [segment, segment + length s + 1), strtol reads the tail [dot + 1,
     segment + length s + 1): sa_addr rd segment (length s + 1), with sa_str's slack (the atail_vis the RtString
     forms of rows 11 and 16 ask) and amem_range segment (length s + 8), the band room row 3's template asks of its
     string (amem_range x (astr_len str + 8), RtNumber.v:81-104, where x + astr_len str = segment + length s);
     length s < 16 gives the n < 2 ^ 32 of each range (aread_ok). The checked memcpy reads [segment, segment +
     plen) and writes [parent, parent + plen): aintrin_realizes OCpy (lib/Reusable/YG0d.v:326) asks both ranges
     addressable (sa_addr), the destination in a place the call may write (sa_dst) and the two apart (sa_disj
     segment (cstr_span segment s) parent 16, the plain apart with seg_spec.cstr_span for length + 8).
   - where each object lies: the segment by sa_loc (the one caller passes c + 356 i, the name field of seg[i]
     inside the reader's heap block); parent and the vid cell by sa_dst (the caller's class-1 side-stack frame,
     whose description at image A 0x176dc puts parent at frame + 32, 16 bytes, and vid at frame + 64, 2 bytes;
     their shadow is made 00 00 / 02 just before this call, 0x899d8-0x899e4). Every arm keeps them outside this
     call's stack window, which replaces the plain apart premises from [lo, sp); parent and vid stay apart from
     each other (sa_disj vid 2 parent 16), as in the plain pre. The plain wr_at / rw_cells writability is sa_dst's.
   - sa_ssp rd gotw guard, the plain ssp_ok: musl's __strtol_internal (image A 0x9a23c) loads the GOT word 0xa36d8
     (ld at 0x9a268), which holds 0x5ff078 = __stack_chk_guard (read from the pin's PT_LOAD bytes; nm), and
     compares the guard at its exit (0x9a2c4-0x9a2cc); row 3's template asks aguard_ok gotw guard. gotw and guard
     are parameters.
   - arodata_okP over the read-only window RLO RHI: rows 3, 11 and 16 ask rt_rom_view (fuzz_command
     lib/A/Rt/RtDefs.v:145).
   - sa_kept segs W mem W' mem' regs STK_reac_declared_vlan_split (split_E parent vid s) in the post: every byte
     outside the stack window and the footprint reads as at the entry, the shadow of an image object included,
     which the journal alone does not keep (SegABase.v's sa_kept, found by the G4 / G5 walks); split_E
     is split_W's two ranges, one disjunct each. True of the code: it takes no side-stack
     frame and calls no set_shadow entry (provenance/evidence/image-tables/program.asan.tsv line 31, callsites.asan.tsv lines
     373-381); its own stores are the saved registers in its frame (0x89b90-0x89bac), parent[plen] (0x89d00) and
     the vid cell (0x89d20); the checked memcpy writes only [parent, parent + plen) and its ESTACK scratch
     (aintrin_realizes, lib/Reusable/YG0d.v:343); strrchr and strlen write only their scratch (the RtString form,
     art_post's keep clause with E = False); strtol writes its scratch and the errno cell, which it leaves at ev
     (ERRNO above), and with the NULL end pointer no end cell; name_ok gives the same clause over its window,
     which lies in this one. ROW 3 MUST THEREFORE KEEP its template's errno value (s10_errno str ev) in its post:
     a post that only names the errno cell as written would make this clause unprovable.
   - no side-stack frame and no printf: apost_base, EV_reac_declared_vlan_split = 0, post tail sa_noalloc.
   Call site (provenance/evidence/image-tables/callsites.asan.tsv line 368): reac_segconf_declared 0x899f8 with a0 = c + 356 i (s6,
   advanced by 356 at 0x89a48), a1 = frame + 32 (s10), a2 = 16, a3 = frame + 64 (s11).
   image A: A_reac_declared_vlan_split = 0x89b8c; STK_reac_declared_vlan_split = 64 + 3 * ESTACK (INFERENCE: its
   frame above the widest window it calls, row 3's 3 * ESTACK - RtSeg.astrtol0_realizes, accepted at
   commit 80d098bd1905, keeps its template's window; row 11 asks 2 * ESTACK, row 16 ESTACK, the
   checked memcpy ESTACK, name_ok 64 + ESTACK); RLO RHI = image A's RELRO bounds; gotw =
   0xa36d8, guard = 0x5ff078.
   IMAGE-INDEPENDENT: no image module is Required; A_reac_declared_vlan_split, STK_reac_declared_vlan_split, RLO,
   RHI, gotw, guard and every other image cell are parameters (or fields of B).
   The WALK takes these runtime entries as Section hypotheses (the interceptor lane's interface
   provenance/evidence/interceptors/INTERFACE-A-interceptors.md (commit 7068323e2626): rows 3 and 11 as at e45889d6935a,
   row 16 in the accepted v1, 5e0b8a44fdc; at e45889d6935a strlen is that file's DECISION 2, option (b)):
     RtSeg.astrrchr_realizes (pc) (row 11, lib/A/Rt/RtSeg.v:173 at commit 80d098bd1905), at the
       strrchr trampoline (image A 0x43a2c);
     RtSeg.astrtol0_realizes (pc gotw guard) (row 3, lib/A/Rt/RtSeg.v:226 at 80d098bd1905: the NULL end pointer
       form, written for exactly this call site, 0x89c68 with a1 = 0; its template RtNumber.astrtol_realizes
       needs 0 < e), at the strtol trampoline (image A 0x43ab8);
     RtString.astrlen_realizes (row 16), at the strlen trampoline (image A 0x43a0c);
     aintrin_realizes OCpy (lib/Reusable/YG0d.v:326; the frame's text, not the interceptor lane's), at pc_memcpy
       (image A __asan_memcpy 0x558e0);
     name_ok_contract (lib/A/Prog/name_ok_c.v) at name_ok's entry and stack (image A 0x89d58).
   They are NOT premises of this contract: the statement does not mention them. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI04 YI09 YN3v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
(* The parent length split copies: [Some di], dot = segment + di, when every test before name_ok passes; it then
   writes parent[0 .. di] (memcpy and the NUL). The plain split_copy (lib/Prog/reac_declared_vlan_split_c.v:59-70)
   word for word, SegModel's names qualified; the plain file is not Required (it Requires the plain image). *)
Definition split_copy (s : list Z) : option nat :=
match SegModel.strrchr s DOT with
| None => None
| Some di =>
  if (di =? 0)%nat || (SegModel.hd0 (skipn (S di) s) =? 0) then None else
  let tail := SegModel.cut_nul (skipn (S di) s) in
  if negb (forallb SegModel.isdigit tail) then None else
  let v := SegModel.strtol10 tail in
  if (v <? 1) || (4094 <? v) then None else
  if (16 <? di + 1)%nat || (16 <? di + 1)%nat then None else
  if (16 <? SegModel.strlen s + 1)%nat then None else Some di
end.
(* The bytes it writes outside its stack window: parent[0 .. di] when it copies, the vid cell when it returns 1 (the
   plain split_W, :106-109, without the stack window and the errno cell; see the head comment). *)
Definition split_W (parent vid : Z) (s : list Z) : list (Z * Z) :=
match split_copy s with Some di => [(parent, parent + Z.of_nat di + 1)] | None => [] end ++
match SegModel.vlan_split s with Some _ => [(vid, vid + 2)] | None => [] end.
(* The byte set of split_W, one disjunct per range: what the post's sa_kept exempts besides the stack window. *)
Definition split_E (parent vid : Z) (s : list Z) (a : Z) : Prop :=
(match split_copy s with Some di => parent <= a < parent + Z.of_nat di + 1 | None => False end) \/
(match SegModel.vlan_split s with Some _ => vid <= a < vid + 2 | None => False end).
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section c.
Variable segs : list Segment.
Section d.
Variable B : asyms.
(* What split asks of its caller (the plain split_pre, :93-103, over the reader rd = aview segs (w_H W) mem; regs
   are this call's entry registers): the segment a C string of fewer than 16 bytes with its slack (sa_str), its
   bytes and NUL addressable, the band room row 3 asks past it, in a heap block, a side-stack frame or the image;
   parent 16 bytes and the vid cell 2 bytes (2-aligned) in places the call may write, addressable, apart from each
   other and parent apart from the segment's read span; cap = 16 (the spine's IFNAMSIZ, SegModel.v:764); the
   stack-protector cells strtol compares. The plain errno_ok, stack_ok, apart-from-[lo, sp) and mem_inv conjuncts
   are afn_pre's and the places' here (head comment). Outside the sections:
   split_pre segs B ly S W mem regs segment parent cap vid s gotw guard. *)
Definition split_pre (ly : alayout) (S : astate) (W : world segs) (mem : word -> option byte)
(regs : bvmap 5 word) (segment parent cap vid : Z) (s : list Z) (gotw guard : Z) : Prop :=
segment <> 0 /\ sa_str (aview segs (w_H W) mem) segment s /\ (length s < 16)%nat /\
sa_addr (aview segs (w_H W) mem) segment (Z.of_nat (length s) + 1) /\
amem_range segment (Z.of_nat (length s) + 8) /\
sa_loc segs B ly S segment (Z.of_nat (length s) + 1) /\
parent <> 0 /\ cap = 16 /\ sa_dst segs B ly S W mem regs parent 16 /\
sa_addr (aview segs (w_H W) mem) parent 16 /\
sa_disj segment (seg_spec.cstr_span segment s) parent 16 /\
(* vid is the second reason sa_dst's real-stack arm carries astack_pres (SegABase.v, the comment on sa_dst;
   found by the G4 / G5 walk of reac_declared_vlan_split): the code keeps vid in s0 (`mv s0,a3` at 0x89bcc) up to
   `jal name_ok` at 0x89d08, whose afn_pre asks `achain ly rd (sp - 64) vid ch`, which for a real-stack vid
   needs the word at vid - 8. The one caller passes a slot of its class-1 side-stack frame, which takes the
   frame arm, but the contract must hold in every arm. *)
vid <> 0 /\ vid mod 2 = 0 /\ sa_dst segs B ly S W mem regs vid 2 /\
sa_addr (aview segs (w_H W) mem) vid 2 /\ sa_disj vid 2 parent 16 /\
sa_ssp (aview segs (w_H W) mem) gotw guard.
(* the events this call spends: 0, it reaches no allocator entry (nor does name_ok) *)
Definition EV_reac_declared_vlan_split : Z := 0.
Definition reac_declared_vlan_split_contract
(A_reac_declared_vlan_split STK_reac_declared_vlan_split RLO RHI gotw guard : Z) : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (segment parent cap vid : Z) (s : list Z),
afn_pre segs B STK_reac_declared_vlan_split ly S W regs mem md ch ->
arodata_okP segs RLO RHI B (aview segs (w_H W) mem) ->
getr regs 10 = w64 segment -> 0 <= segment < 2 ^ 64 -> getr regs 11 = w64 parent -> 0 <= parent < 2 ^ 64 ->
getr regs 12 = w64 cap -> 0 <= cap < 2 ^ 64 -> getr regs 13 = w64 vid -> 0 <= vid < 2 ^ 64 ->
split_pre ly S W mem regs segment parent cap vid s gotw guard ->
st_nev S + EV_reac_declared_vlan_split <= EV_MAX ->
SRr segs W (cfg_at segs A_reac_declared_vlan_split regs mem md)
(apost_base segs B STK_reac_declared_vlan_split (split_W parent vid s) regs ly S W mem md
EV_reac_declared_vlan_split
(fun ly' S' W' regs' mem' md' =>
 getr regs' 10 = w64 (match SegModel.vlan_split s with Some _ => 1 | None => 0 end) /\
 (match SegModel.vlan_split s with
  | Some (p, v) => sa_strz (aview segs (w_H W') mem') parent p /\ sa_val (aview segs (w_H W') mem') vid 2 v
  | None => True
  end) /\
 sa_kept segs W mem W' mem' regs STK_reac_declared_vlan_split (split_E parent vid s) /\
 sa_noalloc B ly S ly' S')).
End d.
End c.
End b.

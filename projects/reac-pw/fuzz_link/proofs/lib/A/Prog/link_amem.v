(* reac-pw/fuzz_link, image A (the asan build): the views and the contract SHAPES that the image-A contracts of link's
   36 own functions share. This file is the image-A analog of lib/Prog/link_mem.v sections 2 and 3. It holds no
   address and no other number of the image: every contract takes the image's segments `segs`, its asyms `B`, its
   relro bounds `rlo rhi` and its addresses (lib/A/Prog/link_aaddr.v) as arguments.

   THE FORM (the reasons are in link-a/form/FORM.md (internal record, sha256 13aeff774164)).
   An A contract is pcap's caller-journal form (libreac/fuzz_pcap lib/A/Prog/PcapSourceCloseSpec.v
   tpcap_source_close_specX, itself cgif's YC20.v tlzw_spec / trfc_spec) over the program-global journal
   `ajournal_gx G XO OUT` of lib/A/W_journalG.v (pcap's, from plugin-hostd/fuzz_reply). The premise is the journal of
   whoever started it (in a run: LLVMFuzzerTestOneInput's, with G = link's globals); the Post is the SAME journal
   with its event index raised by the function's EV, and a kept clause relative to the call. Three reasons:
   - link's functions store into image globals (g_nl, g_names, g_say, ...). The donor's `ajournal`
     (Reusable/YCbq.v:347-369) keeps every image byte outside the allocator's statics and errno, so no contract over
     it can say "fuzz_close writes g_nl.open". `ajournal_gx G` keeps them outside G only (W_journalG.v:197-208).
   - they store through pointers into their CALLERS' side-stack frames (copy_attr into nl_talk's caller's buffer,
     fuzz_recv into nl_talk's class-9 frame, attr_text / nl_error into kernel's class-8 frame). The journal lets a
     callee write a frame its owner took (`awr_byte`'s `in_frames ly own`, YCbq.v:457-461); a journal that starts at
     the callee's own entry cannot hand those bytes on (W_journalG.v:477-486 `ajournal_gx_sub` asks every callee
     footprint byte to be a heap-block byte).
   - text_of stores into slots of LLVMFuzzerTestOneInput's REAL frame (link-a/design/ACEJ-WILD.md
     (internal record, sha256 6ee1df95f779) section 1); those lie inside the journal's window [sp0 - STK, sp0).

   How a plain `leaf pc K Pre Wr Post` (lib/Prog/link_mem.v:159-174) maps to `aleaf pc K EV SIDE Pre Wr Post`:
   - `Pre` and `Post` keep their link_spec content; the memory views are the A twins below (`anlk_at` for
     `nlk_at`, ...), read over `rdW W memc` (the memory the walk sees), at the addresses of link_aaddr.v.
   - `Wr` keeps its intervals, at image A's addresses, with a NULL buffer owning no bytes (`aivl`, the plain L7
     rule). On image A the write set is also a PREMISE: each byte of it must be one the caller's journal lets a
     callee write (`ajw`).
   - `K` is image A's: the function's frame (link-a/facts/asan-facts.tsv (internal record, sha256 05ab19b7928f) column `frame`)
     plus the deepest stack window of a callee on the covered path, where a runtime callee's window is the one its contract
     takes (ESTACK = 4096 for ecall_pre callees, 2 * ESTACK for the strnlen / bcmp wrappers, ASTACK = 16384 for the allocator).
   - `regs_preserved` becomes `aregs_preserved` (YG0d.v:22), the return to `ret_pc (getr regs 1)` becomes the
     return config `mkst regs2 (getr regs 1) mem2 (seg_rom segs)`, and `wmono` / `mem_inv` / `stk` become the
     journal (its AR, its window presence).
   - `munch ((sp - K, sp) :: Wr)` becomes `akept ... (spZ regs - K) (spZ regs) (inFP Wr)`, which is acall_kept
     (YCbq.v:822-833) with the write set excepted in the stack and image clauses too.
   - added: the journal and the four register facts of every pcap own-function contract, `gx_ok G`,
     `arodata_okP`, the event room `st_nev S + k + EV <= EV_MAX` (against the journal), the side-stack room
     `aside_room Sc SIDE`, and the
     shadow facts the instrumented checks need, which each contract states (`range_addressable (ard m) SHADOW_OFF`).
     The shadow base is not a premise: the code loads it from the .got cell `as_got_shadow B`, whose content AR's
     const law fixes (YG0f.v:193-195).
   - added to the Post: `frames S2 = frames Sc` (the side stack is back), `ashadow_kept` (the shadow of every heap
     block the call keeps is unchanged), and the descriptors and the file system kept.

   Sources: libreac/fuzz_pcap released lib/A (origin/ossv/recipes f26f9fbd8777), relocated onto link by a Theorem Labs lane at
   two internal commits (lib/A frame; lib/Reusable). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Export link_spec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ==========================================================================
   1. Views over image A's memory (the twins of link_mem.v section 2)
   ========================================================================== *)

Section v.
Variable segs : list Segment.

(* the byte reader the shadow predicates take: `ard (mrestrict (w_H W) mem)` is `aview segs (w_H W) mem`
   (YG0n.v:18-19) by definition (ard_aview below) *)
Definition ard (m : word -> option byte) : reader := fun a => option_map (fun b => bv_unsigned b) (mbyte segs m a).

(* bytes at an address (lib/Lib/Mem.v bytes_at, over the image-A segments) *)
Definition abytes (m : word -> option byte) (a : Z) (bs : list byte) : Prop :=
  0 <= a /\ a + Z.of_nat (length bs) <= 2 ^ 64 /\
  forall i, (i < length bs)%nat -> mbyte segs m (a + Z.of_nat i) = nth_error bs i.
(* n writable bytes (lib/Lib wr_at) *)
Definition awrange (m : word -> option byte) (a n : Z) : Prop :=
  forall i, 0 <= i < n -> writable_at segs m (a + i).
Definition au8arr (m : word -> option byte) (a : Z) (bs : list byte) : Prop :=
  abytes m a bs /\ awrange m a (Z.of_nat (length bs)).
(* a buffer of n bytes a function may read and write, its contents unknown *)
Definition abuf (m : word -> option byte) (a n : Z) : Prop :=
  exists junk, Z.of_nat (length junk) = n /\ au8arr m a junk.

(* little-endian words; like link_mem's u16_at / u32_at / u64_at they fix v only modulo 2 ^ (8 * n) *)
Definition au16_at (m : word -> option byte) (a v : Z) : Prop := val_mem segs m a 2 v.
Definition au32_at (m : word -> option byte) (a v : Z) : Prop := val_mem segs m a 4 v.
Definition au64_at (m : word -> option byte) (a v : Z) : Prop := val_mem segs m a 8 v.

(* a C string at `a`: its bytes, then a NUL, and no NUL inside *)
Definition acstr_at (m : word -> option byte) (a : Z) (s : list byte) : Prop :=
  abytes m a (s ++ [zb 0]) /\ ~ In (zb 0) s.

(* a buffer text_buf(cap) made: cap bytes and the guard byte after them *)
Definition atbuf_at (m : word -> option byte) (a cap : Z) (bs : list byte) : Prop :=
  au8arr m a (bs ++ [zb GUARD_BYTE]) /\ Z.of_nat (length bs) = cap.

(* the fake kernel, at its image-A base g (LA_G_NL) *)
Definition anlk_at (m : word -> option byte) (g : Z) (bs : list byte) : Prop :=
  au8arr m g bs /\ Z.of_nat (length bs) = NK_SIZE.
Definition amodel_at (m : word -> option byte) (p : Z) (bs : list byte) : Prop :=
  au8arr m p bs /\ Z.of_nat (length bs) = MD_SIZE.
Definition amarks_at (m : word -> option byte) (p : Z) (bs : list byte) : Prop :=
  au8arr m p bs /\ Z.of_nat (length bs) = MK_SIZE.
Definition anlw_at (m : word -> option byte) (p : Z) (bs : list byte) : Prop :=
  au8arr m p bs /\ Z.of_nat (length bs) = NW_SIZE.

(* the interface table of g_nl (link_mem.v iftab_at, with the index bound of LinkHelpers 2026-10-30) *)
Definition aiftab_at (m : word -> option byte) (g : Z) (bs : list byte) (tab : list (list byte * Z)) : Prop :=
  nk_n_if bs = Z.of_nat (length tab) /\ Z.of_nat (length tab) <= 80 /\
  forall i nm ix, nth_error tab i = Some (nm, ix) ->
    0 <= ix < 2 ^ 31 /\
    exists p, au64_at m (g + NK_IF_NAME + 8 * Z.of_nat i) p /\ p <> 0 /\
              acstr_at m p nm /\
              au32_at m (g + NK_IF_INDEX + 4 * Z.of_nat i) ix.

(* the four policy strings, at their image-A addresses *)
Definition apolicy_ro (m : word -> option byte) (prefix served vlan empty : Z) : Prop :=
  acstr_at m prefix S_PREFIX /\ acstr_at m served S_SERVED /\ acstr_at m vlan S_VLAN /\ acstr_at m empty [].

(* an argument read as `const char *`: NULL or a C string *)
Definition astr_arg (m : word -> option byte) (a : Z) (o : option (list byte)) : Prop :=
  match o with None => a = 0 | Some s => a <> 0 /\ acstr_at m a s end.
(* a buffer argument a reader may fill: NULL or a zero cap is "no buffer" *)
Definition abuf_arg (m : word -> option byte) (a cap : Z) : Prop :=
  a <> 0 -> 1 <= cap -> abuf m a cap.
End v.

(* registers *)
Definition aarg (regs : bvmap 5 word) (i : Z) : Z := argZ regs i.
Definition ares (regs : bvmap 5 word) : Z := bv_unsigned (getr regs 10).
Definition ares_i32 (regs : bvmap 5 word) : Z :=
  let v := ares regs mod 2 ^ 32 in if v <? 2 ^ 31 then v else v - 2 ^ 32.

(* separations (link_mem.v:229-254, unchanged in meaning) *)
Definition apart_frame (regs : bvmap 5 word) (K a n : Z) : Prop := a + n <= spZ regs - K \/ spZ regs <= a.
Definition apart_gnl (g a n : Z) : Prop := a + n <= g \/ g + NK_SIZE <= a.
Definition apart (a n b k : Z) : Prop := a + n <= b \/ b + k <= a.

(* a buffer interval of a write set: a NULL buffer owns no byte (the plain L7 rule) *)
Definition aivl (p n : Z) : Z * Z := (p, p + (if p =? 0 then 0 else n)).

(* ==========================================================================
   2. The A-state pieces and the two contract shapes
   ========================================================================== *)

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* The sink head is an EXPLICIT argument of every shape that depends on it, as on every pcap statement
   (PcapSourceCloseSpec.v, of pcap's porter): the only global sink_head instance in this closure is the plain
   build's (Reusable/YI5b.v src0_sink_head), so it must never be inferred. Inside the section it is a local instance. *)
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Variable segs : list Segment.
Variables rlo rhi : Z.
Variable B : asyms.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

Lemma ard_aview : forall (W : world segs) mem, ard segs (rdW W mem) = aview segs (w_H W) mem.
Proof. intros W mem. reflexivity. Qed.

(* A byte the caller's journal lets a callee write: a byte the journal's runner admits (its window but not an
   out-cell byte, a heap block of FP, a block allocated since the journal began, a side frame the journal's owner
   took), a byte of a program global of G, or an out cell. This is the per-byte condition of W_journalG.v:259-262
   awr_ok_x and of ajournal_gx_exec (W_journalG.v:303-304). *)
Definition ajw (G : list (Z * Z)) (XO : Z) (OUT : list (Z * Z)) (STK sp0 : Z) (FP : list (Z * Z))
    (ly : alayout) (S : astate) (lyc : alayout) (Sc : astate) (own : list (Z * Z)) (a : Z) : Prop :=
  (awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\ ~ (sp0 <= a < sp0 + XO)) \/
  inG G a \/ (inFP OUT a /\ sp0 <= a < sp0 + XO).

(* What a call keeps, relative to the call: acall_kept (YCbq.v:822-833) with the call's write set E excepted in
   the stack clause (out cells in the caller's real frame) and in the image clause (program globals). *)
Definition akept (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte)
    (W2 : world segs) (mem2 : word -> option byte) (slo shi : Z) (E : Z -> Prop) : Prop :=
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (slo <= a < shi) -> ~ E a ->
     aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a) /\
  (forall b m i, In (b, m) (ablocks B lyc Sc) -> 0 <= i < req_size m -> ~ E (b + i) ->
     aview segs (w_H W2) mem2 (b + i) = aview segs (w_H W) memc (b + i)) /\
  (forall a, in_img segs a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
     ~ E a -> aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a) /\
  (forall cid pos a, In (cid, pos) (frames Sc) ->
     (in_zr a (frame_rng lyc (cid, pos)) \/ in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8)) ->
     ~ E a -> aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a) /\
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (slo <= a < shi) -> apresent (w_H W) memc a -> apresent (w_H W2) mem2 a) /\
  (forall a, slo <= a < shi -> apresent (w_H W2) mem2 a).

(* The shadow of every heap block the call keeps is unchanged. The shadow of the side frames of Sc is in akept's
   frame clause; the real stack's and the image's shadow are fixed by AR at both ends (zshadow_ok, YG0n.v:188-191,
   and the const cells of the redzones). This is what lets a caller re-state `range_addressable` of a heap buffer
   after the call (ra_shadow_eq), e.g. op_read's text buffer between model_read and check_bounds. *)
Definition ashadow_kept (lyc : alayout) (Sc : astate) (ly2 : alayout) (S2 : astate)
    (W : world segs) (memc : word -> option byte) (W2 : world segs) (mem2 : word -> option byte) : Prop :=
  forall b m a, In (b, m) (ablocks B lyc Sc) -> In (b, m) (ablocks B ly2 S2) -> b <= a < b + req_size m ->
    aview segs (w_H W2) mem2 (shadow_addr a) = aview segs (w_H W) memc (shadow_addr a).

(* Room on the side stack: for each (class, depth) of SIDE, depth more frames of that class fit. A function that
   calls frame_alloc_<c> lists (c, d) with d the most frames of class c that are live at once in its call tree
   (its own and its callees'). With this premise the side stack always hands out a frame
   (YCbq.v:803-805 stack_malloc_progressP, YG0d.v:285-300 astack_malloc_realizes), so the real-stack fallback arm
   after `beqz` on the frame address is not taken. *)
Definition aside_room (S : astate) (SIDE : list (Z * Z)) : Prop :=
  Forall (fun cd => count_cid (fst cd) (frames S) + snd cd <= fs_frames (fst cd)) SIDE.

(* The return state every A contract gives: the caller's journal raised by EV, the callee-saved registers, the side
   stack as at the call, the descriptors and the file system, the kept clause and the heap-block shadow, and Q. *)
Definition apost (K EV : Z) (E : Z -> Prop)
    (G : list (Z * Z)) (XO : Z) (OUT : list (Z * Z)) (STK sp0 : Z) (FP : list (Z * Z))
    (ly : alayout) (S : astate) (W0 : world segs) (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (mdc : Model) (k : Z)
    (regs : bvmap 5 word)
    (Q : alayout -> astate -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
  : world segs -> config -> Prop :=
  fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
    c2 = mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom segs)) md2 /\
    ajournal_gx segs B G XO OUT STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 (k + EV) /\
    aregs_preserved regs regs2 /\ frames S2 = frames Sc /\
    m_fds md2 = m_fds mdc /\ m_fs md2 = m_fs mdc /\
    akept lyc Sc W memc W2 mem2 (spZ regs - K) (spZ regs) E /\
    ashadow_kept lyc Sc ly2 S2 W memc W2 mem2 /\
    Q ly2 S2 W2 regs2 mem2 md2.

(* The premises every A contract takes, at a call with registers regs on the caller's journal.
   The event room is stated against the JOURNAL (its start S and its index k), as cgif's trfc_spec does
   (Reusable/YC20.v:282): after a callee the index is k + EV, so a caller re-derives the room of its next callee from
   its own room, with no fact about st_nev at the call (finding 1 of link-a/form/audit.md
   (internal record, sha256 47ace00055b4)). The LAST conjunct (library-walk option c, accepted 2026-10-30): every byte
   the function writes is outside the read-only set `in_roP segs rlo rhi` (non-writable segments and the relro window).
   Every callee's apre takes `arodata_okP` (YC20.v:46), so a function that writes through a pointer argument and then
   calls a callee must re-establish it, which needs its write-set bytes off `in_roP`; `ajw` admits a byte by `inG G`,
   and `gx_ok` asks only `in_img` and not owned-static, so without this conjunct the premises did not decide it.
   Discharges: `not_ro_of_free` (an interval `ro_free_b` checks), `not_ro_off_img` (a stack, heap or side-frame byte,
   off the image), `not_ro_high`; at image A, link_aro.v's `LA_G_not_ro`. *)
Definition apre (K EV : Z) (SIDE : list (Z * Z)) (Wr : list (Z * Z))
    (G : list (Z * Z)) (XO : Z) (OUT : list (Z * Z)) (STK sp0 : Z) (FP : list (Z * Z))
    (ly : alayout) (S : astate) (W0 : world segs) (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (mdc : Model) (k : Z)
    (regs : bvmap 5 word) : Prop :=
  ajournal_gx segs B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k /\
  gx_ok segs B G /\
  arodata_okP segs rlo rhi B (aview segs (w_H W) memc) /\
  YK0s.ret_ok (getr regs 1) /\ 4096 <= raZ regs /\
  getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
  spZ regs mod 16 = 0 /\ sp0 - STK <= spZ regs - K /\ spZ regs <= sp0 /\
  st_nev S + k + EV <= EV_MAX /\
  aside_room Sc SIDE /\
  (forall a, inFP Wr a -> ajw G XO OUT STK sp0 FP ly S lyc Sc own a) /\
  (forall a, inFP Wr a -> ~ in_roP segs rlo rhi a).

(* SHAPE 1: a call that reaches no allocator (32 of the 36). It keeps the block list, and the whole allocator state
   but its side stack: `S2 = set_fs (st_fs S2) Sc`, so the event count, the meter (Reusable/YC5d.v:48-51
   ameter_fs_laws) and the depot are as at the call; the side stack is as at the call by apost's
   `frames S2 = frames Sc`. A caller needs this to state the meter room and the wild-trace room of a later
   allocating callee (LLVMFuzzerTestOneInput: text_buf at 0x835f4 after model_read and reac_link_alias_read). *)
Definition aleaf (pc K EV : Z) (SIDE : list (Z * Z))
    (Pre : bvmap 5 word -> (word -> option byte) -> Prop)
    (Wr : bvmap 5 word -> (word -> option byte) -> list (Z * Z))
    (Post : bvmap 5 word -> (word -> option byte) -> bvmap 5 word -> (word -> option byte) -> Prop) : Prop :=
  forall G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word),
    apre K EV SIDE (Wr regs (rdW W memc)) G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ->
    Pre regs (rdW W memc) ->
    SRr segs W (cfg_at segs pc regs memc mdc)
      (apost K EV (fun a => inFP (Wr regs (rdW W memc)) a) G XO OUT STK sp0 FP ly S W0 mem0 md0 own
         lyc Sc W memc mdc k regs
         (fun ly2 S2 W2 regs2 mem2 md2 =>
            S2 = set_fs (st_fs S2) Sc /\ Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\
            Post regs (rdW W memc) regs2 (rdW W2 mem2))).

(* SHAPE 2: a call that reaches the allocator (text_buf, text_of, mark_quietly; LLVMFuzzerTestOneInput is the
   frame's, AD1m.v / PcapEntry.v tfib_lib_contract_x). Beside SHAPE 1's premises it takes
   - the live-byte room and the meter room for what it may allocate (LIVE, MO under the meter MT), as pcap's
     tpcap_source_open_specX (PcapSourceOpenDefs.v:168-206) does;
   - the frame chain at the call and its spine in CTX, the contexts whose allocator traces the start-up universe
     lists (`In (raZ regs :: spine ch) CTX`, YC20.v:272);
   - `LedPre Sc`: the depot conjuncts of the cf layer's trace carrier (the frame reviewer's ruling 09:59Z,
     link-a/design/ACEJ-WILD.md (internal record, sha256 6ee1df95f779); adopted by the unit's owner 12:20Z: +1 per text_of call, the slot carries +96);
   and it gives, beside SHAPE 1's post without the block Permutation,
   - `mo_le MT Sc S2 MO` and `LedPost Sc S2`,
   - `PostA`, which also sees the block lists before and after, so it can name the fresh block.
   The intended instances, against the cf layer's names (`Univ` with field `u_wmax` in YG00.v, `wild_part` in
   YG01.v, `as_universe B : Univ` in YG0f.v; the wild-count lemmas in cgif lib/YGwildCount.v,
   on link lib/Reusable/YGwildCount.v), which come onto link with the lib/A frame:
     text_of:      LedPre  := fun Sc => (length (wild_part (as_universe B) (st_depot Sc)) + 1
                                          <= u_wmax (as_universe B))%nat
                   LedPost := fun Sc S2 => (length (wild_part (as_universe B) (st_depot S2))
                                            <= length (wild_part (as_universe B) (st_depot Sc)) + 1)%nat
     text_buf, mark_quietly: LedPre := fun _ => True (no wild trace at their allocator sites in ACej.v;
                   link-a/design/ACEJ-WILD.md (internal record, sha256 6ee1df95f779) section 3), and
                   LedPost := fun Sc S2 => (length (wild_part (as_universe B) (st_depot S2))
                                            <= length (wild_part (as_universe B) (st_depot Sc)))%nat
                   (the count does not grow; with `True` a caller could not state text_of's LedPre after a
                   text_buf call, e.g. LLVMFuzzerTestOneInput's text_of at 0x837d8 after text_buf at 0x835f4;
                   the form audit's finding 2).
   Until then they are parameters of this shape, so the contract files of the three compile now. *)
Definition aleaf_alloc (MT : ameter_ops) (pc K EV LIVE MO : Z) (SIDE : list (Z * Z)) (CTX : list (list Z))
    (LedPre : astate -> Prop) (LedPost : astate -> astate -> Prop)
    (Pre : bvmap 5 word -> (word -> option byte) -> Prop)
    (Wr : bvmap 5 word -> (word -> option byte) -> list (Z * Z))
    (PostA : bvmap 5 word -> (word -> option byte) -> bvmap 5 word -> (word -> option byte) ->
             list (Z * Z) -> list (Z * Z) -> Prop) : Prop :=
  forall G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) ch,
    apre K EV SIDE (Wr regs (rdW W memc)) G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ->
    blocks_bytes Sc + LIVE <= LIVE_MAX -> mo_ok MT Sc MO ->
    achain lyc (aview segs (w_H W) memc) (spZ regs) (s0Z regs) ch -> In (raZ regs :: spine ch) CTX ->
    LedPre Sc ->
    Pre regs (rdW W memc) ->
    SRr segs W (cfg_at segs pc regs memc mdc)
      (apost K EV (fun a => inFP (Wr regs (rdW W memc)) a) G XO OUT STK sp0 FP ly S W0 mem0 md0 own
         lyc Sc W memc mdc k regs
         (fun ly2 S2 W2 regs2 mem2 md2 =>
            mo_le MT Sc S2 MO /\ LedPost Sc S2 /\
            PostA regs (rdW W memc) regs2 (rdW W2 mem2) (ablocks B lyc Sc) (ablocks B ly2 S2))).

(* ==========================================================================
   THE READ SET (the library contracts' gap, accepted 2026-10-30)
   `aleaf` places every WRITTEN byte relative to the A-state (apre's `ajw`), but not a byte the function only
   READS through a pointer argument. Such a buffer may lie in a free side frame or a free heap range that a
   frame_alloc / malloc in the caller's chain hands out and writes (e.g. nl_talk's frame_alloc_9 at 0x889f8 stores
   into its fresh frame before fuzz_send reads req): it meets every Pre conjunct, and the Post, which speaks of the
   bytes the Pre read, is false of the bytes the code reads. The `_rd` shapes take a read set `Rd`, a predicate on
   the bytes (over the memory the walk sees), and ask each of its bytes to be one `akept` keeps across the call
   (`akb`); `akept_akb` is that fact. A predicate, not a list, because several reads are C strings whose length the
   Pre gives only through an existential (fuzz_if_nametoindex / index_of's name, attr_text's string and strlen's
   slack, kernel's texts): `fun regs m a => exists s, acstr_at segs m p s /\ p <= a <= p + Z.of_nat (length s)`.
   `rd_ivl lo hi` and `rd_of_fp FP` keep range-style read sets one-liners. With `Rd = fun _ _ _ => False` the
   shapes are `aleaf` / `aleaf_alloc` (`aleaf_rd_none`, `aleaf_alloc_rd_none`).
   ========================================================================== *)

(* read-set helpers: the bytes of [lo, hi), and the bytes of a list of half-open (lo, hi) intervals *)
Definition rd_ivl (lo hi : Z) : Z -> Prop := fun a => lo <= a < hi.
Definition rd_of_fp (FP : list (Z * Z)) : Z -> Prop := fun a => inFP FP a.

(* the bytes `akept lyc Sc W memc W2 mem2 slo shi E` keeps (outside E) AND whose shadow AR pins at both ends: in the
   real-stack row [ly_stk_lo lyc, ly_stk_hi lyc) outside the window [slo, shi) (AR's zshadow_ok, YG0n.v:188-191), in
   a heap block of Sc (AR's shadow_ok), in the image but not the runtime's statics or errno (the image granules'
   const cells), or in a side frame of Sc (its shadow: akept's frame clause).
   NARROWED (accepted by a Theorem Labs lane 2026-10-30): clause 1 was every byte above `alloc_ceiling` outside
   the window. akept keeps those bytes' values, but AR pins the shadow of none of them outside the stack row
   (alloc_ceiling <= a < ly_stk_lo, ly_stk_hi <= a < kHighMemEnd; checked by computation on AF0m by that lane), so a
   read-set byte placed there could not have its range_addressable / shadow_hull_vis re-stated for the next callee. *)
Definition akb (lyc : alayout) (Sc : astate) (slo shi a : Z) : Prop :=
  (ly_stk_lo lyc <= a < ly_stk_hi lyc /\ ~ (slo <= a < shi)) \/
  (exists b m, In (b, m) (ablocks B lyc Sc) /\ b <= a < b + req_size m) \/
  (in_img segs a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4)) \/
  (exists cid pos, In (cid, pos) (frames Sc) /\ in_zr a (frame_rng lyc (cid, pos))).

(* akept keeps every akb byte outside E. Clause 1 needs the stack row inside akept's [alloc_ceiling, 2 ^ 64); every
   journal gives that of its layout (ajournal_gx_row below, so akept_akb_gx needs no extra premise). *)
Lemma akept_akb : forall lyc Sc W memc W2 mem2 slo shi (E : Z -> Prop) a,
  alloc_ceiling <= ly_stk_lo lyc -> ly_stk_hi lyc <= 2 ^ 64 ->
  akept lyc Sc W memc W2 mem2 slo shi E -> akb lyc Sc slo shi a -> ~ E a ->
  aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a.
Proof.
  intros lyc Sc W memc W2 mem2 slo shi E a Hlo Hhi (K1 & K2 & K3 & K4 & _) Hb HE.
  destruct Hb as [(H1 & H2) | [(b & m & Hin & Hr) | [(H1 & H2 & H3) | (cid & pos & Hin & Hr)]]].
  - exact (K1 a ltac:(lia) H2 HE).
  - assert (Ea : b + (a - b) = a) by lia. pose proof (K2 b m (a - b) Hin ltac:(lia)) as Hk.
    rewrite Ea in Hk. exact (Hk HE).
  - exact (K3 a H1 H2 H3 HE).
  - exact (K4 cid pos a Hin (or_introl Hr) HE).
Qed.

(* What a journal says of the stack row at its current layout lyc: the row is above the allocator's ceiling, below
   2 ^ 47, and holds the journal's whole window [sp0 - STK, sp0 + XO) (astk_ok, YCbq.v:330-332, kept by layout_le). *)
Lemma ajournal_gx_row : forall G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k,
  ajournal_gx segs B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  alloc_ceiling <= ly_stk_lo lyc /\ ly_stk_hi lyc <= 2 ^ 47 /\
  ly_stk_lo lyc + STK <= sp0 /\ sp0 + XO <= ly_stk_hi lyc.
Proof.
  intros G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (_ & _ & (memS & HJ & _) & _).
  destruct HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hst & _ & _).
  destruct Hst as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
  destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Elo & Ehi & _).
  rewrite Elo, Ehi. lia.
Qed.

(* akept_akb on a call whose layout carries a journal (every call of an A contract: apre's first conjunct) *)
Lemma akept_akb_gx : forall G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k W2 mem2 slo shi
    (E : Z -> Prop) a,
  ajournal_gx segs B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  akept lyc Sc W memc W2 mem2 slo shi E -> akb lyc Sc slo shi a -> ~ E a ->
  aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a.
Proof.
  intros G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k W2 mem2 slo shi E a HJ.
  destruct (ajournal_gx_row G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k HJ) as (Hlo & Hhi & _).
  assert (H47 : 2 ^ 47 <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia).
  apply akept_akb; lia.
Qed.

(* a byte of the journal's window outside the callee's window is in akb's stack clause (e.g. kernel's cursor, in
   LLVMFuzzerTestOneInput's real frame) *)
Lemma akb_of_window : forall G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k slo shi a,
  ajournal_gx segs B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  sp0 - STK <= a < sp0 -> ~ (slo <= a < shi) -> akb lyc Sc slo shi a.
Proof.
  intros G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k slo shi a HJ Ha Hn.
  pose proof (ajournal_gx_row G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k HJ) as (_ & _ & H1 & H2).
  pose proof HJ as (_ & HXO & _). left. split; [lia | exact Hn].
Qed.

Definition aleaf_rd (pc K EV : Z) (SIDE : list (Z * Z))
    (Pre : bvmap 5 word -> (word -> option byte) -> Prop)
    (Rd : bvmap 5 word -> (word -> option byte) -> Z -> Prop)
    (Wr : bvmap 5 word -> (word -> option byte) -> list (Z * Z))
    (Post : bvmap 5 word -> (word -> option byte) -> bvmap 5 word -> (word -> option byte) -> Prop) : Prop :=
  forall G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word),
    apre K EV SIDE (Wr regs (rdW W memc)) G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ->
    (forall a, Rd regs (rdW W memc) a -> akb lyc Sc (spZ regs - K) (spZ regs) a) ->
    Pre regs (rdW W memc) ->
    SRr segs W (cfg_at segs pc regs memc mdc)
      (apost K EV (fun a => inFP (Wr regs (rdW W memc)) a) G XO OUT STK sp0 FP ly S W0 mem0 md0 own
         lyc Sc W memc mdc k regs
         (fun ly2 S2 W2 regs2 mem2 md2 =>
            S2 = set_fs (st_fs S2) Sc /\ Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\
            Post regs (rdW W memc) regs2 (rdW W2 mem2))).

Definition aleaf_alloc_rd (MT : ameter_ops) (pc K EV LIVE MO : Z) (SIDE : list (Z * Z)) (CTX : list (list Z))
    (LedPre : astate -> Prop) (LedPost : astate -> astate -> Prop)
    (Pre : bvmap 5 word -> (word -> option byte) -> Prop)
    (Rd : bvmap 5 word -> (word -> option byte) -> Z -> Prop)
    (Wr : bvmap 5 word -> (word -> option byte) -> list (Z * Z))
    (PostA : bvmap 5 word -> (word -> option byte) -> bvmap 5 word -> (word -> option byte) ->
             list (Z * Z) -> list (Z * Z) -> Prop) : Prop :=
  forall G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) ch,
    apre K EV SIDE (Wr regs (rdW W memc)) G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ->
    (forall a, Rd regs (rdW W memc) a -> akb lyc Sc (spZ regs - K) (spZ regs) a) ->
    blocks_bytes Sc + LIVE <= LIVE_MAX -> mo_ok MT Sc MO ->
    achain lyc (aview segs (w_H W) memc) (spZ regs) (s0Z regs) ch -> In (raZ regs :: spine ch) CTX ->
    LedPre Sc ->
    Pre regs (rdW W memc) ->
    SRr segs W (cfg_at segs pc regs memc mdc)
      (apost K EV (fun a => inFP (Wr regs (rdW W memc)) a) G XO OUT STK sp0 FP ly S W0 mem0 md0 own
         lyc Sc W memc mdc k regs
         (fun ly2 S2 W2 regs2 mem2 md2 =>
            mo_le MT Sc S2 MO /\ LedPost Sc S2 /\
            PostA regs (rdW W memc) regs2 (rdW W2 mem2) (ablocks B lyc Sc) (ablocks B ly2 S2))).

Lemma aleaf_rd_none : forall pc K EV SIDE Pre Wr Post,
  aleaf_rd pc K EV SIDE Pre (fun _ _ _ => False) Wr Post <-> aleaf pc K EV SIDE Pre Wr Post.
Proof.
  intros pc K EV SIDE Pre Wr Post. unfold aleaf_rd, aleaf. split.
  - intros H G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HA HP.
    apply H; [exact HA | intros a [] | exact HP].
  - intros H G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HA _ HP.
    exact (H G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HA HP).
Qed.

Lemma aleaf_alloc_rd_none : forall MT pc K EV LIVE MO SIDE CTX LedPre LedPost Pre Wr PostA,
  aleaf_alloc_rd MT pc K EV LIVE MO SIDE CTX LedPre LedPost Pre (fun _ _ _ => False) Wr PostA <->
  aleaf_alloc MT pc K EV LIVE MO SIDE CTX LedPre LedPost Pre Wr PostA.
Proof.
  intros MT pc K EV LIVE MO SIDE CTX LedPre LedPost Pre Wr PostA. unfold aleaf_alloc_rd, aleaf_alloc. split.
  - intros H G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ch HA HL HM HC HX HD HP.
    apply (H G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ch);
      [exact HA | intros a [] | exact HL | exact HM | exact HC | exact HX | exact HD | exact HP].
  - intros H G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ch HA _ HL HM HC HX HD HP.
    exact (H G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ch HA HL HM HC HX HD HP).
Qed.

End c.

(* A shadow fact moves to a later memory when the shadow bytes it reads are unchanged (pcap's
   PcapSourceCloseSpec.v ra_frame, over any two readers). *)
Lemma ra_shadow_eq : forall (rd rd' : reader) a n,
  range_addressable rd SHADOW_OFF a n ->
  (forall x, a <= x < a + n -> rd' (shadow_addr x) = rd (shadow_addr x)) ->
  range_addressable rd' SHADOW_OFF a n.
Proof.
  intros rd rd' a n HR Hk x Hx. destruct (HR x Hx) as (s & Hs & Ho). exists s. split; [|exact Ho].
  unfold shadow_of_addr. rewrite <- Hs. exact (Hk x Hx).
Qed.

(* ==========================================================================
   THE WRITE SET IS OFF THE READ-ONLY SET (apre's last conjunct): discharges. `in_roP segs rlo rhi` is YC20.v:43-45
   (a byte of a non-writable segment, or of the relro window [rlo, rhi)).
   ========================================================================== *)

(* an interval [lo, hi) that meets no non-writable segment and not the relro window, as one boolean *)
Definition ro_free_b (segs : list Segment) (rlo rhi lo hi : Z) : bool :=
  forallb (fun s => seg_writable s || (hi <=? Z.of_N (seg_base s)) ||
                    (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? lo)) segs &&
  ((hi <=? rlo) || (rhi <=? lo)).

Lemma not_ro_of_free : forall segs rlo rhi lo hi a,
  ro_free_b segs rlo rhi lo hi = true -> lo <= a < hi -> ~ in_roP segs rlo rhi a.
Proof.
  intros segs rlo rhi lo hi a H Ha Hro. unfold ro_free_b in H. apply andb_true_iff in H as [Hs Hw].
  destruct Hro as [(s & Hin & Hwr & Hr) | Hr].
  - rewrite forallb_forall in Hs. specialize (Hs s Hin). rewrite Hwr in Hs. cbn [orb] in Hs.
    apply orb_true_iff in Hs as [H1 | H1]; apply Z.leb_le in H1; lia.
  - apply orb_true_iff in Hw as [H1 | H1]; apply Z.leb_le in H1; lia.
Qed.

(* a byte off the image (a real-stack, heap or side-frame byte: YCbq.v blk_img / frm_img give `~ in_img` from AR)
   is not read-only, when the relro window lies in the image (pcap's `pa_relro_img`; link: PcapRelroA.v
   pcap_relro_in_image) *)
Lemma not_ro_off_img : forall segs rlo rhi a,
  (forall x, rlo <= x < rhi -> in_img segs x) -> ~ in_img segs a -> ~ in_roP segs rlo rhi a.
Proof.
  intros segs rlo rhi a Hr Hn [(s & Hin & _ & Hb) | Hw]; apply Hn;
    [exists s; split; [exact Hin | exact Hb] | exact (Hr a Hw)].
Qed.

(* every byte at or above kLowMemEnd (the real-stack row, above alloc_ceiling, in particular), when the image is
   below kLowMemEnd (the kit's `segs_low`) *)
Lemma not_ro_high : forall segs rlo rhi a,
  (forall x, in_img segs x -> 0 <= x < kLowMemEnd) -> (forall x, rlo <= x < rhi -> in_img segs x) ->
  kLowMemEnd <= a -> ~ in_roP segs rlo rhi a.
Proof.
  intros segs rlo rhi a Hlow Hr Ha. apply not_ro_off_img; [exact Hr|]. intros Hi. pose proof (Hlow a Hi). lia.
Qed.

(* ==========================================================================
   THE FP STATE (2026-10-30): the shapes for a call that returns at another FP state
   The printf-family contracts return at SOME FP state fx' (f registers but f10 kept, rounding mode 0) and need
   rounding mode 0 at entry (the GXA route: f10 is lost in pop_arg,
   proofs/cjson/cjson_read_fuzzer/lib/RL/G/G_pop_arg.v:481).
   A link function whose call tree reaches them (remember, reac_code_emit, reac_served_mark, mark_quietly) cannot
   use aleaf / aleaf_rd / aleaf_alloc(_rd): those fix one fx for the whole call. The shapes below are the `_rd`
   shapes with
   - one more Pre conjunct, rounding mode 0 at the entry fx (`YK0o.frm_zero (fp_csr fx)`; `YK0o.fp_frm_zero_fx0`
     gives it at the start-up's fx0), and
   - the Post `apostF`: there is fx' with `BoxBase.fxr fx fx'` (boxreg's relation, ported by path: f registers
     but f10 the entry's, fcsr the entry's or at rounding mode 0) and apost at fx', whose return config is
     `mkst regs2 ra mem2 rom` at fx'. Rounding mode 0 is carried: `fxr_frm0`.
   and with the Pre taking the caller's block list first (`ablocks B lyc Sc`): the FILE-path callees ask
   `In (f, 1304) (ablocks B lyc Sc)` for the sink FILE (the rewind / fprintf / vfprintf wrapper contracts), which
   a Pre over registers and memory only cannot state. `aleaf_rdb` / `aleaf_alloc_rdb` are the same two shapes at a
   fixed fx (`aleaf_rdb_rd`, `aleaf_alloc_rdb_rd`: with a Pre that ignores the list they are aleaf_rd /
   aleaf_alloc_rd).
   A caller applies an fx-form contract with `apostF_continue` (one SRr_bind; the continuation holds at every fx'
   with fxr fx fx'), runs the rest of its walk at fx' (a lemma of a section `Context {fx}`), and brings that walk's
   apostF at fx' back to its own entry fx with `srr_apostF_lift` (fxr is transitive, `fxr_trans`). A callee
   stated at a fixed fx is applied in that form through `aleaf_fx_of_rd` / `aleaf_fx_of_rdb` (and the alloc
   twins): fx' := fx.
   Models: boxreg (libreac/fuzz_boxreg, origin/ossv/recipes) Prog/BoxBase.v:71-105 apost_baseF / fxr /
   apost_baseF_continue, Prog/BoxLxDefs.v:337-355 lx_fxr_trans / lx_fxr_frm0, Rt/FMsnprintfSx.v:87-105
   srr_fx_continue; plugin-hostd/fuzz_command Prog/PaFx.v fxrel_of_frm0 and srr_apost_baseF_lift. boxreg's
   apost_baseF and apost_baseF_continue do not fit link as they are: their journal is the donor's ajournal, and
   their continuation asks the world unchanged (`W' = W`), which a journal post does not give.
   The Requires are here, after the shapes above, so that nothing they load can change how those shapes elaborate;
   both are qualified (BoxBase also defines YC20's in_roP / arodata_okP / apost_base). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require BoxBase.

(* fxr fxa fxb: fxb's f registers but f10 are fxa's, and fxb's fcsr is fxa's or at rounding mode 0 *)
Lemma fxr_trans : forall fxa fxb fxc : YK11.FPState,
  @BoxBase.fxr fxa fxb -> @BoxBase.fxr fxb fxc -> @BoxBase.fxr fxa fxc.
Proof.
  intros fxa fxb fxc (R1 & C1) (R2 & C2). split.
  - intros k Hk. rewrite (R2 k Hk). exact (R1 k Hk).
  - destruct C2 as [C2 | C2]; [rewrite C2; exact C1 | right; exact C2].
Qed.

(* rounding mode 0 at the entry is rounding mode 0 at every fx' a chain of calls returns *)
Lemma fxr_frm0 : forall fxa fxb : YK11.FPState,
  YK0o.frm_zero (@YK11.fp_csr fxa) -> @BoxBase.fxr fxa fxb -> YK0o.frm_zero (@YK11.fp_csr fxb).
Proof. intros fxa fxb H (_ & [C | C]); unfold YK0o.frm_zero in *; [rewrite C; exact H | exact C]. Qed.

(* the printf-family post (f registers but f10 kept, rounding mode 0) is fxr's right disjunct *)
Lemma fxr_of_frm0 : forall fxa fxb : YK11.FPState,
  (forall k : bv 5, bv_unsigned k <> 10 -> Sem.reg_get (@YK11.fp_regs fxb) k = Sem.reg_get (@YK11.fp_regs fxa) k) ->
  YK0o.frm_zero (@YK11.fp_csr fxb) -> @BoxBase.fxr fxa fxb.
Proof. intros fxa fxb HR HZ. split; [exact HR | right; exact HZ]. Qed.

Section fxs. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Variable segs : list Segment.
Variables rlo rhi : Z.
Variable B : asyms.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* apost at some fx' with fxr fx fx': the return config is at fx' *)
Definition apostF (K EV : Z) (E : Z -> Prop)
    (G : list (Z * Z)) (XO : Z) (OUT : list (Z * Z)) (STK sp0 : Z) (FP : list (Z * Z))
    (ly : alayout) (S : astate) (W0 : world segs) (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (mdc : Model) (k : Z)
    (regs : bvmap 5 word)
    (Q : alayout -> astate -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
  : world segs -> config -> Prop :=
  fun W2 c2 => exists fx' : YK11.FPState, @BoxBase.fxr fx fx' /\
    apost (fx := fx') SK segs B K EV E G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Q W2 c2.

(* a return at the entry's own fx (a path that reaches no printf-family call) *)
Lemma apostF_of_apost : forall K EV E G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Q W2 c2,
  apost SK segs B K EV E G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Q W2 c2 ->
  apostF K EV E G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Q W2 c2.
Proof. intros K EV E G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Q W2 c2 H.
  exists fx. split; [exact (@BoxBase.fxr_refl fx) | exact H]. Qed.

(* The continuation: a caller holding a walk into apostF (an fx-form callee's contract) goes on from the return
   config at the fx' the callee returns, for every fx' with fxr fx fx'. *)
Lemma apostF_continue : forall K EV E G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Q
    (Wc : world segs) (c : config) (R : world segs -> config -> Prop),
  SRr segs Wc c (apostF K EV E G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Q) ->
  (forall (fx' : YK11.FPState) (W2 : world segs) (c2 : config), wle Wc W2 -> @BoxBase.fxr fx fx' ->
     apost (fx := fx') SK segs B K EV E G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Q W2 c2 ->
     SRr segs W2 c2 R) ->
  SRr segs Wc c R.
Proof.
  intros K EV E G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Q Wc c R H1 H2.
  eapply SRr_bind; [exact H1|]. intros W2 c2 Hle (fx' & Hfx & HP). exact (H2 fx' W2 c2 Hle Hfx HP).
Qed.

(* aleaf_rd / aleaf_alloc_rd with the Pre taking the caller's block list first, at a fixed fx *)
Definition aleaf_rdb (pc K EV : Z) (SIDE : list (Z * Z))
    (Pre : list (Z * Z) -> bvmap 5 word -> (word -> option byte) -> Prop)
    (Rd : bvmap 5 word -> (word -> option byte) -> Z -> Prop)
    (Wr : bvmap 5 word -> (word -> option byte) -> list (Z * Z))
    (Post : bvmap 5 word -> (word -> option byte) -> bvmap 5 word -> (word -> option byte) -> Prop) : Prop :=
  forall G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word),
    apre SK segs rlo rhi B K EV SIDE (Wr regs (rdW W memc)) G XO OUT STK sp0 FP ly S W0 mem0 md0 own
      lyc Sc W memc mdc k regs ->
    (forall a, Rd regs (rdW W memc) a -> akb segs B lyc Sc (spZ regs - K) (spZ regs) a) ->
    Pre (ablocks B lyc Sc) regs (rdW W memc) ->
    SRr segs W (cfg_at segs pc regs memc mdc)
      (apost SK segs B K EV (fun a => inFP (Wr regs (rdW W memc)) a) G XO OUT STK sp0 FP ly S W0 mem0 md0 own
         lyc Sc W memc mdc k regs
         (fun ly2 S2 W2 regs2 mem2 md2 =>
            S2 = set_fs (st_fs S2) Sc /\ Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\
            Post regs (rdW W memc) regs2 (rdW W2 mem2))).

Definition aleaf_alloc_rdb (MT : ameter_ops) (pc K EV LIVE MO : Z) (SIDE : list (Z * Z)) (CTX : list (list Z))
    (LedPre : astate -> Prop) (LedPost : astate -> astate -> Prop)
    (Pre : list (Z * Z) -> bvmap 5 word -> (word -> option byte) -> Prop)
    (Rd : bvmap 5 word -> (word -> option byte) -> Z -> Prop)
    (Wr : bvmap 5 word -> (word -> option byte) -> list (Z * Z))
    (PostA : bvmap 5 word -> (word -> option byte) -> bvmap 5 word -> (word -> option byte) ->
             list (Z * Z) -> list (Z * Z) -> Prop) : Prop :=
  forall G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) ch,
    apre SK segs rlo rhi B K EV SIDE (Wr regs (rdW W memc)) G XO OUT STK sp0 FP ly S W0 mem0 md0 own
      lyc Sc W memc mdc k regs ->
    (forall a, Rd regs (rdW W memc) a -> akb segs B lyc Sc (spZ regs - K) (spZ regs) a) ->
    blocks_bytes Sc + LIVE <= LIVE_MAX -> mo_ok MT Sc MO ->
    achain lyc (aview segs (w_H W) memc) (spZ regs) (s0Z regs) ch -> In (raZ regs :: spine ch) CTX ->
    LedPre Sc ->
    Pre (ablocks B lyc Sc) regs (rdW W memc) ->
    SRr segs W (cfg_at segs pc regs memc mdc)
      (apost SK segs B K EV (fun a => inFP (Wr regs (rdW W memc)) a) G XO OUT STK sp0 FP ly S W0 mem0 md0 own
         lyc Sc W memc mdc k regs
         (fun ly2 S2 W2 regs2 mem2 md2 =>
            mo_le MT Sc S2 MO /\ LedPost Sc S2 /\
            PostA regs (rdW W memc) regs2 (rdW W2 mem2) (ablocks B lyc Sc) (ablocks B ly2 S2))).

Lemma aleaf_rdb_rd : forall pc K EV SIDE (Pre : bvmap 5 word -> (word -> option byte) -> Prop) Rd Wr Post,
  aleaf_rdb pc K EV SIDE (fun _ => Pre) Rd Wr Post <-> aleaf_rd SK segs rlo rhi B pc K EV SIDE Pre Rd Wr Post.
Proof. intros pc K EV SIDE Pre Rd Wr Post. unfold aleaf_rdb, aleaf_rd. split; intros H; exact H. Qed.

Lemma aleaf_alloc_rdb_rd : forall MT pc K EV LIVE MO SIDE CTX LedPre LedPost
    (Pre : bvmap 5 word -> (word -> option byte) -> Prop) Rd Wr PostA,
  aleaf_alloc_rdb MT pc K EV LIVE MO SIDE CTX LedPre LedPost (fun _ => Pre) Rd Wr PostA <->
  aleaf_alloc_rd SK segs rlo rhi B MT pc K EV LIVE MO SIDE CTX LedPre LedPost Pre Rd Wr PostA.
Proof.
  intros MT pc K EV LIVE MO SIDE CTX LedPre LedPost Pre Rd Wr PostA. unfold aleaf_alloc_rdb, aleaf_alloc_rd.
  split; intros H; exact H.
Qed.

(* SHAPE 1 at a returned FP state: aleaf_rdb with rounding mode 0 at the entry fx and the post apostF *)
Definition aleaf_fx (pc K EV : Z) (SIDE : list (Z * Z))
    (Pre : list (Z * Z) -> bvmap 5 word -> (word -> option byte) -> Prop)
    (Rd : bvmap 5 word -> (word -> option byte) -> Z -> Prop)
    (Wr : bvmap 5 word -> (word -> option byte) -> list (Z * Z))
    (Post : bvmap 5 word -> (word -> option byte) -> bvmap 5 word -> (word -> option byte) -> Prop) : Prop :=
  forall G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word),
    apre SK segs rlo rhi B K EV SIDE (Wr regs (rdW W memc)) G XO OUT STK sp0 FP ly S W0 mem0 md0 own
      lyc Sc W memc mdc k regs ->
    (forall a, Rd regs (rdW W memc) a -> akb segs B lyc Sc (spZ regs - K) (spZ regs) a) ->
    YK0o.frm_zero (@YK11.fp_csr fx) ->
    Pre (ablocks B lyc Sc) regs (rdW W memc) ->
    SRr segs W (cfg_at segs pc regs memc mdc)
      (apostF K EV (fun a => inFP (Wr regs (rdW W memc)) a) G XO OUT STK sp0 FP ly S W0 mem0 md0 own
         lyc Sc W memc mdc k regs
         (fun ly2 S2 W2 regs2 mem2 md2 =>
            S2 = set_fs (st_fs S2) Sc /\ Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\
            Post regs (rdW W memc) regs2 (rdW W2 mem2))).

(* SHAPE 2 at a returned FP state: aleaf_alloc_rdb with rounding mode 0 at the entry fx and the post apostF *)
Definition aleaf_alloc_fx (MT : ameter_ops) (pc K EV LIVE MO : Z) (SIDE : list (Z * Z)) (CTX : list (list Z))
    (LedPre : astate -> Prop) (LedPost : astate -> astate -> Prop)
    (Pre : list (Z * Z) -> bvmap 5 word -> (word -> option byte) -> Prop)
    (Rd : bvmap 5 word -> (word -> option byte) -> Z -> Prop)
    (Wr : bvmap 5 word -> (word -> option byte) -> list (Z * Z))
    (PostA : bvmap 5 word -> (word -> option byte) -> bvmap 5 word -> (word -> option byte) ->
             list (Z * Z) -> list (Z * Z) -> Prop) : Prop :=
  forall G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) ch,
    apre SK segs rlo rhi B K EV SIDE (Wr regs (rdW W memc)) G XO OUT STK sp0 FP ly S W0 mem0 md0 own
      lyc Sc W memc mdc k regs ->
    (forall a, Rd regs (rdW W memc) a -> akb segs B lyc Sc (spZ regs - K) (spZ regs) a) ->
    blocks_bytes Sc + LIVE <= LIVE_MAX -> mo_ok MT Sc MO ->
    achain lyc (aview segs (w_H W) memc) (spZ regs) (s0Z regs) ch -> In (raZ regs :: spine ch) CTX ->
    LedPre Sc ->
    YK0o.frm_zero (@YK11.fp_csr fx) ->
    Pre (ablocks B lyc Sc) regs (rdW W memc) ->
    SRr segs W (cfg_at segs pc regs memc mdc)
      (apostF K EV (fun a => inFP (Wr regs (rdW W memc)) a) G XO OUT STK sp0 FP ly S W0 mem0 md0 own
         lyc Sc W memc mdc k regs
         (fun ly2 S2 W2 regs2 mem2 md2 =>
            mo_le MT Sc S2 MO /\ LedPost Sc S2 /\
            PostA regs (rdW W memc) regs2 (rdW W2 mem2) (ablocks B lyc Sc) (ablocks B ly2 S2))).

(* a contract at a fixed fx gives its fx form (fx' := fx), so an fx-form caller applies it the same way *)
Lemma aleaf_fx_of_rdb : forall pc K EV SIDE Pre Rd Wr Post,
  aleaf_rdb pc K EV SIDE Pre Rd Wr Post -> aleaf_fx pc K EV SIDE Pre Rd Wr Post.
Proof.
  intros pc K EV SIDE Pre Rd Wr Post H. unfold aleaf_rdb, aleaf_fx in *.
  intros G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HA HR _ HP.
  eapply SRr_mono; [exact (H G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HA HR HP)|].
  intros W2 c2 _ HQ. apply apostF_of_apost. exact HQ.
Qed.

Lemma aleaf_alloc_fx_of_rdb : forall MT pc K EV LIVE MO SIDE CTX LedPre LedPost Pre Rd Wr PostA,
  aleaf_alloc_rdb MT pc K EV LIVE MO SIDE CTX LedPre LedPost Pre Rd Wr PostA ->
  aleaf_alloc_fx MT pc K EV LIVE MO SIDE CTX LedPre LedPost Pre Rd Wr PostA.
Proof.
  intros MT pc K EV LIVE MO SIDE CTX LedPre LedPost Pre Rd Wr PostA H. unfold aleaf_alloc_rdb, aleaf_alloc_fx in *.
  intros G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ch HA HR HL HM HC HX HD _ HP.
  eapply SRr_mono;
    [exact (H G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ch HA HR HL HM HC HX HD HP)|].
  intros W2 c2 _ HQ. apply apostF_of_apost. exact HQ.
Qed.

Lemma aleaf_fx_of_rd : forall pc K EV SIDE (Pre : bvmap 5 word -> (word -> option byte) -> Prop) Rd Wr Post,
  aleaf_rd SK segs rlo rhi B pc K EV SIDE Pre Rd Wr Post -> aleaf_fx pc K EV SIDE (fun _ => Pre) Rd Wr Post.
Proof.
  intros pc K EV SIDE Pre Rd Wr Post H. apply aleaf_fx_of_rdb. apply (proj2 (aleaf_rdb_rd pc K EV SIDE Pre Rd Wr Post)).
  exact H.
Qed.

Lemma aleaf_alloc_fx_of_rd : forall MT pc K EV LIVE MO SIDE CTX LedPre LedPost
    (Pre : bvmap 5 word -> (word -> option byte) -> Prop) Rd Wr PostA,
  aleaf_alloc_rd SK segs rlo rhi B MT pc K EV LIVE MO SIDE CTX LedPre LedPost Pre Rd Wr PostA ->
  aleaf_alloc_fx MT pc K EV LIVE MO SIDE CTX LedPre LedPost (fun _ => Pre) Rd Wr PostA.
Proof.
  intros MT pc K EV LIVE MO SIDE CTX LedPre LedPost Pre Rd Wr PostA H. apply aleaf_alloc_fx_of_rdb.
  apply (proj2 (aleaf_alloc_rdb_rd MT pc K EV LIVE MO SIDE CTX LedPre LedPost Pre Rd Wr PostA)). exact H.
Qed.

(* SHAPE 2 at a returned FP state, for a function that opens a FILE (mark_quietly's opening arm: fmemopen at 0x88410,
   the mark walk's gap E, accepted 2026-10-30): aleaf_alloc_fx with one more premise right after apre, that the
   caller's journal footprint is sink-open (`YI16.sink_open_fp FP`, i.e. it holds the token byte 0). fmemopen's post is
   a callee journal with footprint [sink_token]; composing it into the caller's journal (A/Prog/YC85G.v
   ajournal_sub_tok, A/Prog/PaJournalFs.v ajournal_gx_callee) asks that footprint to lie in the caller's FP, which
   `inFP FP 0` is (YC85G.v:54-57), and apre does not give. The harness journal's FP is the lib/A frame's
   `amf_harness_fp T` (A/AMemFileSink.v:231), sink-open by A/AMemFile.v `amf_harness_fp_sink_open` (cite it; no
   copy here). `aleaf_alloc_fx_sk_of_fx`: a contract proved without the premise is one with it. *)
Definition aleaf_alloc_fx_sk (MT : ameter_ops) (pc K EV LIVE MO : Z) (SIDE : list (Z * Z)) (CTX : list (list Z))
    (LedPre : astate -> Prop) (LedPost : astate -> astate -> Prop)
    (Pre : list (Z * Z) -> bvmap 5 word -> (word -> option byte) -> Prop)
    (Rd : bvmap 5 word -> (word -> option byte) -> Z -> Prop)
    (Wr : bvmap 5 word -> (word -> option byte) -> list (Z * Z))
    (PostA : bvmap 5 word -> (word -> option byte) -> bvmap 5 word -> (word -> option byte) ->
             list (Z * Z) -> list (Z * Z) -> Prop) : Prop :=
  forall G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) ch,
    apre SK segs rlo rhi B K EV SIDE (Wr regs (rdW W memc)) G XO OUT STK sp0 FP ly S W0 mem0 md0 own
      lyc Sc W memc mdc k regs ->
    YI16.sink_open_fp FP ->
    (forall a, Rd regs (rdW W memc) a -> akb segs B lyc Sc (spZ regs - K) (spZ regs) a) ->
    blocks_bytes Sc + LIVE <= LIVE_MAX -> mo_ok MT Sc MO ->
    achain lyc (aview segs (w_H W) memc) (spZ regs) (s0Z regs) ch -> In (raZ regs :: spine ch) CTX ->
    LedPre Sc ->
    YK0o.frm_zero (@YK11.fp_csr fx) ->
    Pre (ablocks B lyc Sc) regs (rdW W memc) ->
    SRr segs W (cfg_at segs pc regs memc mdc)
      (apostF K EV (fun a => inFP (Wr regs (rdW W memc)) a) G XO OUT STK sp0 FP ly S W0 mem0 md0 own
         lyc Sc W memc mdc k regs
         (fun ly2 S2 W2 regs2 mem2 md2 =>
            mo_le MT Sc S2 MO /\ LedPost Sc S2 /\
            PostA regs (rdW W memc) regs2 (rdW W2 mem2) (ablocks B lyc Sc) (ablocks B ly2 S2))).

Lemma aleaf_alloc_fx_sk_of_fx : forall MT pc K EV LIVE MO SIDE CTX LedPre LedPost Pre Rd Wr PostA,
  aleaf_alloc_fx MT pc K EV LIVE MO SIDE CTX LedPre LedPost Pre Rd Wr PostA ->
  aleaf_alloc_fx_sk MT pc K EV LIVE MO SIDE CTX LedPre LedPost Pre Rd Wr PostA.
Proof.
  intros MT pc K EV LIVE MO SIDE CTX LedPre LedPost Pre Rd Wr PostA H. unfold aleaf_alloc_fx, aleaf_alloc_fx_sk in *.
  intros G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ch HA _ HR HL HM HC HX HD HZ HP.
  exact (H G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ch HA HR HL HM HC HX HD HZ HP).
Qed.

End fxs.

(* The lift: the rest of a caller's walk, run at the fx1 a callee returned (fxr fx fx1), proves the caller's
   apostF at fx1; that is its apostF at its entry fx. Stated outside `fxs` because it names apostF at two FP
   states. *)
Section fxl. Context {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Variable segs : list Segment.
Variable B : asyms.

Lemma apostF_lift : forall (fx fx1 : YK11.FPState) K EV E G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc
    k regs Q W2 c2,
  @BoxBase.fxr fx fx1 ->
  apostF (fx := fx1) SK segs B K EV E G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Q W2 c2 ->
  apostF (fx := fx) SK segs B K EV E G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Q W2 c2.
Proof.
  intros fx fx1 K EV E G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Q W2 c2 H01 (fx2 & H12 & HP).
  exists fx2. split; [exact (fxr_trans fx fx1 fx2 H01 H12) | exact HP].
Qed.

Lemma srr_apostF_lift : forall (fx fx1 : YK11.FPState) K EV E G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W
    memc mdc k regs Q (Wc : world segs) (c : config),
  @BoxBase.fxr fx fx1 ->
  SRr segs Wc c (apostF (fx := fx1) SK segs B K EV E G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc
    k regs Q) ->
  SRr segs Wc c (apostF (fx := fx) SK segs B K EV E G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc
    k regs Q).
Proof.
  intros fx fx1 K EV E G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Q Wc c H01 H.
  eapply SRr_mono; [exact H|]. intros W2 c2 _ HP.
  exact (apostF_lift fx fx1 K EV E G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Q W2 c2 H01 HP).
Qed.

End fxl.

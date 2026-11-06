(* reac-pw/fuzz_segconf, ASan builds: the vocabulary that the ASan-level contracts of segconf's 34 program
   functions (lib/A/Prog/<F>_c.v) share. Statement text only: no function of the binary is proved here.

   IMAGE-INDEPENDENT: this file Requires no image module, and the contracts built on it take every image number
   (the entry, the stack a call needs, the read-only cells a function loads, a trampoline's pc) as a PARAMETER or
   a Section variable. segconf's two images do not share a listing: 30 of its 34 functions have a different size
   in fuzz_segconf.asan-ubsan than in fuzz_segconf.asan (provenance/evidence/image-tables/program.asan-ubsan.tsv), so every AF_<F>
   offset differs and a `Context {PI : PAImg seg_listing}` would fix one image. Each image's walk instantiates the
   parameters with its own measured values, as fuzz_qdisc's lib/A/QPgCSpec.v takes the divisor cell's address as
   the parameter `am`.

   THE FORM (plugin-hostd/fuzz_command's lib/A/Prog shape, its lib/A/Prog/number_c.v as the model; cgif
   lib/YC7x.v:72-167 and lib/YC21.v:33-88): a contract of function F is

     Definition <F>_contract (A_F STK_F : Z) : Prop :=
       forall ly S W (regs : bvmap 5 word) mem md ch <arguments>,
       afn_pre segs B STK_F ly S W regs mem md ch ->          (* the entry *)
       <arodata premise, argument registers, where each object lies, its shadow facts, SegModel premises> ->
       st_nev S + EV_F <= EV_MAX ->
       SRr segs W (cfg_at segs A_F regs mem md)
         (apost_base segs B STK_F <footprint> regs ly S W mem md EV_F
           (fun ly' S' W' regs' mem' md' => <functional post> /\ sa_noalloc B ly S ly' S')).

   - A_F is F's entry address and STK_F the bytes below the entry sp that F and its callees use (F's own frame,
     its realignment, and the deepest window a runtime entry it calls asks for). Both are parameters.
   - <footprint> is the list of byte ranges outside F's own stack window that F may write.
   - EV_F is the allocator events F spends: 0 for all 33 callees (only LLVMFuzzerTestOneInput allocates).
   - <functional post> is the plain lane's plain post (lib/Prog/<F>_c.v) in SegModel's terms, read through the exit
     reader `aview segs (w_H W') mem'` with this file's [sa_] encodings.
   - sa_noalloc is number_c.v's post tail for a call that reaches no allocator entry.
   - A function that reaches musl's printf states its post with apost_baseF (lib/A/Prog/SegPgBase.v), not
     apost_base: printf_core writes fa0 and the rounding mode.
   - The runtime entries F calls (astack_malloc_realizes for a fake-stack frame, stack_malloc_progressP,
     astack_free_law, frame_flag_lawP, one <x>_realizes per interceptor) are the WALK's Section hypotheses: the
     contract's body does not mention them, so they do not reach its statement. Each contract file names, in its
     head comment, the entries its walk must take, with the row of the interceptor lane's interface
     (provenance/evidence/interceptors/INTERFACE-A-interceptors.md (commit 7068323e2626)) that gives each text.

   THE ASAN FACTS a contract adds over the plain one, in this file's names:
   - [sa_addr rd q n]: [q, q + n) is addressable and its shadow bytes are mapped. Stated for every object F loads
     or stores through an inline check, and for every range F hands to an interceptor. Without it the check's
     error arm (a call of __asan_report_<kind>) is not excluded.
   - where an object lies: [sa_heap] (inside a live heap block), [sa_fframe] (inside a live side-stack frame),
     [sa_img] (an image byte the runtime does not own and that is not errno); [sa_loc] is the disjunction.
   - [sa_dst]: where a written destination may lie.
   - [sa_room]: room for one more side-stack frame (classes 0, 1, 3, 5 in segconf).
   - [sa_frm0], [sa_ssp]: what musl's printf_core, strstr, strspn and strtol read of the machine.
   - [sa_va_args]: refuse's variadic arguments.
   The contract fixes the plain lane's walks forced hold here too: counters are u32 (seg_spec.u32_enc), the role field
   is below 2^31 (seg_spec.role_enc), a %s argument is at most 65535 bytes and an int argument is 0 <= z < 2^31
   with the forbidden ranges named ([sa_va_arg]), a heap block is named by the allocator's live list and never by
   an address bound against the image's end, and a text is kept apart from the next block by its read span
   (seg_spec.cstr_span), not by length + 8.

   EVERY SIGNATURE BELOW IS WRITTEN OUT IN FULL: segs and B are explicit arguments wherever a body needs them, so
   a contract file writes exactly the arity it reads here. The three Contexts (fx, rc, SK) are implicit and are
   inferred at every use. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* ============================== bytes and strings through a reader ============================== *)
(* A state's memory is read by [aview segs (w_H W) mem] (lib/Reusable/YG0n.v): the byte as a Z in [0, 256), None
   where nothing is mapped. sa_bytes has the body of fuzz_command's abytes_atR (its lib/A/Rt/RtDefs.v), so those
   two convert by unfolding. A TEXT does NOT: sa_strz is over SegModel's list Z, while astr_atR / astr_at and the
   runtime rows' answers (ZS s) are over list byte, so unfolding alone does not take one to the other (corrected
   2026-10-30 after the interceptor lane's contract review, L1; an earlier version of this comment said it did). The glue is
   sa_strz_bytes, proved further down: from sa_strz over aview it gives astr_atR's body at seg_spec.zb l (the
   bytes and the NUL, no NUL among them) and seg_spec.zs (seg_spec.zb l) = l, so a walk that meets a runtime
   contract takes s := seg_spec.zb l and rewrites its answer back to the text. *)
Definition ZB0 : byte := Z_to_bv 8 0.
Definition sa_bytes (rd : reader) (a : Z) (bs : list byte) : Prop :=
forall i, (i < length bs)%nat -> rd (a + Z.of_nat i) = Some (bv_unsigned (nth i bs ZB0)).
Definition sa_zs (rd : reader) (a : Z) (l : list Z) : Prop :=
forall i, (i < length l)%nat -> rd (a + Z.of_nat i) = Some (nth i l 0).
Definition sa_val (rd : reader) (a : Z) (n : nat) (v : Z) : Prop :=
forall k, (k < n)%nat -> rd (a + Z.of_nat k) = Some (le_byte v n k).
(* the C string s at p: its bytes and its NUL, what strcmp and the byte loops read (seg_spec.cstrz_at) *)
Definition sa_strz (rd : reader) (p : Z) (s : list Z) : Prop :=
sa_zs rd p (s ++ [0]) /\ ~ In 0 s.
(* the bytes after the NUL at e up to the next 8-byte boundary are mapped: what the word-at-a-time musl readers
   behind the strlen / strchr / strrchr / memchr / strnlen interceptors touch (seg_spec.cstr_at's slack) *)
Definition sa_tail (rd : reader) (e : Z) : Prop :=
forall x, e < x < e - e mod 8 + 8 -> rd x <> None.
Definition sa_str (rd : reader) (p : Z) (s : list Z) : Prop :=
sa_strz rd p s /\ sa_tail rd (p + Z.of_nat (length s)).
Definition sa_ostr (rd : reader) (p : Z) (o : option (list Z)) : Prop :=
match o with None => p = 0 | Some s => p <> 0 /\ sa_str rd p s end.
Definition sa_ostrz (rd : reader) (p : Z) (o : option (list Z)) : Prop :=
match o with None => p = 0 | Some s => p <> 0 /\ sa_strz rd p s end.

(* ============================== the text glue: list Z against list byte ============================== *)
(* The runtime rows state a string as a list byte s (fuzz_command's astr_at / astr_atR, RtDefs.v:61-62 and :72-73,
   and the rows' answers over ZS s), segconf's contracts as SegModel's list Z. These three lemmas take one to the
   other at the ASan reader, where every byte read is bv_unsigned of a byte and so in [0, 256) (the interceptor lane's
   contract review, L1). sa_strz_bytes gives astr_atR's BODY at seg_spec.zb l - sa_bytes is abytes_atR's body, and
   ZB0 is the literal Z_to_bv 8 0 those definitions use - together with seg_spec.zs (seg_spec.zb l) = l, so a walk
   instantiates a row with s := seg_spec.zb l and rewrites its answer back to the text. *)
Lemma sa_aview_rng : forall segs H mem a v, aview segs H mem a = Some v -> 0 <= v < 256.
Proof.
intros segs H mem a v E. unfold aview in E.
destruct (mbyte segs (mrestrict H mem) a) as [b|]; cbn in E; [|discriminate].
inversion E; subst. pose proof (bv_unsigned_in_range _ b) as R. change (bv_modulus 8) with 256 in R. lia.
Qed.
Lemma sa_zs_zb : forall l, Forall (fun z => 0 <= z < 256) l -> seg_spec.zs (seg_spec.zb l) = l.
Proof.
induction 1 as [|z l Hz Hl IH]; [reflexivity|].
unfold seg_spec.zs, seg_spec.zb in *. cbn. f_equal; [|exact IH].
rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 8) with 256. lia.
Qed.
Lemma sa_strz_bytes : forall segs H mem p l, sa_strz (aview segs H mem) p l ->
sa_bytes (aview segs H mem) p (seg_spec.zb l ++ [ZB0]) /\ ~ In ZB0 (seg_spec.zb l) /\
seg_spec.zs (seg_spec.zb l) = l.
Proof.
intros segs H mem p l [Hzs Hn0].
assert (HF : Forall (fun z => 0 <= z < 256) l).
{ apply Forall_forall. intros z Iz. destruct (In_nth l z 0 Iz) as [i [Hi Hn]].
  assert (Hi' : (i < length (l ++ [0%Z]))%nat) by (rewrite length_app; cbn; lia).
  pose proof (Hzs i Hi') as E. rewrite app_nth1 in E by exact Hi. rewrite Hn in E.
  exact (sa_aview_rng _ _ _ _ _ E). }
split; [|split].
- intros i Hi.
  assert (Eapp : seg_spec.zb l ++ [ZB0] = seg_spec.zb (l ++ [0]))
    by (unfold seg_spec.zb; rewrite map_app; reflexivity).
  rewrite Eapp in Hi |- *. unfold seg_spec.zb in Hi |- *. rewrite length_map in Hi.
  unfold ZB0. rewrite (map_nth (Z_to_bv 8) (l ++ [0]) 0 i).
  pose proof (Hzs i Hi) as E. rewrite E. f_equal.
  pose proof (sa_aview_rng _ _ _ _ _ E) as R.
  rewrite Z_to_bv_unsigned. symmetry. apply bv_wrap_small. change (bv_modulus 8) with 256. lia.
- unfold seg_spec.zb. intros Hin. apply in_map_iff in Hin. destruct Hin as [z [Ez Iz]].
  apply Hn0. replace 0 with z; [exact Iz|].
  rewrite Forall_forall in HF. pose proof (HF z Iz) as Rz.
  apply (f_equal bv_unsigned) in Ez. unfold ZB0 in Ez. rewrite !Z_to_bv_unsigned in Ez.
  rewrite (bv_wrap_small _ z) in Ez by (change (bv_modulus 8) with 256; lia).
  rewrite (bv_wrap_small _ 0) in Ez by (change (bv_modulus 8) with 256; lia).
  exact Ez.
- exact (sa_zs_zb l HF).
Qed.

(* ============================== segconf's objects through a reader ============================== *)
(* seg_spec's [_at] forms with the reader in place of the plain build's memory. The encodings themselves
   (seg_spec.rconf_enc, mconf_encp, mseg_enc, rseg_enc, rtab_enc, mtab_enc) are used as they are, so a post here
   is the plain post's Gallina. *)
Definition sa_rconf (rd : reader) (c : Z) (rc : SegModel.rconf) : Prop :=
exists bs, sa_bytes rd c bs /\ seg_spec.rconf_enc rc bs.
Definition sa_rseg (rd : reader) (a : Z) (s : SegModel.rseg) : Prop :=
exists bs, sa_bytes rd a bs /\ seg_spec.rseg_enc s bs.
Definition sa_mconfp (pend : bool) (rd : reader) (a : Z) (mc : SegModel.mconf) : Prop :=
exists bs, sa_bytes rd a bs /\ seg_spec.mconf_encp pend mc bs.
Definition sa_mconf (rd : reader) (a : Z) (mc : SegModel.mconf) : Prop := sa_mconfp false rd a mc.
Definition sa_mseg (rd : reader) (a : Z) (g : SegModel.mseg) : Prop :=
exists bs, sa_bytes rd a bs /\ seg_spec.mseg_enc g bs.
Definition sa_rtab (rd : reader) (a : Z) (t : list (list Z * Z)) : Prop :=
exists bs, sa_bytes rd a bs /\ seg_spec.rtab_enc t bs.
Definition sa_mtab (rd : reader) (a : Z) (t : list (list Z * Z)) : Prop :=
exists bs, sa_bytes rd a bs /\ seg_spec.mtab_enc t bs.
(* the guard entry tab[cap] the harness fills with 0x5a (seg_spec.guard_at) *)
Definition sa_guardtab (rd : reader) (tab cap : Z) : Prop :=
sa_bytes rd (tab + seg_spec.RVLAN_SIZE * cap) seg_spec.GUARD_BYTES.

(* ======================================= the shadow facts ======================================= *)
(* [q, q + n) is addressable and its shadow bytes are mapped: an inline check of a byte of it passes, and so does
   an interceptor's range check (cgif's src_ok / dest_ok shadow part, lib/Reusable/YG0d.v:311-343; the same
   conjuncts as fuzz_command's aread_ok, its lib/A/Rt/RtDefs.v) *)
Definition sa_addr (rd : reader) (q n : Z) : Prop :=
0 <= q /\ q + n <= 2 ^ 63 /\ amem_range q n /\
range_addressable rd SHADOW_OFF q n /\ (0 < n -> shadow_hull_vis rd q n).
(* [p, p + n) and [q, q + m) do not meet *)
Definition sa_disj (p n q m : Z) : Prop := p + n <= q \/ q + m <= p.
(* the n bytes at a are apart from every range of Wl (seg_spec.apart_all) *)
Definition sa_apart_all (a n : Z) (Wl : list (Z * Z)) : Prop :=
Forall (fun iv => a + n <= fst iv \/ snd iv <= a) Wl.
(* the stack-protector cells musl reads in printf_core, strstr, strspn and strtol: the GOT word gotw holds the
   guard object's address, and the guard is a mapped word (seg_env.ssp_ok; fuzz_command's aguard_ok). Both
   addresses are image numbers, so each contract takes them as parameters. *)
Definition sa_ssp (rd : reader) (gotw guard : Z) : Prop :=
rdword rd gotw = Some guard /\ exists g, rdword rd guard = Some g.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

(* the rounding mode musl's printf_core needs: fcsr's frm field (bits 5..7) is 0 (seg_env.frm0; fuzz_command's
   frm0_entry). Stated in the contract of every function that reaches a printf wrapper. *)
Definition sa_frm0 : Prop := Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0.

(* ======================================= where objects lie ======================================= *)
(* inside one live heap block of the state (fuzz_command's in_blockA) *)
Definition sa_heap (B : asyms) (ly : alayout) (S : astate) (q n : Z) : Prop :=
exists b m, In (b, m) (ablocks B ly S) /\ b <= q /\ q + n <= b + m.
(* inside one live side-stack frame of the state (identity's tdst_ok, its frame case) *)
Definition sa_fframe (ly : alayout) (S : astate) (q n : Z) : Prop :=
exists cid pos, In (cid, pos) (frames S) /\ 0 <= cid /\
frame_addr ly cid pos <= q /\ q + n <= frame_addr ly cid pos + fs_frame_bytes cid.
(* image bytes the runtime does not own and that are not errno: the program's .rodata, .data.rel.ro and its
   registered globals *)
Definition sa_img (segs : list Segment) (B : asyms) (q n : Z) : Prop :=
forall x, q <= x < q + n ->
in_img segs x /\ ~ Exists (in_zr x) (as_owned_static B) /\ ~ (as_errno B <= x < as_errno B + 4).
(* the three places an object of segconf's code lies *)
Definition sa_loc (segs : list Segment) (B : asyms) (ly : alayout) (S : astate) (q n : Z) : Prop :=
sa_heap B ly S q n \/ sa_fframe ly S q n \/ sa_img segs B q n.
(* where a destination the call writes may lie: a side-stack frame or a heap block (each with its shadow
   addressable), or a slot of the caller's real stack above the entry sp and below the layout's top, present
   (fuzz_command's lib/A/Prog/number_c.v states its `out` in the frame and real-stack arms).
   THE LAST CONJUNCT OF THE REAL-STACK ARM, and why the arm is unusable without it (found by the G4 / G5 walk lane's
   walks, 2026-10-30, on reac_segconf_role's `out` and reac_declared_vlan_split's `vid`; it is a
   property of the arm, not of those two functions, so it is fixed here once). A caller keeps such a pointer in
   s0 across a call -- role 0x89600 `mv s0,a2` across `jal reac_segconf_find` 0x89610, split 0x89bcc
   `mv s0,a3` across `jal name_ok` 0x89d08 -- and the callee's afn_pre asks `achain ly rd sp s0 ch`
   (lib/Reusable/YCbq.v:264), whose chain needs the words at s0 - 8 and s0 - 16 (YG00.v:370-372). The frame and
   heap arms give it for nothing: those addresses are below alloc_ceiling, so achain_low (YCbq.v:225) applies.
   The real-stack arm does not: it made only [d, d + n) present, and AR gives nothing above sp. With
   astack_pres the walk takes achain_any with astack_rd_of_pres (YCbq.v:401, :939).
   Every caller can supply it: the only real-stack destination in segconf is the harness's own cell passed to
   reac_segconf_role, and LLVMFuzzerTestOneInput has astack_pres at its entry
   (lib/A/Prog/LLVMFuzzerTestOneInput_c.v:136) and keeps it across a call by astack_pres_journal (YCbq.v:941);
   check_absent passes out = 0; every other destination of every other contract (trim's p, name_ok's s,
   reac_box_catalogue's c, reac_declared_vlan_add's count cell, split's parent and vid at their real call site)
   is a side-stack frame slot and takes the frame arm. The conjunct also implies the presence of [d, d + n),
   which is kept beside it in the donor's shape. *)
Definition sa_dst (segs : list Segment) (B : asyms) (ly : alayout) (S : astate) (W : world segs)
(mem : word -> option byte) (regs : bvmap 5 word) (d n : Z) : Prop :=
(sa_fframe ly S d n /\ range_addressable (aview segs (w_H W) mem) SHADOW_OFF d n) \/
(sa_heap B ly S d n /\ range_addressable (aview segs (w_H W) mem) SHADOW_OFF d n) \/
(spZ regs <= d /\ d + n <= ly_top ly /\ (forall i, 0 <= i < n -> apresent (w_H W) mem (d + i)) /\
 astack_pres ly (w_H W) mem (spZ regs)).
(* What a call keeps BESIDES what the journal keeps: every byte outside its own stack window and outside the
   byte set E it may write. apost_base's ajournal keeps only four classes -- bytes at or above alloc_ceiling
   outside [sp0 - STK, sp0), the live blocks, the image bytes the runtime does not own, and the side-stack
   frames of the entry state with their shadow -- and the SHADOW of an image object is in none of them: a
   shadow address is below alloc_ceiling and is not in_img. So a caller that holds `sa_addr rd name n` or
   `sa_tail rd e` of a .rodata string, and calls twice, cannot carry those facts past the first call. Found by
   the G4 / G5 walk lane's walk of check_absent, which calls reac_segconf_find, _role, _ignored and _model one
   after the other with the harness's image name "nosuch0" (passed at 0x857a4) and must re-give query_pre at
   each. The wording is fuzz_command's art_post keep clause (its lib/A/Rt/RtDefs.v), with the window and the
   write set as parameters.
   A contract may state this only where it is TRUE of the code: a function that takes a side-stack frame also
   writes that frame and its shadow, which lie outside both the window and the footprint, so for those the
   clause is stated over the smaller set each of them names, or not at all. *)
Definition sa_kept (segs : list Segment) (W : world segs) (mem : word -> option byte)
(W' : world segs) (mem' : word -> option byte) (regs : bvmap 5 word) (STK : Z) (E : Z -> Prop) : Prop :=
forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - STK <= a < spZ regs) -> ~ E a ->
aview segs (w_H W') mem' a = aview segs (w_H W) mem a.
(* room for one more side-stack frame: segconf nests at most LLVMFuzzerTestOneInput (class 3) ->
   reac_segconf_parse_file (class 5) -> refuse (class 0), with m_file (class 1) and reac_segconf_declared
   (class 1) beside them (provenance/evidence/image-tables/program.asan.tsv) *)
Definition sa_room (S : astate) : Prop := Z.of_nat (length (frames S)) <= 8.
(* Room for n side-stack frames taken one inside the other: the call's own and those of the callees it is
   inside at the time. segconf nests three deep: LLVMFuzzerTestOneInput (class 3) -> reac_segconf_parse_file
   (class 5) -> refuse (class 0), so the harness needs 3, parse_file 2 and refuse 1
   (provenance/evidence/image-tables/program.asan.tsv). sa_room S is the n = 1 bound, written out: `length (frames S) <= 8` and
   `length (frames S) + 1 <= 9` are the same bound, and either shape is discharged by lia. A callee's contract
   asks its own n at ITS entry, where the caller's frames are already there; that is why one Prop does not
   serve a nest. Found by a contracts check, 2026-10-30. *)
Definition sa_room_n (n : Z) (S : astate) : Prop := Z.of_nat (length (frames S)) + n <= 9.

(* ============================ band room past a string, from where it lies ============================ *)
(* The printf rows' family ends with cmd_args_amem (fuzz_command lib/A/Rt/RtPFCmd.v:82-87, taken by the interceptor lane's
   FR_seg, RtPFSeg.v:160-168): each %s / %.24s argument w of a string s needs amem_range w (|s| + 8), the
   arithmetic application-range predicate (lib/Reusable/YG0d.v:325), which sa_addr gives only over |s| + 1. It
   needs no premise: it follows from where every contract already places the string (a G3 walk lane
   raised it as STOP #5 and withdrew it after checking image A; image B's G3 walk lane found the same). A live
   heap block (AR_blocks_law, YG0d.v:431-434) and a live side-stack frame (AR_frames_law, :455-458) are in_app
   (YG0f.v:282), whose low arm ends at kLowShadowBeg = 0x7fff7000 while amem_range's ends at
   kLowMemEnd - 1 = 0x7fff7fff (YG0f.v:18, :21), 4,095 bytes further, and whose high arm ends at
   ASAN_CEIL <= 0x7fffff800000 (YG0f.v:16), far below kHighMemEnd - 1: a3_amem_slack. An image string ends at or
   below kImgEnd = 0x601000 (YG0f.v:19): a3_amem_img. A literal's address is a number the walk computes with.
   a3_amem_slack is the G3 walk lane's general step (its pf_a3.v), stated as that lane states it; the proof here is
   this lane's own text. *)
Lemma a3_amem_slack : forall lo len p k, in_app lo len -> lo <= p -> 0 <= k -> p + k <= lo + len + 4095 ->
amem_range p k.
Proof.
intros lo len p k [H0 H] H1 H2 H3. pose proof (@ASAN_CEIL_range rc) as [[C1 C2] _].
unfold amem_range, kLowShadowBeg, kLowMemEnd, kHighMemBeg, kHighMemEnd in *.
destruct H as [H|[H4 H5]]; [left; lia | right; split; lia].
Qed.
Lemma a3_amem_img : forall p k, p + k <= kImgEnd -> 4096 <= p -> amem_range p k.
Proof. intros p k H1 H2. unfold amem_range, kImgEnd, kLowMemEnd in *. left. lia. Qed.

(* ================================ the image's own strings and table ================================ *)
(* An image object whose shadow is addressable at EVERY allocator state, not only at the call. This is what an
   image literal or the catalogue table needs, because no fact KEEPS an image object's shadow across a
   side-stack frame: the kit's astack_malloc_realizes (lib/Reusable/YG0d.v:293-308) keeps a byte only outside
   aowned at its entry and its exit, and aowned (YG0n.v:236-242) holds the shadow of lm_zone = [0, kLowMemEnd)
   minus the client bytes, which is the shadow of every image byte. So refuse, which calls
   __asan_stack_malloc_0 at 0x88e30 before its snprintf calls read its format literals, and
   reac_segconf_parse_file, which calls __asan_stack_malloc_5 at 0x87af0 before its first literal read, could
   not use an entry-state sa_addr of a literal inside their own walks, and no caller of a function with a
   side-stack frame could carry one across the call. The allocator record pins such shadow at every AR state
   (its zero-shadow ranges and its constant cells), and the stack_malloc post and the journal both give AR at
   the new state, so a walk re-derives the shadow wherever it needs it. This is fuzz_command's own route, its
   lib/A/Prog/CmdRecBase.v cmd_addressable_chk / cmd_hull_vis_chk / cmd_aread_ok_chk at 501c0d516c69, which
   each image discharges by a boolean check over its record. Found by a contracts check, 2026-10-30; accepted by
   the image-A owner. The per-image obligation (each literal and the table sa_pinned, from segconf's generated record)
   belongs to the listing's stage 2 (SegRecBase, the CmdRecBase analogue). *)
Definition sa_pinned (segs : list Segment) (B : asyms) (q n : Z) : Prop :=
forall ly S (W : world segs) mem md, AR segs B ly S W mem md -> sa_addr (aview segs (w_H W) mem) q n.
(* The slack after a literal's NUL is NOT kept by the journal either: it lies in the global's right redzone
   (image A: .str at 0x21340 has size 3 and a 29-byte redzone, provenance/evidence/image-tables/asan_globals.asan.tsv line 27), a
   redzone's shadow is not zero, so the record can pin it only as a constant cell, and am_const_owned
   (lib/Reusable/YG0n.v:212, :201-202) then makes the redzone an owned static, which the journal's image clause
   (YCbq.v:479-480) does not keep. fuzz_command's record shows the same (its lib/A/AF0m.v:5208 lists the redzone
   after its 3-byte global). But an image byte is mapped at EVERY reader, with no AR at all: aview is mbyte over
   mrestrict, and mbyte falls back to the segment's byte (fuzz_command's CmdRecBase.v:367 crf_rom_view_some, used
   for literal tails in its CmdRecRo.v:95 cmd_tail_vis_at). So a literal's tail is stated as a pure image fact,
   sa_romtail, discharged per image by a computation over segs, and sa_tail_of_romtail below gives the reader form
   at any state. THIS HOLDS FOR THE .bss LABEL longl TOO (corrected 2026-10-30; an earlier version of this comment
   said longl's slack was not ROM and needed the AR-pinned form): seg_rom is LPS's memory_read, which reads any
   readable segment, and the rw .bss segment is in segs (LPS RiscvSemantics.v:397-405, pointed out by the plain lane's
   review and agreed by the image-A owner), so longl's slack 0x5de6f9..0x5de6ff (image A) has a seg_rom byte.
   sa_pinned_tail, the AR-pinned form, stays as what a callee asks of a label's tail; sa_pinned_tail_of_romtail
   below gives it from sa_romtail at once. Found by a contracts check, 2026-10-30. *)
Definition sa_romtail (segs : list Segment) (e : Z) : Prop :=
forall x, e < x < e - e mod 8 + 8 -> seg_rom segs (Z_to_bv 64 x) <> None.
Definition sa_pinned_tail (segs : list Segment) (B : asyms) (e : Z) : Prop :=
forall ly S (W : world segs) mem md, AR segs B ly S W mem md -> sa_tail (aview segs (w_H W) mem) e.
Lemma sa_tail_of_romtail : forall segs H mem e, sa_romtail segs e -> sa_tail (aview segs H mem) e.
Proof.
intros segs H mem e HR x Hx. specialize (HR x Hx). unfold aview, mbyte.
destruct (mrestrict H mem (Z_to_bv 64 x)) as [b|]; [discriminate|].
destruct (seg_rom segs (Z_to_bv 64 x)) as [b|] eqn:E; [discriminate|].
intros _. first [exact (HR E) | exact (HR eq_refl)].
Qed.
Lemma sa_pinned_tail_of_romtail : forall segs B e, sa_romtail segs e -> sa_pinned_tail segs B e.
Proof. intros segs B e HR ly S W mem md _. exact (sa_tail_of_romtail segs (w_H W) mem e HR). Qed.
(* A .rodata literal the code passes to an interceptor: the C string s at a with its slack, its bytes and NUL
   addressable at every allocator state (sa_pinned), its slack mapped at every state (sa_romtail), and every
   byte an image byte the runtime does not own. segconf's code passes 41 of them (reac_segconf.c's .str ..
   .str.42 at image A 0x21340..0x21be0, and the formats of fuzz_segconf.c). A contract does not name an
   address: it takes a function `lit : list Z -> Z` from a literal's text to its address and asks
   `forall s, In s <F>_LITS -> sa_lit segs B rd (lit s) s`, with <F>_LITS the SegModel texts of that function.
   Each image's walk gives its own lit. The address is positive: the string interceptors' released contracts
   ask it (fuzz_command lib/A/Rt/RtString.v astrlen_realizes and astrcmp_realizes, the interceptor lane's rows 16 and 17,
   take `0 < x`), and no kit fact gives a lower bound for an image address - the walk hypothesis segs_low gives
   only `in_img segs a -> 0 <= a`. Found by a contracts check, 2026-10-30. *)
Definition sa_lit (segs : list Segment) (B : asyms) (rd : reader) (a : Z) (s : list Z) : Prop :=
0 < a /\ sa_str rd a s /\ sa_pinned segs B a (Z.of_nat (length s) + 1) /\
sa_romtail segs (a + Z.of_nat (length s)) /\ sa_img segs B a (Z.of_nat (length s) + 1).
(* The box-model table `fuzz_catalogue` (catalogue.c; image A 0xa18e0, 3256 bytes in .data.rel.ro, 11 rows of
   0x128 bytes) as the code reads it: the table addressable at every allocator state (sa_pinned) and an image
   object, and row i's token pointer a word of the image that points at token i's bytes. The token BYTES are
   image-independent (pin_spec.tok_bytes, tied to SegModel.cat_toks by seg_spec.cat_toks_bytes); the token
   POINTERS of pin_spec.rows are the plain and UBSan images' values and are NOT used here - the pointer is read
   from the image's own word and bound existentially, so both ASan images satisfy the same text. *)
Definition sa_cat (segs : list Segment) (B : asyms) (rd : reader) (cat : Z) : Prop :=
sa_pinned segs B cat pin_spec.CAT_BYTES /\ sa_img segs B cat pin_spec.CAT_BYTES /\
forall i, (i < pin_spec.CAT_N)%nat ->
exists tp, rdword rd (pin_spec.row_addr cat i) = Some tp /\
sa_lit segs B rd tp (seg_spec.zs (pin_spec.tok_bytes i)).

(* ===================================== refuse's variadic arguments ===================================== *)
(* seg_spec.va_arg_ok over the reader, with the shadow facts ASan's printf_common checks of a %s argument (its
   bytes and NUL, which internal_strnlen measures) and with the read span cstr_span in place of length + 8. *)
Definition sa_va_arg (rd : reader) (Wl : list (Z * Z)) (r : word) (x : SegModel.arg) : Prop :=
match x with
| SegModel.AS s =>
    bv_unsigned r <> 0 /\ sa_str rd (bv_unsigned r) s /\ (length s <= 65535)%nat /\
    sa_addr rd (bv_unsigned r) (Z.of_nat (length s) + 1) /\
    sa_apart_all (bv_unsigned r) (seg_spec.cstr_span (bv_unsigned r) s) Wl
| SegModel.AI z => 0 <= z < 2 ^ 31 /\ bv_unsigned r = z
end.
Fixpoint sa_va_args (rd : reader) (Wl : list (Z * Z)) (rs : list word) (xs : list SegModel.arg) : Prop :=
match xs, rs with
| [], _ => True
| x :: xs', r :: rs' => sa_va_arg rd Wl r x /\ sa_va_args rd Wl rs' xs'
| _ :: _, [] => False
end.

(* ==================================== the post tail of a call ==================================== *)
(* A call that reaches no allocator entry: the live blocks are a permutation of the entry's, the layout is kept,
   and the only state change is the side-stack frame it takes and releases (fuzz_command's
   lib/A/Prog/number_c.v post, its meter class (b)). Every one of segconf's 33 non-harness functions is of this
   kind; LLVMFuzzerTestOneInput, which allocates, states its own block clauses. *)
Definition sa_noalloc (B : asyms) (ly : alayout) (S : astate) (ly' : alayout) (S' : astate) : Prop :=
Permutation (ablocks B ly' S') (ablocks B ly S) /\ ly' = ly /\ (exists f, S' = set_fs f S).
End b.

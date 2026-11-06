(* Cut invariants of fuzz_ctrl LLVMFuzzerTestOneInput, asan-ubsan build of libreac v1.9.0 (binary sha256 ee07e2c3...),
   entry function [0x81018, 0x83114) (slot-plan-asan.md section 3). The image-B twin of lib/A/Prog/SlotInv.v:
   frame_facts (the non-obligation conjuncts of FrameAPI.frame_asan), the ghost values fixed at ENTRY, the
   frame-and-shadow invariant FRA (the 3136-byte side-stack frame, s3 = S(fr), the 392 shadow bytes of FP.4), the
   per-cut invariants Inv_B<addr> of plan section 3, Hcut/Hat/Hat2, and the slot goal. Addresses in this file are
   the v1.9.0 binary's unless marked "patched" (the libreac-patched image this file was first written for; the
   v1.9.0 re-derivation is v190-B-cuts.md (a working note, not in this delivery)). *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Step Cells.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcModel RcRec RcParse RcReply RcIdentModel RcFrag RcLeaf
  RcPorts RcDecl RcClassify RcKind RcMatch.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcBox RcSynth reac_ctrl_build_as_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require RcAsanFP reac_ctrl_build_as_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Contract FrameAPI AsanLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import SlotModel.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require reac_ctrl_kind_name_c bcmp_wrap_c
  asan_stack_malloc_c asan_memset_c reac_ctrl_parse_c reac_ctrl_identity_reply_c reac_ctrl_identity_fragment_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Spec Require StrFun.
From OSSVerify.libreac.fuzz_ctrl Require Statements.
(* Generation N.1's class accounting (lib/B/ClassConsDef.v a_class_bytes) and the allocator's class table
   (lib/AZ/Spec/AsanCtrl.v K_NUM_CLASSES, size_of_class), for ENT's per-class conjunct. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require ClassConsDef.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.AZ.Spec Require AsanCtrl.
Import ListNotations.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.FrameAPI.
(* The callee contracts' constants read by the F7 / F8 (reac_ctrl_kind_name) and F18 (wrapper_bcmp) cuts. *)
Module KNC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.reac_ctrl_kind_name_c.
Module BW := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.bcmp_wrap_c.
Module SF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Spec.StrFun.
(* rw_cells / CB of the identity_reply post carried by the F10 reply cells (lib/B/Prog/Seg/F10.v); then the
   reac_ctrl_build_as call at the round-trip loop head (R6X): the plain contract's row table, the image-B
   contract's frame constants and side-stack state, the row accessors, name_ok and the frame package. *)
Module BAP := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.reac_ctrl_build_as_c.
Module BAC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.reac_ctrl_build_as_c.
Module RS6 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcSynth.
Module RBx := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcBox.
Module FP := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.RcAsanFP.
Module LSt := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Step.
Module LCl := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Cells.
(* The stack-allocation contract's FakeStack layout, read by FSREC (push 5b). *)
Module SMC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.asan_stack_malloc_c.
(* The identity_fragment contract's stack depth K and its post memory fg_mem, read by the F13 / F14 cuts. *)
Module RIFC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.reac_ctrl_identity_fragment_c.

(* The ASan frame of LLVMFuzzerTestOneInput (v1.9.0, image B): FRAME_BYTES bytes from fr, FRAME_SHADOW shadow bytes
   from S(fr). 0x81084 / 0x81088 `lui a0,1; addiw a0,a0,-960` (the frame_alloc_6 request) and 0x82f3c / 0x82f40
   (`addiw a1,a0,-960`, the frame_release_6 size) give 4096 - 960 = 3136, 0x82f50 `li a1,392` the meta_fill_00
   length. Every frame-size occurrence below is written through these names (as lib/A/Prog/SlotInv.v);
   FRAME_BYTES_val / FRAME_SHADOW_val give lia the numerals. *)
Definition FRAME_BYTES : Z := 3136.
Definition FRAME_SHADOW : Z := FRAME_BYTES / 8.
Lemma FRAME_BYTES_val : FRAME_BYTES = 3136.
Proof. reflexivity. Qed.
Lemma FRAME_SHADOW_val : FRAME_SHADOW = 392.
Proof. reflexivity. Qed.

(* frame_asan_ubsan (B/FrameAPI.v:147) without its last conjunct (the slot obligation yielding asan_ubsan_halts); the
   conjunct itself is slot_obligation. frame batch 2 (a Theorem Labs lane 48004cf7bfc) added the sink-env bound (FrameAPI.v:156,
   after `0 < empty < 2 ^ 62`); frame_facts carries it LAST, so the v1.8 positions of frame_facts are kept. *)
Definition frame_facts (B : malloc_syms) (APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT)
    (LS : lib_shape) (SH : sink_head) (SK : sink_syms) (ra empty : Z) : Prop :=
  ms_segs B = rsegs /\ ra mod 2 = 0 /\
  ms_tp B = AC.as_tp AC.ASYMS /\ ms_errno_off B = -164 /\
  @sk_ofl_head SH = 0x5fcd48 /\ @sk_ofl_lock SK = 0x5fcd40 /\ @sk_threaded SK = 0x5fc8e0 + 1 /\
  empty = 0x5dbd20 /\ 0 < empty < 2 ^ 62 /\
  (forall a, in_globals AF.frame_G a -> AC.a_in_img a) /\
  (forall a, in_globals AF.frame_RELRO a -> AC.a_in_img a) /\
  (forall rc H mem md a, AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) H mem md a ->
     ~ in_globals AF.frame_G a /\ ~ in_globals AF.frame_RELRO a) /\
  (forall pl fs K, @LIBK LS pl fs K = K (LL 0 fs [])) /\
  (forall a, @YI14.env_addr SH SK a -> 0 <= a < AC.GT).

Definition slot_obligation (B : malloc_syms) (APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT)
    (LS : lib_shape) (SH : sink_head) (SK : sink_syms) (ra empty : Z) : Prop :=
  forall (G : list (Z * Z)) (GI : nat -> list (Z * Z) -> (word -> option byte) -> Prop),
    (forall a, in_globals G a -> in_globals AF.frame_G a) ->
    AF.G_local_t B G GI ->
    (forall mem, G_img_c B G mem -> GI 0%nat [] mem) ->
    AF.TB_bound GI ->
    (forall (rc : RunCeil) (fx : FPState) (j : nat), (j < 4)%nat ->
       @AF.alib_contract fx LS B AsanRTInv.RT (APIf rc) SH SK G AF.frame_RELRO GI j AF.ENTRY ra empty AF.SLOT_STACK) ->
    Statements.asan_ubsan_halts.

Lemma frame_asan_split : AF.frame_asan_ubsan -> exists B APIf LS SH SK ra empty,
  frame_facts B APIf LS SH SK ra empty /\ slot_obligation B APIf LS SH SK ra empty.
Proof.
  intros (B & AA & LS & SH & SK & ra & empty & Hsegs & Hra & Htp & Herrno & Hofl & Hlock & Hthr & Hempty & Hemptyr &
    Henv & HG & HRELRO & Howned & HLIBK & Hslot).
  exists B, AA, LS, SH, SK, ra, empty. split; [| exact Hslot].
  unfold frame_facts.
  exact (conj Hsegs (conj Hra (conj Htp (conj Herrno (conj Hofl (conj Hlock (conj Hthr (conj Hempty (conj Hemptyr
    (conj HG (conj HRELRO (conj Howned (conj HLIBK Henv))))))))))))).
Qed.

(* Ghost values fixed at ENTRY: the input bytes (n = length), p, the entry sp S, the entry registers, memory and
   model, the live heap H (the input block plus the target's kept blocks) and the kept-block list T. *)
Record ghost := Ghost {
  g_in : list byte;
  g_p : Z;
  g_S : Z;
  g_regs : bvmap 5 word;
  g_mem : word -> option byte;
  g_md : Model;
  g_H : list (Z * Z);
  g_T : list (Z * Z)
}.
Definition g_n (g : ghost) : Z := nlen (g_in g).

(* ==== The generated allocator laws (lib/B/Contract.v) this bundle takes apart, each destructed ONCE here, by
   statement (a Theorem Labs lane 15:18Z / 15:32Z: a generated conjunction is never destructed by position at a use; one local
   lemma per law). Each lemma matches its record's fields to the law's conjuncts by `eassumption` (after decompose),
   so a conjunct a later generation adds or moves changes neither the lemma nor its users. SlotInv.v, Seg/Tac_slot.v
   and Seg/Tac_fsfree.v read the laws only through these. *)
Section LawFields.
Variable API : AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Local Notation AHl := (AC.aa_AH AC.ASYMS AsanRTInv.RT API).
Local Notation OWNl := (AC.aa_owned AC.ASYMS AsanRTInv.RT API).
Local Notation SLOl := (AC.aa_stklo AC.ASYMS AsanRTInv.RT API).
Local Notation SHIl := (AC.aa_stkhi AC.ASYMS AsanRTInv.RT API).
Local Notation LAWSl := (AC.aa_laws AC.ASYMS AsanRTInv.RT API).

(* a_laws_blocks: a live block's placement and its bytes. *)
Record lw_blk (H : list (Z * Z)) (mem : word -> option byte) (md : Model) (p n : Z) : Prop := {
  lwb_align : p mod 16 = 0;
  lwb_low : 4096 <= p;
  lwb_end : p + n <= SLOl mem md;
  lwb_app_end : end_in_app p n;
  lwb_byte : forall a, p <= a < p + n ->
    app_mem a /\ writable_at rsegs mem a /\ ~ AC.a_in_img a /\ ~ AC.a_on_img_page a /\ ~ AC.a_in_fs AC.ASYMS mem a }.
Lemma lw_blocks : forall H mem md p n, AHl H mem md -> In (p, n) H -> lw_blk H mem md p n.
Proof.
  intros H mem md p n HAH Hin.
  decompose [and ex] (AC.a_laws_blocks _ _ _ _ _ LAWSl H mem md p n HAH Hin).
  constructor;
    first [ eassumption
          | intros a Ha; match goal with Hx : forall a, _ -> app_mem a /\ _ |- _ =>
              let Hc := fresh "Hc" in pose proof (Hx a Ha) as Hc; decompose [and] Hc; repeat split; assumption end ].
Qed.

(* lwb_byte's last conjunct by name (image A's twin, same name and statement; a Theorem Labs lane's F13 / F16 read it). *)
Lemma lwb_byte_not_fs : forall H mem md p n, lw_blk H mem md p n ->
  forall a, p <= a < p + n -> ~ AC.a_in_fs AC.ASYMS mem a.
Proof. intros H mem md p n HB a Ha. exact (proj2 (proj2 (proj2 (proj2 (lwb_byte H mem md p n HB a Ha))))). Qed.

(* a_laws_not_owned: the runtime owns neither a block / slack / FakeStack / real-stack byte nor its shadow byte. *)
Record lw_now (H : list (Z * Z)) (mem : word -> option byte) (md : Model) (a : Z) : Prop := {
  lwn_byte : ~ OWNl H mem md a;
  lwn_shadow : ~ OWNl H mem md (shadow_addr a) }.
Lemma lw_not_owned : forall H mem md a, AHl H mem md ->
  (AC.in_blocks H a \/ AC.in_slack H a \/ AC.a_in_fs AC.ASYMS mem a \/ SLOl mem md <= a < APPMEM_END) ->
  lw_now H mem md a.
Proof.
  intros H mem md a HAH Hor.
  decompose [and] (AC.a_laws_not_owned _ _ _ _ _ LAWSl H mem md a HAH Hor). constructor; assumption.
Qed.

(* a_laws_client: the runtime owns no shadow byte of an image byte (the field this bundle reads). *)
Lemma lw_client_img_shadow : forall H mem md a, AHl H mem md -> AC.a_in_img a -> ~ OWNl H mem md (shadow_addr a).
Proof.
  intros H mem md a HAH Hi.
  decompose [and] (AC.a_laws_client _ _ _ _ _ LAWSl H mem md a HAH).
  match goal with Hx : AC.a_in_img a -> ~ _ |- _ => exact (Hx Hi) end.
Qed.

(* a_laws_fs_place: the FakeStack region. *)
Record lw_fsp (mem : word -> option byte) (md : Model) (b : Z) : Prop := {
  lwf_gt : AC.GT <= b;
  lwf_end : b + AC.FS_SIZE <= SLOl mem md;
  lwf_align : b mod 4096 = 0;
  lwf_app : forall a, b <= a < b + AC.FS_SIZE -> app_mem a }.
Lemma lw_fs_place : forall H mem md b, AHl H mem md -> word_mem rsegs mem (AC.as_tp AC.ASYMS) b ->
  0 <= b < 2 ^ 64 -> lw_fsp mem md b.
Proof.
  intros H mem md b HAH Hw Hr.
  decompose [and] (AC.a_laws_fs_place _ _ _ _ _ LAWSl H mem md b HAH Hw Hr). constructor; assumption.
Qed.

(* a_laws_fs_state: the FakeStack's runtime state (the field this file reads). *)
Lemma lw_fs_ok : forall H mem md FS, AHl H mem md -> word_mem rsegs mem (AC.as_tp AC.ASYMS) FS ->
  0 <= FS < 2 ^ 64 -> AC.a_fs_ok mem FS.
Proof.
  intros H mem md FS HAH Hw Hr.
  decompose [and ex] (AC.a_laws_fs_state _ _ _ _ _ LAWSl H mem md FS HAH Hw Hr). assumption.
Qed.

(* a_fs_ok's bytes (its conjunct this bundle reads). *)
Lemma lw_fs_bytes : forall mem FS, AC.a_fs_ok mem FS ->
  forall a, FS <= a < FS + AC.FS_SIZE -> writable_at rsegs mem a /\ exists b, mbyte rsegs mem a = Some b.
Proof.
  intros mem FS Hok. unfold AC.a_fs_ok in Hok. decompose [and] Hok. assumption.
Qed.

(* a_laws_mat_le: lazy-page materialization keeps AH, ownership and the stack bounds. *)
Record lw_mat (H : list (Z * Z)) (mem : word -> option byte) (md md' : Model) : Prop := {
  lwm_ah : AHl H mem md -> AHl H mem md';
  lwm_own : forall a, OWNl H mem md' a <-> OWNl H mem md a;
  lwm_lo : SLOl mem md' = SLOl mem md;
  lwm_hi : SHIl mem md' = SHIl mem md }.
Lemma lw_mat_le : forall H mem md md', AsanLift.mat_le md md' -> lw_mat H mem md md'.
Proof.
  intros H mem md md' Hm.
  decompose [and] (AC.a_laws_mat_le _ _ _ _ _ LAWSl H mem md md' Hm). constructor; assumption.
Qed.

(* a_laws_store: a store outside the allocator's store set keeps AH, ownership and the stack bounds. *)
Record lw_sto (H : list (Z * Z)) (mem mem' : word -> option byte) (md : Model) : Prop := {
  lws_ah : AHl H mem' md;
  lws_own : forall a, OWNl H mem' md a <-> OWNl H mem md a;
  lws_lo : SLOl mem' md = SLOl mem md;
  lws_hi : SHIl mem' md = SHIl mem md }.
Lemma lw_store : forall H mem mem' md, AHl H mem md ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ AC.a_store_ok H (SLOl mem md) a -> mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)) ->
  (forall a, 0 <= a < 2 ^ 64 -> writable_at rsegs mem a -> writable_at rsegs mem' a) ->
  lw_sto H mem mem' md.
Proof.
  intros H mem mem' md HAH P1 P2.
  decompose [and] (AC.a_laws_store _ _ _ _ _ LAWSl H mem mem' md HAH P1 P2). constructor; assumption.
Qed.

(* a_laws_fs_store: a store that, outside the allocator's store set, writes only the FakeStack region [FS, FS + FS_SIZE)
   or its shadow, and leaves the FakeStack's runtime state a_fs_ok, keeps AH, ownership and the stack bounds (same
   record as lw_store). *)
Lemma lw_fs_store : forall H mem mem' md FS, AHl H mem md ->
  word_mem rsegs mem (AC.as_tp AC.ASYMS) FS -> 0 <= FS < 2 ^ 64 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ AC.a_store_ok H (SLOl mem md) a -> ~ (FS <= a < FS + AC.FS_SIZE) ->
     ~ (exists b, FS <= b < FS + AC.FS_SIZE /\ a = shadow_addr b) -> mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)) ->
  (forall a, 0 <= a < 2 ^ 64 -> writable_at rsegs mem a -> writable_at rsegs mem' a) ->
  AC.a_fs_ok mem' FS ->
  lw_sto H mem mem' md.
Proof.
  intros H mem mem' md FS HAH Hw Hr P1 P2 Hok.
  decompose [and] (AC.a_laws_fs_store _ _ _ _ _ LAWSl H mem mem' md FS HAH Hw Hr P1 P2 Hok). constructor; assumption.
Qed.
End LawFields.
Arguments lwn_byte {API H mem md a} _.
Arguments lwn_shadow {API H mem md a} _.

(* The slot's OWN share of class c: one slot of class c (the harness holds at most one block of its own at a
   time: fuzz_dup at fuzz_ctrl.c:524 freed at :613 before fuzz_dup at :704 freed at :706), 0 at the classes no
   primary request reaches. The body of a Theorem Labs lane's CtrlClassLive.BC_ctrl (a working branch
   61aba11640, CtrlClassLive.v (not in this delivery)), as image A's SlotInv.v (0b6b7fff89f). Top level, not a section variable: no
   lemma's arity moves. *)
Definition BC_ctrl (c : Z) : Z :=
  if (c =? 0) || (c =? 5) || (c =? 31) then 0 else AsanCtrl.size_of_class c.

Section Slot.
Context {fx : YK11.FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Let API := APIf rc.
Let segs := ms_segs B.

(* Registers and memory cells (as lib/U/Prog/SlotInv.v). Register numbers: ra 1, sp 2, gp 3, tp 4, s0 8, s1 9,
   a0-a7 10-17, s2 18, s3 19, s4 20, s5 21, s6 22, s7 23, s8 24, s9 25, s10 26, s11 27. *)
Definition rg (regs : bvmap 5 word) (r : bv 5) (v : Z) : Prop := getr regs r = Z_to_bv 64 v.
Definition q64 (m : word -> option byte) (a v : Z) : Prop := bytes_at rsegs m a (le8 (Z_to_bv 64 v)).
Definition u32 (m : word -> option byte) (a v : Z) : Prop := bytes_at rsegs m a (le4 (Z_to_bv 64 v)).
Definition u16 (m : word -> option byte) (a v : Z) : Prop := bytes_at rsegs m a (le2 (Z_to_bv 64 v)).
Definition b8 (m : word -> option byte) (a v : Z) : Prop := bytes_at rsegs m a [Z_to_bv 8 v].
Definition hb1 (phi n : Z) : list (Z * Z) := [(phi, n)].

(* The 13 caller registers saved at [S - 104, S): ra and s0-s11 (plan 3.1, FP.1). *)
Definition saved_bytes (g : ghost) : list byte :=
  le8 (getr (g_regs g) 27) ++ le8 (getr (g_regs g) 26) ++ le8 (getr (g_regs g) 25) ++
  le8 (getr (g_regs g) 24) ++ le8 (getr (g_regs g) 23) ++ le8 (getr (g_regs g) 22) ++
  le8 (getr (g_regs g) 21) ++ le8 (getr (g_regs g) 20) ++ le8 (getr (g_regs g) 19) ++
  le8 (getr (g_regs g) 18) ++ le8 (getr (g_regs g) 9) ++ le8 (getr (g_regs g) 8) ++ le8 (Z_to_bv 64 ra).

(* S(fr), the shadow byte of the frame base: (fr >> 3) + 0x7fff8000 (AsanRT.shadow_addr, K = ASAN_K). *)
Definition Sfr (fr : Z) : Z := shadow_addr fr.

(* The stack window every cut carries below its own sp. The entry pre gives the stack facts at the entry sp S with
   K = SLOT_STACK (stklo <= S - 2^20, [S - 2^20, S) readable and writable), so PREF and FRA carry them S-anchored;
   every sp of the function is above S - 4096 (A = (S - 448) & -32 >= S - 479, real-arm sp = fr = A - 3136 >=
   S - 3615), so the sp-anchored window [sp - FN_STACK, sp) of fra_win lies inside [S - SLOT_STACK, S), and every
   callee's own stack need (largest 2224, the checked memcpy) is below FN_STACK. *)
Definition FN_STACK : Z := AF.SLOT_STACK - 4096.

(* The side-arm FakeStack frame record (push 5b, for frame_release_6 / asan_stack_free_6_contract): the frame is
   slot j of size class 6 of the FakeStack FS (the word at tp), its flag byte is 1 (in use) and the slot's last word
   holds the flag's address, as A1's frame_alloc_6 call (0x8108c jal frame_alloc_6, a0 = 3136) leaves them. The
   fs_* layout is the one the stack-allocation contracts read (lib/B/Prog/asan_stack_malloc_c.v; Contract.v's
   a_fs_* are the same formulas). *)
Definition FSREC (fr : Z) (mem : word -> option byte) : Prop :=
  exists FS j, word_mem rsegs mem (AC.as_tp AC.ASYMS) FS /\ 0 <= FS < 2 ^ 64 /\ 0 <= j < SMC.fs_M 6 /\
    fr = SMC.fs_frame FS 6 j /\ bytes_at rsegs mem (SMC.fs_flag FS 6 j) [Z_to_bv 8 1] /\
    bytes_at rsegs mem (fr + SMC.fs_B 6 - 8) (le8 (Z_to_bv 64 (SMC.fs_flag FS 6 j))).

(* FRA (plan 3.1): the frame-and-shadow invariant carried at every cut from A3 to Y2, on top of the ubsan twin.
   The frame base fr (fr mod 32 = 0) is carried by the spill q64 (A + 336) = fr (s1+336, set 0x810c4, never
   overwritten), NOT by a register: s9 and s8 hold fr / the request result only up to 0x815e0 / 0x815e4 (v1.9
   0x815e0 `addi s9,s2,-1`, 0x815e4 `ld s8,56(s1)`) and are reused as the input left count and the code-byte
   pointer afterwards (so FRA pins neither reg 25 nor reg 24; the A-region cuts add rg regs 25 fr in their own
   body). s1 = A the spill base, s0 = S, s3 = S(fr), s10 = ASAN_K the shadow
   offset (reg 26, loaded at 0x81078, never rewritten before the epilogue reload 0x82f8c, so it holds K at
   every FRA cut; every inline shadow check computes `add aX, aX, s10`). The frame bytes are a_store_ok
   (real arm, s8 = 0) or in FS (side arm, s8 = fr) by the frame-location disjunction. Plus
   the frame header, the 392 shadow bytes S(fr)..S(fr)+391 (FP.4, carried abstractly as a 392-byte list), the slot
   window writable, the saved caller registers, the asan runtime RT, the live heap H = hb ++ the entry heap with
   the single-buffer ROOM bound, and the runtime cells ro_agree / sink_none / errno. Also the spill-base bounds
   sp <= A (the frame / side-stack block sits at or below the spill base A = s1) and A + 448 <= S (the 448-byte
   prologue save area [A, A+448) fits below the entry sp S), both read off the prologue 0x81018-0x81088.
   Push 5c adds what the callee preconditions of the segments need at every FRA cut: the slot window outside the
   frame addressable (the entry pre gives the whole window addressable and only the frame's shadow is poisoned,
   so fra_call_pre can hand a callee its own window) and the three ghost facts about the ENTRY state's stack top
   that a_call_pre asks for (S at or below stkhi, stkhi at or below APPMEM_END, the bytes of [S, stkhi) present
   at entry); ENT carries those three to the cut's own state. The fr reload spill q64 (A + 40) = fr (v1.9 stored
   0x815ac `sd s9,40(s1)`, reloaded 0x82f28 `ld s9,40(s1)`; patched [A+56], 0x81540 / 0x82ec4) is in FRA only:
   FRAS / FRAR drop it, as they drop the selector spill [A+48] (0x815a8 `sd s8,48(s1)`; patched [A+64]), since
   the early edge 0x81450 reaches the release join with neither written.
   Push 5b: the side arm carries the FakeStack frame record FSREC (the release call frame_release_6 reads the
   flag byte and the slot's last word), and its separation bound is FS + 6328320 <= fr (the metadata and the
   classes below 6), not FS + 36864: fs_frame FS 6 j = FS + 36864 + 6 * 2^20 + j * 4096.
   No mem_inv here (5d): the entry pre gives ro_agree only, and a callee reaches its own mem_inv premise
   through MemNorm.evt_normalize from ro_agree (slot contract S1.7).
   Input facts (image A's text, carried here once instead of per segment): the input bytes at p and, for n > 0, the
   input block (p, n) live in the entry heap and addressable, which the entry pre (alib_pre) gives. *)
Definition FRA (g : ghost) (fr : Z) (hb : list (Z * Z)) (regs : bvmap 5 word) (mem : word -> option byte)
    (md : Model) : Prop :=
  exists A sp s5,
    AsanRTInv.RT sp mem md /\
    AC.aa_AH AC.ASYMS AsanRTInv.RT API (hb ++ g_H g) mem md /\
    ro_agree rsegs mem /\ sink_none B mem md /\ m_halted md = None /\
    G_img_c B AF.frame_RELRO mem /\
    getr regs 2 = Z_to_bv 64 sp /\ sp mod 16 = 0 /\ AC.aspZ regs = sp /\
    AC.aa_stklo AC.ASYMS AsanRTInv.RT API mem md <= g_S g - AF.SLOT_STACK /\
    getr regs 4 = Z_to_bv 64 (AC.as_tp AC.ASYMS) /\
    rg regs 8 (g_S g) /\ rg regs 9 A /\ getr regs 3 = getr (g_regs g) 3 /\
    rg regs 19 (Sfr fr) /\ rg regs 26 ASAN_K /\
    fr mod 32 = 0 /\ (s5 = 0 \/ s5 = fr) /\ A mod 32 = 0 /\ A <= g_S g /\ sp <= A /\ fr + FRAME_BYTES <= A /\
    A + 448 <= g_S g /\ g_S g - 4096 < sp /\ g_S g < APPMEM_END /\
    q64 mem (A + 336) fr /\ q64 mem (A + 48) s5 /\ q64 mem (A + 40) fr /\
    ((s5 = 0 /\ sp = fr /\
        (forall a, fr <= a < fr + FRAME_BYTES -> AC.aa_stklo AC.ASYMS AsanRTInv.RT API mem md <= a < APPMEM_END)) \/
     (s5 = fr /\
        (forall FS, word_mem rsegs mem (AC.as_tp AC.ASYMS) FS -> 0 <= FS < 2 ^ 64 -> FS + 6328320 <= fr) /\
        (forall a, fr <= a < fr + FRAME_BYTES -> AC.a_in_fs AC.ASYMS mem a) /\ FSREC fr mem)) /\
    q64 mem fr 0x41b58ab3 /\ q64 mem (fr + 16) AF.ENTRY /\
    (exists sh, bytes_at rsegs mem (Sfr fr) sh /\ length sh = Z.to_nat FRAME_SHADOW) /\
    stk rsegs mem (g_S g - AF.SLOT_STACK) (g_S g) /\
    bytes_at rsegs mem (g_S g - 104) (saved_bytes g) /\
    (forall a, AC.a_errno AC.ASYMS <= a < AC.a_errno AC.ASYMS + 4 -> writable_at rsegs mem a) /\
    (forall a, in_globals AF.frame_AG a -> addressable mem a 1) /\
    (forall a, g_S g - AF.SLOT_STACK <= a < g_S g -> ~ (fr <= a < fr + FRAME_BYTES) -> addressable mem a 1) /\
    g_S g <= AC.aa_stkhi AC.ASYMS AsanRTInv.RT API (g_mem g) (g_md g) /\
    AC.aa_stkhi AC.ASYMS AsanRTInv.RT API (g_mem g) (g_md g) <= APPMEM_END /\
    (forall a, g_S g <= a < AC.aa_stkhi AC.ASYMS AsanRTInv.RT API (g_mem g) (g_md g) ->
       exists b, mbyte rsegs (g_mem g) a = Some b) /\
    (length hb <= 1)%nat /\ AC.a_live_bytes (g_H g) <= 5 * 2 ^ 30 /\
    bytes_at rsegs mem (g_p g) (g_in g) /\ (0 < g_n g -> In (g_p g, g_n g) (g_H g) /\ addressable mem (g_p g) (g_n g)).

(* ENT (push 5c): what a cut keeps of the ENTRY state. It is exactly the part of the slot post
   (AF.alib_post, lib/B/FrameAPI.v:76-103) that compares the return state with the entry state and that FRA does
   not already give; the segment that runs the epilogue turns it into the post with ent_post (Seg/Tac_slot.v).
   Each conjunct names the alib_post line it serves. hb is the cut's extra live list, as in FRA: the post reads
   the live list H' of the return, which at a cut is hb ++ the entry heap. ENT is a predicate of its own,
   conjoined in CUTST / CUTST0 / CUTSTR next to FRA (not inside FRA): its transports are the entry-relation ones
   (ent_store / ent_call / ent_mat of Seg/Tac_slot.v), which are not the frame's. *)
Definition ENT (g : ghost) (hb : list (Z * Z)) (mem : word -> option byte) (md : Model) : Prop :=
  (* ghost-only facts of the ENTRY state (Inv_ENTRY), which the post's sp-anchored and leaf clauses read: the
     entry sp is S, the kept blocks were live at entry (post 100), the entry file system is sorted (post 98, the
     leaf being pinned to LL 0 (m_fs (g_md g)) []), and the rounding mode is zero (Post's frm_zero). *)
  AC.aspZ (g_regs g) = g_S g /\
  (* ghost tp (push 5b, needed by Y3's `getr regs 4 = getr (g_regs g) 4` reload at 0x82f94): the entry tp word
     is the as_tp constant. ent_entry proves it from a_call_pre_tp; every ENT transport keeps it (it names only g). *)
  getr (g_regs g) 4 = Z_to_bv 64 (AC.as_tp AC.ASYMS) /\
  (forall t, In t (g_T g) -> In t (g_H g)) /\
  Fs.fs_sorted (m_fs (g_md g)) = true /\
  frm_zero (@fp_csr fx) /\
  (* post 81-82: the model changed only in its maps, its lazy-page ledgers and its fd table (same lookups); its
     file system is the entry one. *)
  (exists lz mt vm' fds' pins',
     md = with_vm_backing lz mt (os_upd vm' fds' (m_fs (g_md g)) pins' (g_md g)) /\
     (forall k, fd_lookup fds' k = fd_lookup (m_fds (g_md g)) k)) /\
  (* post 83: the real stack's bounds are the entry ones. *)
  AC.aa_stklo AC.ASYMS AsanRTInv.RT API mem md = AC.aa_stklo AC.ASYMS AsanRTInv.RT API (g_mem g) (g_md g) /\
  AC.aa_stkhi AC.ASYMS AsanRTInv.RT API mem md = AC.aa_stkhi AC.ASYMS AsanRTInv.RT API (g_mem g) (g_md g) /\
  (* post 85: the bytes of every entry block the target does not keep (the harness's input buffer included). *)
  (forall q k i, In (q, k) (g_H g) -> ~ In (q, k) (g_T g) -> 0 <= i < k ->
     mbyte rsegs mem (q + i) = mbyte rsegs (g_mem g) (q + i)) /\
  (* post 86-88: the image's bytes and their writability, outside what the memory-checking runtime owns (in the
     entry state and in this one), outside G and outside errno. *)
  (forall a, AC.a_in_img a ->
     ~ AC.aa_owned AC.ASYMS AsanRTInv.RT API (g_H g) (g_mem g) (g_md g) a ->
     ~ AC.aa_owned AC.ASYMS AsanRTInv.RT API (hb ++ g_H g) mem md a ->
     ~ in_globals AF.frame_G a ->
     ~ (AC.a_errno AC.ASYMS <= a < AC.a_errno AC.ASYMS + 4) ->
     mbyte rsegs mem a = mbyte rsegs (g_mem g) a /\
     (writable_at rsegs (g_mem g) a <-> writable_at rsegs mem a)) /\
  (* post 91-92: the stack at or above the entry sp S. *)
  (forall a, g_S g <= a < APPMEM_END ->
     mbyte rsegs mem a = mbyte rsegs (g_mem g) a /\
     (writable_at rsegs (g_mem g) a <-> writable_at rsegs mem a)) /\
  (* post 93-94 (asan): the shadow bytes of the image and of [S, APPMEM_END). *)
  (forall a, (AC.a_in_img a \/ g_S g <= a < APPMEM_END) ->
     mbyte rsegs mem (shadow_addr a) = mbyte rsegs (g_mem g) (shadow_addr a)) /\
  (* ENT append #1 (v1.9, = image A's): alib_post's "and their Shadow" conjunct (FrameAPI.v alib_post, frame batch 2
     item 9, a Theorem Labs lane 05:19Z), verbatim with ENT's binders: the shadow bytes of every entry block the target does
     not keep. Transports: ent_shadow_entry / ent_shadow_store / ent_shadow_call / ent_shadow_mat (Seg/Tac_slot.v). *)
  (forall q k i, In (q, k) (g_H g) -> ~ In (q, k) (g_T g) -> 0 <= i < k ->
     mbyte rsegs mem (shadow_addr (q + i)) = mbyte rsegs (g_mem g) (shadow_addr (q + i))) /\
  (* Generation N.1's per-class bound, 14th and LAST (a Theorem Labs lane's design 16:0xZ, mirrored from image A, 0b6b7fff89f):
     SOME per-class bound BE on the ENTRY heap, with room for the slot's own share under the shared budget 2 ^ 22
     (classbound/fuzz_ctrl.tsv (a working note, not in this delivery): Bc = 2 ^ 22, m = 1, SP = size_of_class c; image B has the same allocator
     class table, lib/AZ/Spec/AsanCtrl.v, and the same harness heap use). It is existential, so no section variable is
     added and no lemma's arity moves. It names only the ghost, so every transport keeps the witness; Seg/Tac_cls.v's
     sl_malloc_cls / sl_free_cls turn it into the allocator's class premises with Bc c = BE c + BC_ctrl c. At entry it
     is the slot's named premise ENTRY_CLASS (Seg/Tac_slot.v), which the driver owes until a Theorem Labs lane puts it in
     alib_pre. *)
  (exists BE : Z -> Z,
     (forall c, 0 <= c < AsanCtrl.K_NUM_CLASSES -> ClassConsDef.a_class_bytes (g_H g) c <= BE c) /\
     (forall c, 0 <= c < AsanCtrl.K_NUM_CLASSES -> BE c + BC_ctrl c <= 2 ^ 22)).

(* ENT append #1 as a predicate of its own (the statement of its four transports). *)
Definition ent_shd (g : ghost) (mem : word -> option byte) : Prop :=
  forall q k i, In (q, k) (g_H g) -> ~ In (q, k) (g_T g) -> 0 <= i < k ->
    mbyte rsegs mem (shadow_addr (q + i)) = mbyte rsegs (g_mem g) (shadow_addr (q + i)).

(* A cut: the config at pc with FRA (the frame base fr is existential, passed to the register/memory predicate P)
   and ENT, the extra live buffer list hb, and P the cut's own register/memory content. *)
Definition CUTST (g : ghost) (pc : Z) (hb : list (Z * Z))
    (P : Z -> bvmap 5 word -> (word -> option byte) -> Prop) (c : config) : Prop :=
  exists regs mem md fr,
    c = mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom segs)) md /\
    FRA g fr hb regs mem md /\ ENT g hb mem md /\ P fr regs mem.

(* FRAH: FRA with the frame selector sel (the frame request's result, s8 = reg 24) a parameter instead of an
   existential, WITHOUT the spill q64 mem (A + 48) sel, and with the frame header word hdr a parameter. The selector
   is stored to [A + 48] only at 0x815a8 (`sd s8,48(s1)`), at the exit 0x815a0-0x815ac of the our[] loop, inside the A5
   (0x81548) and R1 (0x81550) segments; the early edge 0x81450 (`j 0x82f2c`, after the size test 0x81424-0x8144c)
   reaches the release join with the selector in register 24 alone and with neither [A + 48] nor [A + 40] written.
   The cuts before the store and on that edge carry FRAH and name the selector themselves. The header word is
   0x41b58ab3 up to the release join and 0x45e0360e after the store at 0x82f34. FRAH carries FRA's input facts (the
   input bytes at p and, for n > 0, the block (p, n) live and addressable), which the entry pre gives. *)
Definition FRAH (g : ghost) (fr : Z) (hb : list (Z * Z)) (regs : bvmap 5 word) (mem : word -> option byte)
    (md : Model) (sel hdr : Z) : Prop :=
  exists A sp,
    AsanRTInv.RT sp mem md /\
    AC.aa_AH AC.ASYMS AsanRTInv.RT API (hb ++ g_H g) mem md /\
    ro_agree rsegs mem /\ sink_none B mem md /\ m_halted md = None /\
    G_img_c B AF.frame_RELRO mem /\
    getr regs 2 = Z_to_bv 64 sp /\ sp mod 16 = 0 /\ AC.aspZ regs = sp /\
    AC.aa_stklo AC.ASYMS AsanRTInv.RT API mem md <= g_S g - AF.SLOT_STACK /\
    getr regs 4 = Z_to_bv 64 (AC.as_tp AC.ASYMS) /\
    rg regs 8 (g_S g) /\ rg regs 9 A /\ getr regs 3 = getr (g_regs g) 3 /\
    rg regs 19 (Sfr fr) /\ rg regs 26 ASAN_K /\
    fr mod 32 = 0 /\ (sel = 0 \/ sel = fr) /\ A mod 32 = 0 /\ A <= g_S g /\ sp <= A /\ fr + FRAME_BYTES <= A /\
    A + 448 <= g_S g /\ g_S g - 4096 < sp /\ g_S g < APPMEM_END /\
    q64 mem (A + 336) fr /\
    ((sel = 0 /\ sp = fr /\
        (forall a, fr <= a < fr + FRAME_BYTES -> AC.aa_stklo AC.ASYMS AsanRTInv.RT API mem md <= a < APPMEM_END)) \/
     (sel = fr /\
        (forall FS, word_mem rsegs mem (AC.as_tp AC.ASYMS) FS -> 0 <= FS < 2 ^ 64 -> FS + 6328320 <= fr) /\
        (forall a, fr <= a < fr + FRAME_BYTES -> AC.a_in_fs AC.ASYMS mem a) /\ FSREC fr mem)) /\
    q64 mem fr hdr /\ q64 mem (fr + 16) AF.ENTRY /\
    (exists sh, bytes_at rsegs mem (Sfr fr) sh /\ length sh = Z.to_nat FRAME_SHADOW) /\
    stk rsegs mem (g_S g - AF.SLOT_STACK) (g_S g) /\
    bytes_at rsegs mem (g_S g - 104) (saved_bytes g) /\
    (forall a, AC.a_errno AC.ASYMS <= a < AC.a_errno AC.ASYMS + 4 -> writable_at rsegs mem a) /\
    (forall a, in_globals AF.frame_AG a -> addressable mem a 1) /\
    (forall a, g_S g - AF.SLOT_STACK <= a < g_S g -> ~ (fr <= a < fr + FRAME_BYTES) -> addressable mem a 1) /\
    g_S g <= AC.aa_stkhi AC.ASYMS AsanRTInv.RT API (g_mem g) (g_md g) /\
    AC.aa_stkhi AC.ASYMS AsanRTInv.RT API (g_mem g) (g_md g) <= APPMEM_END /\
    (forall a, g_S g <= a < AC.aa_stkhi AC.ASYMS AsanRTInv.RT API (g_mem g) (g_md g) ->
       exists b, mbyte rsegs (g_mem g) a = Some b) /\
    (length hb <= 1)%nat /\ AC.a_live_bytes (g_H g) <= 5 * 2 ^ 30 /\
    bytes_at rsegs mem (g_p g) (g_in g) /\ (0 < g_n g -> In (g_p g, g_n g) (g_H g) /\ addressable mem (g_p g) (g_n g)).

(* Before the release's header store: the header word is the one A3 wrote at 0x810ec. *)
Definition FRAS (g : ghost) (fr : Z) (hb : list (Z * Z)) (regs : bvmap 5 word) (mem : word -> option byte)
    (md : Model) (sel : Z) : Prop := FRAH g fr hb regs mem md sel 0x41b58ab3.
(* After it (0x82f34 `sd a0,0(s9)` with a0 = 0x45e0360e, so Y1 at 0x82f48 and Y2 at 0x82f58). *)
Definition FRAR (g : ghost) (fr : Z) (hb : list (Z * Z)) (regs : bvmap 5 word) (mem : word -> option byte)
    (md : Model) (sel : Z) : Prop := FRAH g fr hb regs mem md sel 0x45e0360e.

(* The FRAS cut: as CUTST, with the selector passed to the cut's own predicate as well as the frame base. *)
Definition CUTST0 (g : ghost) (pc : Z) (hb : list (Z * Z))
    (P : Z -> Z -> bvmap 5 word -> (word -> option byte) -> Prop) (c : config) : Prop :=
  exists regs mem md fr sel,
    c = mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom segs)) md /\
    FRAS g fr hb regs mem md sel /\ ENT g hb mem md /\ P fr sel regs mem.
(* The same cut after the release's header store. *)
Definition CUTSTR (g : ghost) (pc : Z) (hb : list (Z * Z))
    (P : Z -> Z -> bvmap 5 word -> (word -> option byte) -> Prop) (c : config) : Prop :=
  exists regs mem md fr sel,
    c = mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom segs)) md /\
    FRAR g fr hb regs mem md sel /\ ENT g hb mem md /\ P fr sel regs mem.

(* Two Z values held by the same register agree modulo 2^64. *)
Lemma rg_eq64 : forall (regs : bvmap 5 word) (r : bv 5) (a b : Z),
  rg regs r a -> rg regs r b -> a mod 2 ^ 64 = b mod 2 ^ 64.
Proof.
  intros regs r a b Ha Hb. unfold rg in Ha, Hb. rewrite Ha in Hb.
  apply (f_equal bv_unsigned) in Hb. rewrite !Z_to_bv_unsigned in Hb.
  unfold bv_wrap in Hb. change (bv_modulus 64) with (2 ^ 64) in Hb. exact Hb.
Qed.

(* and so agree outright when both lie in one 2^64-wide window. v1.9.0: the bound on a is 2^64 - 56, what the
   selector spill [A + 48] gives (A + 48 + 8 <= 2^64; patched [A + 64] gave 2^64 - 72; a Theorem Labs lane 15:17Z). *)
Lemma rg_eq : forall (regs : bvmap 5 word) (r : bv 5) (a b : Z),
  rg regs r a -> rg regs r b -> -64 <= a -> a <= 2 ^ 64 - 56 -> 0 < b -> b <= 2 ^ 64 - 448 -> a = b.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros regs r a b Ha Hb H1 H2 H3 H4.
  pose proof (rg_eq64 regs r a b Ha Hb) as Hm.
  revert Hm H1 H2 H3 H4. change (2 ^ 64) with 18446744073709551616.
  intros Hm H1 H2 H3 H4. Z.div_mod_to_equations. lia.
Qed.

(* FRA gives FRAS at the selector its existential names, plus the [A + 48] spill of that selector. *)
Lemma FRAS_of_FRA : forall g fr hb regs mem md,
  FRA g fr hb regs mem md ->
  exists sel A, rg regs 9 A /\ FRAS g fr hb regs mem md sel /\ q64 mem (A + 48) sel.
Proof.
  intros g fr hb regs mem md H. destruct H as (A & sp & sel & H).
  exists sel, A. split; [unfold rg; tauto | split; [exists A, sp; tauto | tauto]].
Qed.

(* and conversely: FRAS plus the two spills at [A + 48] (the selector) and [A + 40] (the fr reload read at
   0x82f28) rebuilds FRA. The spill base A is pinned by
   register 9, so it is the A of FRAS's existential (rg_eq, with 0 < A from sp <= A and S - 4096 < sp). *)
Lemma FRA_of_FRAS : forall g fr hb regs mem md sel A,
  FRAS g fr hb regs mem md sel -> rg regs 9 A -> q64 mem (A + 48) sel -> q64 mem (A + 40) fr ->
  FRA g fr hb regs mem md.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros g fr hb regs mem md sel A HS Hr9 Hsel Hfr40.
  destruct HS as (A' & sp & HS).
  assert (Hr9' : rg regs 9 A') by tauto.
  assert (Hsp : sp <= A') by tauto.
  assert (HS4 : g_S g - 4096 < sp) by tauto.
  assert (HA448 : A' + 448 <= g_S g) by tauto.
  assert (Hstk : stk rsegs mem (g_S g - AF.SLOT_STACK) (g_S g)) by tauto.
  assert (Hb : 0 <= g_S g - AF.SLOT_STACK /\ g_S g <= 2 ^ 64)
    by (unfold stk in Hstk; split; [apply (proj1 Hstk) | apply (proj1 (proj2 Hstk))]).
  assert (Hsa : 0 <= A + 48 /\ A + 48 + Z.of_nat (length (le8 (Z_to_bv 64 sel))) <= 2 ^ 64)
    by (unfold q64, bytes_at in Hsel; split; [apply (proj1 Hsel) | apply (proj1 (proj2 Hsel))]).
  rewrite length_le8 in Hsa.
  assert (HAeq : A = A').
  { apply (rg_eq regs 9 A A' Hr9 Hr9'); unfold AF.SLOT_STACK in Hb; lia. }
  subst A'. exists A, sp, sel. tauto.
Qed.

(* The sp-anchored window the callee contracts ask for, read off FRA's S-anchored stack facts: every sp of the
   function is above S - 4096 and at most A <= S, so [sp - FN_STACK, sp) is a sub-window of [S - SLOT_STACK, S). *)
Lemma fra_win : forall g fr hb regs mem md,
  FRA g fr hb regs mem md ->
  AC.aa_stklo AC.ASYMS AsanRTInv.RT API mem md <= AC.aspZ regs - FN_STACK /\
  stk rsegs mem (AC.aspZ regs - FN_STACK) (AC.aspZ regs).
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros g fr hb regs mem md H. destruct H as (A & sp & s5 & H).
  assert (Hsp : AC.aspZ regs = sp) by tauto.
  assert (Hlo : AC.aa_stklo AC.ASYMS AsanRTInv.RT API mem md <= g_S g - AF.SLOT_STACK) by tauto.
  assert (HS4 : g_S g - 4096 < sp) by tauto.
  assert (HspA : sp <= A) by tauto.
  assert (HAS : A <= g_S g) by tauto.
  assert (Hstk : stk rsegs mem (g_S g - AF.SLOT_STACK) (g_S g)) by tauto.
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  rewrite Hsp. unfold FN_STACK. split; [lia|].
  destruct (stk_split rsegs mem (g_S g - AF.SLOT_STACK) (sp - (AF.SLOT_STACK - 4096)) (g_S g) Hstk
              ltac:(lia)) as (_ & Hhi).
  destruct (stk_split rsegs mem (sp - (AF.SLOT_STACK - 4096)) sp (g_S g) Hhi ltac:(lia)) as (Hw & _).
  exact Hw.
Qed.

(* The frame's placement, for the callee premises of the call segments: the 3136-byte frame is either entirely 16
   bytes or more below sp (side arm: it is in the FakeStack, which the allocator laws put below stklo) or starts
   exactly at sp (real arm); it is below the spill base in register 9; the FakeStack's metadata and the classes
   below 6 (its first 6328320 bytes) are below it on both arms; and every frame byte is writable (real arm from
   the entry-anchored window, side arm from a_fs_ok). *)
Lemma fra_frame : forall g fr hb regs mem md,
  FRA g fr hb regs mem md ->
  (forall K, 0 <= K <= FN_STACK -> fr + FRAME_BYTES <= AC.aspZ regs - K \/ AC.aspZ regs <= fr) /\
  fr + FRAME_BYTES <= bv_unsigned (getr regs 9) /\
  (forall FS, word_mem rsegs mem (AC.as_tp AC.ASYMS) FS -> 0 <= FS < 2 ^ 64 -> FS + 6328320 <= fr) /\
  (forall a, fr <= a < fr + FRAME_BYTES -> writable_at rsegs mem a).
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros g fr hb regs mem md HFRA.
  destruct HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA448 & HS4 & HAPP &
    Hspill & Hsel & Hfr40 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive & Hinb & Hinblk).
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HFSsz : AC.FS_SIZE = 11571200) by reflexivity.
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  unfold stk in Hwin. destruct Hwin as (Hw0 & Hw1 & Hwv).
  assert (HA64 : 0 <= A < 2 ^ 64) by lia.
  assert (Hplace : forall FS, word_mem rsegs mem (AC.as_tp AC.ASYMS) FS -> 0 <= FS < 2 ^ 64 ->
            FS + AC.FS_SIZE <= AC.aa_stklo AC.ASYMS AsanRTInv.RT API mem md).
  { intros FS Hw HFSr.
    destruct (lw_fs_place API (hb ++ g_H g) mem md FS HAH Hw HFSr) as [_ Hend _]. exact Hend. }
  assert (HbvA : bv_unsigned (getr regs 9) = A).
  { unfold rg in Hr9. rewrite Hr9, Z_to_bv_unsigned. unfold bv_wrap.
    change (bv_modulus 64) with (2 ^ 64). apply Z.mod_small. exact HA64. }
  destruct Hloc as [[H0 [Hspfr Hreal]]|[Hfr0 [HfsbS [Hfs _]]]].
  - split; [intros K HK; right; lia|].
    split; [rewrite HbvA; lia|].
    split.
    { intros FS Hw HFSr. pose proof (Hplace FS Hw HFSr) as Hend. lia. }
    { intros a Ha. exact (proj1 (Hwv a ltac:(lia))). }
  - destruct (Hfs (fr + FRAME_BYTES - 1) ltac:(lia)) as (FSb & HFSr & Hw & Hlo2 & Hhi2).
    pose proof (Hplace FSb Hw HFSr) as Hend.
    split; [intros K HK; left; unfold FN_STACK in HK; lia|].
    split; [rewrite HbvA; lia|].
    split; [exact HfsbS|].
    { intros a Ha.
      destruct (Hfs a Ha) as (FSa & HFSar & Hwa & Hloa & Hhia).
      pose proof (lw_fs_bytes mem FSa (lw_fs_ok API (hb ++ g_H g) mem md FSa HAH Hwa HFSar)) as Hwr.
      exact (proj1 (Hwr a ltac:(lia))). }
Qed.
(* The frame body is byte-backed (adopt 9, image A's fra_stk of push 13B): on the real arm the frame lies in
   (S - 4096, A] inside FRA's entry-anchored window [S - SLOT_STACK, S), on the side arm every frame byte is a
   FakeStack byte, which a_fs_ok makes writable and present. So FLI's `stk rsegs m fr (fr + 3136)` need not be
   a cut conjunct before the frame loop: P12's exit Inv_B81ec4_at g 0 gets it here. *)
Lemma fra_stk : forall g fr hb regs mem md,
  FRA g fr hb regs mem md -> stk rsegs mem fr (fr + FRAME_BYTES).
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros g fr hb regs mem md HFRA.
  destruct HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA448 & HS4 & HAPP &
    Hspill & Hsel & Hfr40 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive & Hinb & Hinblk).
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  unfold stk in Hwin. destruct Hwin as (Hw0 & Hw1 & Hwv).
  unfold stk.
  destruct Hloc as [[H0 [Hspfr Hreal]]|[Hfr0 [HfsbS [Hfs _]]]].
  - split; [lia|]. split; [lia|]. intros a Ha. apply Hwv. lia.
  - destruct (Hfs fr ltac:(lia)) as (FS0 & HFS0r & Hw00 & Hlo0 & Hhi0).
    split; [lia|]. split; [lia|].
    intros a Ha.
    destruct (Hfs a Ha) as (FSa & HFSar & Hwa & Hloa & Hhia).
    pose proof (lw_fs_bytes mem FSa (lw_fs_ok API (hb ++ g_H g) mem md FSa HAH Hwa HFSar)) as Hwr.
    exact (Hwr a ltac:(lia)).
Qed.

(* Every frame byte is app memory: on the real arm the frame lies in [stklo, APPMEM_END) and the allocator laws
   put stklo at or above HIGHMEM_BEG; on the side arm it lies in the FakeStack, whose bytes a_laws_fs_place makes
   app memory. (A lemma, not an FRA conjunct: both arms already carry the fact a callee needs.) *)
Lemma fra_app : forall g fr hb regs mem md,
  FRA g fr hb regs mem md -> AC.GT <= fr /\ (forall a, fr <= a < fr + FRAME_BYTES -> app_mem a).
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros g fr hb regs mem md HFRA.
  destruct HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA448 & HS4 & HAPP &
    Hspill & Hsel & Hfr40 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive & Hinb & Hinblk).
  assert (Hhigh : HIGHMEM_BEG <= AC.aa_stklo AC.ASYMS AsanRTInv.RT API mem md)
    by exact (AC.a_laws_stack_high _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT API) (hb ++ g_H g) mem md HAH).
  destruct Hloc as [[H0 [Hspfr Hreal]]|[Hfr0 [HfsbS [Hfs _]]]].
  - destruct (Hreal fr ltac:(lia)) as (Hlo1 & _).
    unfold AC.GT, HIGHMEM_BEG in *.
    split; [lia|]. intros a Ha. destruct (Hreal a Ha) as (Hlo2 & Hhi2).
    unfold app_mem, HIGHMEM_BEG, APPMEM_END in *. right. lia.
  - destruct (Hfs fr ltac:(lia)) as (FS0 & HFS0r & Hw0 & Hlo0 & Hhi0).
    destruct (lw_fs_place API (hb ++ g_H g) mem md FS0 HAH Hw0 HFS0r) as [HGTb _ _ _].
    split; [unfold AC.GT in *; lia|]. intros a Ha.
    destruct (Hfs a Ha) as (FSa & HFSar & Hwa & Hloa & Hhia).
    destruct (lw_fs_place API (hb ++ g_H g) mem md FSa HAH Hwa HFSar) as [_ _ _ Happ].
    exact (Happ a ltac:(lia)).
Qed.

(* FRA's input facts, projected: the input bytes at p and, for n > 0, the block (p, n) live and addressable. *)
Lemma fra_in : forall g fr hb regs mem md,
  FRA g fr hb regs mem md ->
  bytes_at rsegs mem (g_p g) (g_in g) /\
  (0 < g_n g -> In (g_p g, g_n g) (g_H g) /\ addressable mem (g_p g) (g_n g)).
Proof.
  intros g fr hb regs mem md H. destruct H as (A & sp & s5 & H).
  split; [tauto|]. intros Hn. tauto.
Qed.

(* Every byte of the input block is apart from what a run of the function writes: for n > 0 the block (p, n) is a
   live block of g_H g, so a_laws_blocks puts each of its bytes in app memory below stklo, outside the image and
   outside FS; so it is apart from the frame on both arms (real arm: every frame byte is at or above stklo; side
   arm: every frame byte is in FS). (For n <= 0 the range is empty.) *)
Lemma fra_in_apart : forall g fr hb regs mem md,
  FRA g fr hb regs mem md ->
  forall x, g_p g <= x < g_p g + g_n g ->
    app_mem x /\ x < AC.aa_stklo AC.ASYMS AsanRTInv.RT API mem md /\ ~ (fr <= x < fr + FRAME_BYTES) /\
    ~ AC.a_in_img x.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros g fr hb regs mem md HFRA x Hx.
  destruct HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA448 & HS4 & HAPP &
    Hspill & Hsel & Hfr40 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive & Hinb & Hinblk).
  destruct (Hinblk ltac:(lia)) as (Hin & _).
  destruct (lw_blocks API (hb ++ g_H g) mem md (g_p g) (g_n g) HAH (in_or_app _ _ _ (or_intror Hin))) as [_ _ Hend _ Hb].
  destruct (Hb x Hx) as (Happ & _ & Himg & _ & Hnfs).
  split; [exact Happ|]. split; [lia|]. split; [|exact Himg].
  intros Hfr. destruct Hloc as [[_ [_ Hreal]]|[_ [_ [Hfs _]]]].
  - destruct (Hreal x Hfr) as (Hlo & _). lia.
  - exact (Hnfs (Hfs x Hfr)).
Qed.

(* The fr reload spill at [A + 40] (stored 0x815ac, read at 0x82f28), which FRAS / FRAR drop; A in register 9 is
   in range (A <= S, S - 4096 < sp <= A, and stk puts S - SLOT_STACK at or above 0 and S at or below 2^64). *)
Lemma fra_fr_spill : forall g fr hb regs mem md,
  FRA g fr hb regs mem md -> exists A, rg regs 9 A /\ 0 <= A < 2 ^ 64 /\ q64 mem (A + 40) fr.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros g fr hb regs mem md H. destruct H as (A & sp & s5 & H). exists A.
  assert (Hr9 : rg regs 9 A) by tauto.
  assert (Hsp : sp <= A) by tauto.
  assert (HAS : A <= g_S g) by tauto.
  assert (HS4 : g_S g - 4096 < sp) by tauto.
  assert (Hstk : stk rsegs mem (g_S g - AF.SLOT_STACK) (g_S g)) by tauto.
  assert (Hsp40 : q64 mem (A + 40) fr) by tauto.
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  unfold stk in Hstk. destruct Hstk as (Hb0 & Hb1 & _).
  split; [exact Hr9 | split; [lia | exact Hsp40]].
Qed.

(* The callee precondition at any cut (FRA + ENT), for a stack need K of at most FN_STACK: the wrapper_malloc and
   wrapper_free calls (AK_MALLOC / AK_FREE = 4096) and every program callee. The runtime, the heap, ro_agree,
   m_halted, the sp alignment and the tp register are FRA's; the stack-low bound and the window's bytes come from
   fra_win, the window's addressability from FRA's window conjunct (the frame is apart from [sp - K, sp) by
   fra_frame) and the blocks are below stklo (a_laws_blocks); the stack top and the bytes of [sp, stkhi) are the
   ENTRY facts FRA carries, moved to this state by ENT's stkhi equality and its "at or above S" clause. The
   return register is the caller's: a `jal` sets it, so the segment supplies ret_ok. *)
Lemma fra_call_pre : forall g fr hb regs mem md K,
  FRA g fr hb regs mem md -> ENT g hb mem md ->
  YK0s.ret_ok (getr regs 1) -> 0 <= K <= FN_STACK ->
  AC.a_call_pre AC.ASYMS AsanRTInv.RT (AC.aa_AH AC.ASYMS AsanRTInv.RT API)
    (AC.aa_stklo AC.ASYMS AsanRTInv.RT API) (AC.aa_stkhi AC.ASYMS AsanRTInv.RT API)
    K (hb ++ g_H g) regs mem md.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros g fr hb regs mem md K HFRA HENT Hret HK.
  pose proof (fra_win g fr hb regs mem md HFRA) as (Hlo & Hwk).
  pose proof (fra_frame g fr hb regs mem md HFRA) as (Hapart & _ & _ & _).
  pose proof HFRA as HF.
  destruct HF as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA448 & HS4 & HAPP &
    Hspill & Hsel & Hfr40 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive & Hinb & Hinblk).
  destruct HENT as (Hasp & Htp & HTH & Hfs & Hfz & Hmdl & Hslo & Hshi & Hblk & Himg & Habv & Hshd & Hkshd).
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HFN : FN_STACK = 1044480) by reflexivity.
  pose proof Hwk as Hwk'. unfold stk in Hwk'. destruct Hwk' as (_ & _ & Hwkv).
  pose proof Hwin as Hwin'. unfold stk in Hwin'. destruct Hwin' as (_ & _ & Hwinv).
  assert (Hnb : forall a, AC.aa_stklo AC.ASYMS AsanRTInv.RT API mem md <= a ->
            ~ AC.in_blocks (hb ++ g_H g) a).
  { intros a Ha (p & n & Hin & Hr).
    destruct (lw_blocks API (hb ++ g_H g) mem md p n HAH Hin) as [_ _ Hend _]. lia. }
  apply AC.a_call_pre_intro.
  - exact (AsanRTInv.RT_any sp (AC.aspZ regs) mem md md HRT).
  - exact HAH.
  - exact Hret.
  - rewrite Haspz. exact Hspm.
  - lia.
  - lia.
  - rewrite Hshi. lia.
  - rewrite Hshi. exact HSHI2.
  - intros a Ha. rewrite Hshi in Ha.
    destruct (Z_lt_le_dec a (g_S g)) as [Hlt|Hge].
    + exact (proj2 (Hwinv a ltac:(lia))).
    + destruct (Habv a ltac:(lia)) as (Heq & _). rewrite Heq. exact (HSHI3 a ltac:(lia)).
  - intros a Ha. unfold AC.a_window in Ha.
    split; [exact (proj1 (Hwkv a ltac:(lia)))|].
    split.
    + apply HWA; [lia|]. destruct (Hapart K HK) as [Hd|Hd]; lia.
    + apply Hnb. lia.
  - exact Hr4.
  - exact Hro.
  - exact Hhalt.
  - intros a Ha. unfold AC.a_window in Ha. exact (proj2 (Hwkv a ltac:(lia))).
Qed.

(* ENTRY (A1, 0x81018): the slot pre at pc ENTRY plus the slot obligation's side premises (plan 3.3). *)
(* v1.9 pc 0x81018 *)
Definition Inv_ENTRY (g : ghost) (c : config) : Prop :=
  c = mkCfg (mkst (g_regs g) (Z_to_bv 64 AF.ENTRY) (g_mem g) (seg_rom segs)) (g_md g) /\
  AF.alib_pre B AsanRTInv.RT API AF.SLOT_STACK empty (g_H g) (g_regs g) (g_mem g) (g_md g)
    ra (g_p g) (g_n g) (g_in g) /\
  (forall t, In t (g_T g) -> In t (g_H g)) /\
  (0 < g_n g -> ~ In (g_p g, g_n g) (g_T g)) /\
  G_img_c B AF.frame_RELRO (g_mem g) /\
  AC.aspZ (g_regs g) = g_S g /\
  frm_zero (@fp_csr fx).

(* RET: the slot post at pc = ra (plan 3.3), for some return leaf l and kept-block list T'. *)
Definition Post (g : ghost) (c : config) : Prop :=
  exists (fx' : FPState) (l : lleaf) H' regs' mem' md' T',
    c = mkCfg (@mkst fx' regs' (Z_to_bv 64 ra) mem' (seg_rom segs)) md' /\
    frm_zero (@fp_csr fx') /\
    l = LL 0 (m_fs (g_md g)) [] /\ T' = g_T g /\
    AF.alib_post B AsanRTInv.RT API AF.frame_G AF.SLOT_STACK (g_H g) (g_regs g) (g_mem g) (g_md g)
      l (g_T g) T' H' regs' mem' md'.

(* Shared register / heap facts the cuts use. a0 is register 10 (as ubsan). HB(phi, len): the harness buffer's
   len bytes are addressable (a_new_block, Contract.v:181; plan 7 HB addressability). *)
Definition a0v (regs : bvmap 5 word) (v : Z) : Prop := rg regs 10 v.
Definition HB (mem : word -> option byte) (phi len : Z) : Prop := phi <> 0 /\ addressable mem phi (AC.a_size len).
Definition rnb (g : ghost) (b : nat) : Z := rt_n (g_in g) (Z.of_nat b).
(* The declaration slot in the frame: [A+96] = fr+2560 (set 0x814ec addi a1,a3,384 with a3 = fr+2176; spilled
   0x814f0 sd a1,96(s1); reloaded at 0x81a48 / 0x81a60), the expected declaration bytes for the bcmp at 0x81a64. *)
Definition decl_slot (fr : Z) : Z := fr + 2560.

(* ==== Image-B bundles: the lib/A/Prog/SlotInv.v bundles (CUR, RB, RS, RF, LK, LI, FC, FT, V7/FB, FSb, FLV, PORTS,
   ...) pinned to the image-B registers and spills of the v1.9.0 binary (capstone listing of
   libreac-v190/asan-ubsan/fuzz_ctrl). Frame variables keep the FP.4 "fr +"
   offsets below fr + 2880; v1.9.0 adds the local `first` (40 bytes at fr + 2880) and moves a / pl / n / code /
   blk by +80 (fr + 2960 / 2976 / 3008 / 3040 / 3056; frame 3136 bytes): id_rt fr+2176 at 0x814b4, frag_rt
   fr+2256 at 0x814bc, OUR fr+2624 at 0x814f4, id fr+2688 at 0x814fc, frag fr+2768 at 0x81504, first fr+2880 at
   0x8150c; each data spill is A + <offset> (s1-relative, A = reg 9). Registers: round trip b s6 (reg 22), cursor s7
   (reg 23), left s9 (reg 25), n_b s2 (reg 18), Phi_r s4 (reg 20), the constants s5 = 36 and s11 = 32 (0x816c8 /
   0x816cc); frame loop j a3 (reg 13) at the head 0x81ec4 and the spill A+240 after 0x81f44, cursor s7 (reg 23),
   left s9 (reg 25), len s4 (reg 20), body ptr s5 (reg 21), Phi s2 (reg 18), kind k s8 (reg 24), the constant
   s6 = 1 (reg 22, 0x81ea0), the sum flag s9 (reg 25, from 0x82140 `seqz s9,a0`), blk the spill A+312, the fill
   flag the spill A+184, 1 - sum flag the spill A+248. Data spills: fr A+336 (in FRA); the first-fragment state
   is the frame local `first` (have at fr + 2880, n at fr + 2884, body from fr + 2885; its pointer [A+168],
   the body pointer [A+88]; opens_record 0x825dc-0x82630); the record cursor left-h A+232 (0x81f40, read at the
   latch 0x82cb0) and p + body A+224 (0x81f60, read at 0x82ca8). The ubsan check-false conjuncts (plan 3.1) are
   not carried here. The frame-loop flag values (is_8819 / sum_ok / [len>=50] / TF) and the W00 row index are not
   pinned. *)
Definition spill (regs : bvmap 5 word) (m : word -> option byte) (off v : Z) : Prop :=
  exists A, rg regs 9 A /\ q64 m (A + off) v.
(* B: s7 holds p + c, s9 holds n - c (round trip: 0x815b4 addi s7,s6,1, 0x815e0 addi s9,s2,-1; frame-loop head:
   0x81ee8 lbu a0,0(s7), 0x81ec4 bnez s9) *)
Definition CUR (g : ghost) (c : Z) (regs : bvmap 5 word) : Prop :=
  0 <= c <= g_n g /\ rg regs 23 (g_p g + c) /\ rg regs 25 (g_n g - c).
Definition OURb (g : ghost) (fr : Z) (m : word -> option byte) : Prop :=
  bytes_at rsegs m (fr + 2624) (OUR (g_in g)).
Definition IDBr (g : ghost) (fr : Z) (idb : list byte) (m : word -> option byte) : Prop :=
  bytes_at rsegs m (fr + 2176) idb.
Definition FGBr (g : ghost) (fr : Z) (st : list byte) (m : word -> option byte) : Prop :=
  bytes_at rsegs m (fr + 2256) st.
Definition IDBe (g : ghost) (fr : Z) (idb : list byte) (m : word -> option byte) : Prop :=
  bytes_at rsegs m (fr + 2688) idb.
Definition FGBe (g : ghost) (fr : Z) (st : list byte) (m : word -> option byte) : Prop :=
  bytes_at rsegs m (fr + 2768) st.

(* Round trip (R6-R21), turn b: s6 = b, s4 = Phi_r, s9 = n_b; CUR g 7; our / id_rt / frag_rt. *)
(* B: s6 holds b (0x8169c li s6,0; 0x81ac0 addiw s6,s6,1; 0x81ac8 bne s6,a0,816ec) *)
Definition RB (g : ghost) (fr : Z) (b : nat) (idb fgb : list byte) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  (b <= 6)%nat /\ CUR g 7 regs /\ OURb g fr m /\ rg regs 22 (Z.of_nat b) /\ IDBr g fr idb m /\ FGBr g fr fgb m.
Definition RS (g : ghost) (fr : Z) (b : nat) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  RB g fr b (RID (g_in g) b) (RFG (g_in g) b) regs m.
(* B: s4 holds Phi_r (0x8176c mv s4,a0 after the malloc 0x81760) *)
Definition RFb (g : ghost) (fr : Z) (b : nat) (idb fgb : list byte) (phi : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  RB g fr b idb fgb regs m /\ rnb g b <> 0 /\ rg regs 20 phi /\ bytes_at rsegs m phi (rt_F (g_in g) (Z.of_nat b)).
(* B: s2 holds n_b (0x81714 mv s2,a0 after build_as 0x8170c), up to 0x819c0 (addi s2,s4,18) *)
Definition RFx (g : ghost) (fr : Z) (b : nat) (idb fgb : list byte) (phi : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  RFb g fr b idb fgb phi regs m /\ rg regs 18 (rnb g b).
Definition RF (g : ghost) (fr : Z) (b : nat) (phi : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  RFx g fr b (RID (g_in g) b) (RFG (g_in g) b) phi regs m.

(* Frame loop (F1-F38), turn j: j a3 / A+240, s2 = Phi, s4 = len, s5 = body ptr, s8 = k, A+312 = blk; id/frag of
   the entry (fr+2688/2768); the first-fragment state in the frame local `first` (fr+2880); p/B at fr+176;
   check_ports ports fr+128, first fr+160. *)
Definition IDb (g : ghost) (fr : Z) (idb : list byte) (m : word -> option byte) : Prop :=
  IDBe g fr idb m /\ RcIdentModel.id_ok idb.
Definition FGb (g : ghost) (fr : Z) (st : list byte) (m : word -> option byte) : Prop :=
  FGBe g fr st m /\ frag_ok st.
(* B (v1.9.0): the first-fragment state is the frame local `first` (fuzz_ctrl.c v1.9.0:243-247, :681; 40 bytes
   at fr + 2880): have the 4-byte int at fr + 2880 (0x825e8 `sw s6,0(a1)`, a1 = [A+168], s6 = 1; read 0x823e8
   `lw a0,0(a0)`), n the byte at fr + 2884 (0x82604-0x82610 `lbu a2,8(a1)` / `sb a2,4(a0)`, a1 = [A+312] the
   block), the body from fr + 2885 (0x82624-0x82630 checked_memcpy a0 = [A+88] = fr + 2885, a1 = block + 9,
   a2 = n). P3 zeroes all 40 bytes (0x81d00-0x81d0c checked_memset a0 = [A+168], a2 = 40), which is fs0. The
   patched image kept the state in the spills [A+112] / [A+136] / [A+128] / [A+120]; v1.9.0 has no such spills.
   The five positions are image A's (have, n, body, `first` addressable, FI; lib/A FSb): position 4 is the 40
   usable bytes of `first` (P3's shadow stores 0x81cdc / 0x81ce0 / 0x81cf4-0x81cfc; the next stores to
   360..364(s3) are the epilogue's). `regs` is kept as an argument so that FSb / FSj have image A's form. *)
Definition FSb (g : ghost) (fr : Z) (s : fstate) (st : list byte) (regs : bvmap 5 word) (m : word -> option byte)
    : Prop :=
  u32 m (fr + 2880) (fs_have s) /\ b8 m (fr + 2884) (fs_n s) /\
  bytes_at rsegs m (fr + 2885) (fs_body s) /\ addressable m (fr + 2880) 40 /\ FI st s.
Definition IDj (g : ghost) (fr : Z) (j : nat) (m : word -> option byte) : Prop := IDb g fr (t_ID (g_in g) j) m.
Definition FGj (g : ghost) (fr : Z) (j : nat) (m : word -> option byte) : Prop := FGb g fr (t_FG (g_in g) j) m.
Definition FSj (g : ghost) (fr : Z) (j : nat) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  FSb g fr (fst_at (g_in g) j) (t_FG (g_in g) j) regs m.
Definition IFS (g : ghost) (fr : Z) (j : nat) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  IDj g fr j m /\ FGj g fr j m /\ FSj g fr j regs m.
(* The turn's two frame records, the identity record at fr + 2688 ([A+176]) and the fragment record at fr + 2768
   ([A+208]), by range in turn j (read off the listing; every non-aborting path of the turn passes the calls
   named here, and no other instruction of the turn writes either record):
   - REC0 (t_ID j, t_FG j): from the loop head 0x81ec4 (LI's IFS j) up to the reply-path ingest call 0x82300
     (`jal reac_identity_ingest`, a0 = [A+184]) and, on the ir-false path, up to 0x82308;
   - RECR (t_IDr j, t_FG j): from 0x82304 (after that ingest) and the join 0x82308 up to the fragment call 0x82358;
     t_IDr j = rp_id (t_ID j) len g is the ingest's result when ir, the old record otherwise;
   - RECF (t_IDr j, t_FG (S j)): from 0x8235c (after `jal reac_ctrl_identity_fragment`, which writes the fragment
     record: t_FG (S j) = fg_st len (t_FG j) g) up to the record ingest call 0x82460;
   - RECS (t_ID (S j), t_FG (S j)): from 0x82464 (after that ingest, rf = 1) and the join 0x82468 (rf <> 1 from
     0x8237c) up to the first-fragment stores 0x825dc-0x82630 (the `first` local);
   - IFS g fr (S j) (both records and the first-fragment state FSj (S j)): from 0x82634, the join every path from
     0x82468 reaches after the stores, to the end of the turn (F38's entry 0x82d1c). Up to 0x82468 the cuts carry
     FSj g fr j, since `first` is rewritten only at 0x825e8 / 0x82610 / 0x82630 (and zeroed once, P3's 0x81d0c). *)
Definition FREC (g : ghost) (fr : Z) (idb st : list byte) (m : word -> option byte) : Prop :=
  IDb g fr idb m /\ FGb g fr st m.
Definition REC0 (g : ghost) (fr : Z) (j : nat) (m : word -> option byte) : Prop :=
  FREC g fr (t_ID (g_in g) j) (t_FG (g_in g) j) m.
Definition RECR (g : ghost) (fr : Z) (j : nat) (m : word -> option byte) : Prop :=
  FREC g fr (t_IDr (g_in g) j) (t_FG (g_in g) j) m.
Definition RECF (g : ghost) (fr : Z) (j : nat) (m : word -> option byte) : Prop :=
  FREC g fr (t_IDr (g_in g) j) (t_FG (g_in g) (S j)) m.
Definition RECS (g : ghost) (fr : Z) (j : nat) (m : word -> option byte) : Prop :=
  FREC g fr (t_ID (g_in g) (S j)) (t_FG (g_in g) (S j)) m.
(* The fragment scratch buffer of the frame loop: fragb fr = fr + 2768 = [A+208] (set 0x81508 with a1 = a3 + 592,
   a3 = fr + 2176; never rewritten). *)
Definition fragb (fr : Z) : Z := fr + 2768.
(* RAD (adopt 7): the three frame records' bytes marked usable, the identity record fr + 2688 (38 bytes), the
   fragment record fragb fr (72 bytes) and, new in v1.9.0, the first-fragment local `first` at fr + 2880 (40
   bytes). P3's shadow stores set them: 0x81cb0-0x81cbc `sb zero,336..339(s3)` and 0x81ce4 `sb a0,340(s3)`
   (a0 = 6) for [fr + 2688, fr + 2726); 0x81cc4-0x81cd8 `sb zero,349..354(s3)` and 0x81ce8-0x81cf0
   `sb zero,346..348(s3)` for [fr + 2768, fr + 2840); 0x81cdc / 0x81ce0 / 0x81cf4-0x81cfc `sb zero,360..364(s3)`
   for [fr + 2880, fr + 2920). The next stores to 336..354(s3) / 360..364(s3) are the epilogue's 0x82ed4-0x82f20
   (the frame-loop prologue's poison stores 0x81ea4-0x81ec0 are to 370..385(s3)), so RAD holds from P4 to the
   loop exit: P4 (which has the fragment record as addressable D 72, D = fr + 2768) and P5 carry it, then PL0
   (P6-P12) and FLI (every frame-loop cut). *)
Definition RAD (fr : Z) (m : word -> option byte) : Prop :=
  addressable m (fr + 2688) 38 /\ addressable m (fragb fr) 72 /\ addressable m (fr + 2880) 40.
(* KNT (adopt 11, prover a Theorem Labs lane's F1-F6 lanes): the kind-name table KNC.KIND_NAME (v1.9.0 0x9f580, 112 bytes, 14 name
   pointers) that the reac_ctrl_kind_name calls read (P11's 0x81e04, F7's 0x82170, F8's 0x8217c): its bytes and
   their addressability. The bytes are image data: the table lies in frame_RELRO's block, so
   FRA's G_img_c gives them at every FRA cut (a Theorem Labs lane's p11_table, lib/B/Prog/Seg/P11.v, with the image fact
   kn_table_in_image of lib/B/Prog/reac_ctrl_kind_name.v). The addressability is not FRA's: P1-P11 carry it, and
   no instruction of 0x81e08-0x82eac writes the table or its shadow bytes [0x8000beb0, 0x8000bebe): the stores
   there are to the spills (s1), to the frame's shadow S(fr) + k (s3, k < 392), to the local `first` and to frame
   cells through FLI's
   spills (0x821c4 / 0x821d0 / 0x821dc / 0x82898 / 0x82ae0 / 0x82bc0), and every callee writes only app memory
   (its stack window, the frame, the turn's heap block) or the shadow of the heap block and of its own frames. *)
Definition KNT (m : word -> option byte) : Prop :=
  bytes_at rsegs m KNC.KIND_NAME KNC.kind_name_bytes /\ addressable m KNC.KIND_NAME 112.

(* FLI (a Theorem Labs lane's frame-loop set, frameloop-bundle-B.md sections 1 and 3
   (a working note, not in this delivery); a Theorem Labs lane 14:18Z: one bundle, carried by every
   frame-loop cut through LK / LI): s11 = -8 (0x81e54 li s11,-8) and the 22 spills the loop body reads and no
   instruction in [0x81ec4, 0x82eac) writes (its stores to (s1) are [A+232] / [A+240] / [A+224] (0x81f40-0x81f60),
   [A+272], [A+184], [A+312] and [A+248]). Values read off the v1.9.0 listing:
   [A+160] = fr+32 (0x815a4, a6 = fr+32 at the A5 loop exit), [A+104] = fr+128, the ports words (0x81460),
   [A+136] = fr+160 (0x81468), [A+280] = fr+176 (0x81470), [A+288] = fr+256 (0x81478), [A+304] = fr+272 (0x81480),
   [A+296] = fr+304 (0x81488), [A+200] = fr+336 (0x81490), [A+216] = fr+448 (0x81498), [A+192] = fr+528
   (0x814a0), [A+176] = fr+2688 (0x81500, a1 = a3 + 512), [A+208] = fragb fr (0x81508), [A+168] = fr+2880, the
   local `first` (0x81510), [A+264] = fr+2624 (0x81544), [A+152] = fr+64 (0x815a0, a7 = s9 + 64 from 0x81458),
   then the frame-loop prologue: [A+256] = fragb fr + 8 (0x81e60), [A+128] = fragb fr + 19 (0x81e68), [A+120] =
   fragb fr + 15 (0x81e70), [A+88] = fr+2885, the body of `first` (0x81e74-0x81e7c), [A+112] = fr+186 (0x81e88,
   [A+280] + 10), [A+96] = fr+180 (0x81e90, [A+280] + 4), [A+144] = fr+452 (0x81e9c, [A+216] + 4). The patched
   prologue's flag [A+72] = 0 (an overflow test of fragb fr + 8, read by the patched F16 at 0x82390) has no v1.9.0
   counterpart and is not carried.
   Push 5b adds the two loop-invariant facts of image A's FLSI that this set lacked: our[]'s six bytes
   addressable (the A4 shadow store 0x814b0 `li a0,6` / 0x814b8 `sb a0,328(s3)` marks the granule at S(fr) + 328
   = shadow of fr + 2624 as 6 addressable bytes, and the next store to 328(s3) is the epilogue 0x82f14), and the
   frame body byte-backed, `stk fr (fr + 3136)` (loop-invariant because the body is written only through stores
   that keep stk). Adopt 7 adds RAD, the frame records' addressable bytes (P3's shadow stores
   0x81cb0-0x81cfc; the next stores to those shadow bytes are the epilogue's 0x82ed4-0x82f20). Adopt 11 adds KNT,
   the kind-name table (its bytes and their addressability; the F7 / F8 calls read it, and a Theorem Labs lane's F1-F6 cuts carry
   it there); P12 builds it at the loop head from Inv_B81e08.
   Positions (a Theorem Labs lane's rule: v1.8 positions kept, new facts appended): position 2 was the patched prologue
   flag [A+72] = 0 (read by the patched F16's address arm), which v1.9.0 does not have; it now holds what v1.9.0's
   F16 reads instead, the pointer of `first` [A+168] = fr + 2880 (0x81510), which is also position 27 (appended
   before the fill, kept so that no count changes); position 28 is the pointer of its body [A+88] (0x81e74-0x81e7c). *)
Definition FLI (g : ghost) (fr : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  rg regs 27 (-8) /\ spill regs m 168 (fr + 2880) /\
  spill regs m 96 (fr + 180) /\ spill regs m 112 (fr + 186) /\
  spill regs m 120 (fragb fr + 15) /\ spill regs m 128 (fragb fr + 19) /\
  spill regs m 136 (fr + 160) /\ spill regs m 144 (fr + 452) /\ spill regs m 152 (fr + 64) /\
  spill regs m 280 (fr + 176) /\ spill regs m 160 (fr + 32) /\ spill regs m 176 (fr + 2688) /\
  spill regs m 192 (fr + 528) /\ spill regs m 200 (fr + 336) /\ spill regs m 216 (fr + 448) /\
  spill regs m 208 (fragb fr) /\ spill regs m 104 (fr + 128) /\ spill regs m 256 (fragb fr + 8) /\
  spill regs m 264 (fr + 2624) /\ spill regs m 288 (fr + 256) /\ spill regs m 296 (fr + 304) /\
  spill regs m 304 (fr + 272) /\
  addressable m (fr + 2624) 6 /\ stk rsegs m fr (fr + FRAME_BYTES) /\ RAD fr m /\ KNT m /\
  spill regs m 168 (fr + 2880) /\ spill regs m 88 (fr + 2885).

(* PRA / PRO (adopt 9, the image-B twin of image A's PRO, push 13B on a working branch): the FLI facts that hold
   before the frame-loop prologue and that no instruction up to the loop head 0x81ec4 writes. The cuts from A5 to
   P12 carry them, so P12's exit Inv_B81ec4_at g 0 builds FLI from PRO, PL0 (RAD, [A+176], [A+208]), fra_stk and
   the prologue's own stores 0x81e54-0x81e9c (s11 = -8 and [A+256] / [A+128] / [A+120] / [A+88] / [A+112] /
   [A+96] / [A+144]).
   PRA: A4's ten frame-pointer spills (FLI's values): [A+104] = fr+128 (0x81460), [A+136] = fr+160 (0x81468),
   [A+280] = fr+176 (0x81470), [A+288] = fr+256 (0x81478), [A+304] = fr+272 (0x81480), [A+296] = fr+304
   (0x81488), [A+200] = fr+336 (0x81490), [A+216] = fr+448 (0x81498), [A+192] = fr+528 (0x814a0), [A+168] =
   fr+2880 (0x81510, the local `first`). A5 / R1 carry PRA next to LOOPB. (The patched A4 also spilled fr+32 at
   0x81400, PRA's position 3; v1.9.0 keeps fr+32 in a6 through the our[] loop and spills it at the loop exit, so
   [A+160] = fr+32 is PRO's position 5; position 3 holds v1.9.0's new A4 frame-pointer spill [A+168] = fr+2880,
   which is also position 11 (appended before the fill, kept so that no count changes).)
   PRO: PRA, [A+152] = fr+64 (0x815a0 `sd a7,152(s1)` at the A5 loop exit, a7 = fr+64 from 0x81458, LOOPB's
   reg 17), [A+160] = fr+32 (0x815a4 `sd a6,160(s1)`, a6 = fr+32, LOOPB's reg 16), [A+264] = fr+2624 (0x81544)
   and our[]'s six bytes addressable (0x814b8 `sb a0,328(s3)`, a0 = 6).
   The P cuts P1-P12 carry PRO. Before them each cut already states [A+264] and our[]'s six bytes (LOOPB, R2-R5,
   RBE), so R2-R5 carry PRA, [A+152] and [A+160] next to those, and RBE carries them for R6-R21 and the latch.
   No instruction of 0x81548-0x81ec4 writes them: its stores to (s1) are [A+152] / [A+160] / [A+48] / [A+40]
   (0x815a0-0x815ac), [A+8] (0x81634), [A+32] / [A+24] / [A+272] / [A+16] (0x816a4-0x816b8),
   [A+256] / [A+248] / [A+128] (0x816d8-0x816e8) and the prologue's [A+256] / [A+128] / [A+120] / [A+88] /
   [A+112] / [A+96] / [A+144] (0x81e60-0x81e9c). No instruction forms a
   pointer from s1, so no callee gets an address in [A, A + 448): callee stack windows are below sp <= A, and the
   frame arguments are below fr + 3136 <= A. The shadow byte 328(s3) is written only at 0x814b8 and 0x82f14; the
   two shadow fills of the range (0x8163c meta_fill_00 and 0x81ca4 meta_fill_f8, a0 = S(fr) + 68, a1 = 186 /
   187) end below S(fr) + 256. *)
Definition PRA (fr : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  spill regs m 136 (fr + 160) /\ spill regs m 280 (fr + 176) /\ spill regs m 168 (fr + 2880) /\
  spill regs m 192 (fr + 528) /\ spill regs m 200 (fr + 336) /\ spill regs m 216 (fr + 448) /\
  spill regs m 104 (fr + 128) /\ spill regs m 288 (fr + 256) /\ spill regs m 296 (fr + 304) /\
  spill regs m 304 (fr + 272) /\ spill regs m 168 (fr + 2880).
Definition PRO (fr : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  PRA fr regs m /\ spill regs m 152 (fr + 64) /\ spill regs m 264 (fr + 2624) /\
  addressable m (fr + 2624) 6 /\ spill regs m 160 (fr + 32).

(* B: j is spilled at A+240 from F1's body to F38 (0x81f44 sd a3,240(s1); reloaded 0x82ca0 ld s5,240(s1)) *)
Definition LK (g : ghost) (fr : Z) (j : nat) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  (j <= 255)%nat /\ spill regs m 240 (Z.of_nat j) /\ OURb g fr m /\ FLI g fr regs m.
(* B: at the loop head 0x81ec4 j is in a3, not yet spilled (0x81e50 li a3,0; 0x82d1c addiw a3,s5,1; 0x82d24
   bne a3,a0,81ec4) *)
Definition LI (g : ghost) (fr : Z) (j : nat) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  (j <= 255)%nat /\ rg regs 13 (Z.of_nat j) /\ OURb g fr m /\
  CUR g (t_c (g_in g) j) regs /\ 1 <= t_left (g_in g) j /\ IFS g fr j regs m /\ FLI g fr regs m.
(* B: left-h at A+232 (0x81f40 sd s9,232(s1)); s5 holds the body pointer (0x81ecc addi s5,s7,1 / 0x81f20 addi
   s5,s7,2; spilled 0x81f60 sd s5,224(s1)); s4 holds len (0x81f28 or s4,a1,a0 / 0x81f30 mv s4,s9) *)
Definition FC (g : ghost) (fr : Z) (j : nat) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  spill regs m 232 (t_left (g_in g) j - t_h (g_in g) j) /\ rg regs 21 (g_p g + t_body (g_in g) j) /\
  rg regs 20 (t_len (g_in g) j).
(* FTURN: the per-turn facts every frame cut past F2's copy holds. The turn's two cursor spills, [A+224] = p +
   body_j (0x81f60 sd s5,224(s1)) and [A+232] = left_j - h_j (0x81f40 sd s9,232(s1)); no other store to either
   slot in the frame loop (the only other stores are A4's 0x814e0 / 0x814d8), and F37 reloads both (0x82ca8 ld
   s7,224(s1); 0x82cb0 ld a0,232(s1)) for the cursor of turn j + 1. And the frame's len bytes at Phi: F2's
   checked_memcpy 0x81f74 (a0 = s2 = Phi, a1 = s5 = p + body, a2 = s4 = len; skipped by 0x81f64 `beqz s4` when len
   = 0, where t_phi is empty), no store through s2 and no write of s2 in the loop body, and the callees that get
   Phi read it only (a Theorem Labs lane: F31's PT32 at 0x82af8 reads them; another Theorem Labs lane's F26-F29 local cuts carry them; v1.9.0's
   opens_record copy 0x82630 reads Phi + 27 .. and writes `first`). So FTURN holds
   from 0x81f78 to the end of the turn: FCUTP carries it, and so does every CUTST cut of the frame-loop body. *)
Definition FTURN (g : ghost) (j : nat) (phi : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  spill regs m 224 (g_p g + t_body (g_in g) j) /\ spill regs m 232 (t_left (g_in g) j - t_h (g_in g) j) /\
  bytes_at rsegs m phi (t_phi (g_in g) j) /\ Z.of_nat (length (t_phi (g_in g) j)) <= t_len (g_in g) j.
(* Adopt 8: the 50-byte prefix of the frame bytes at Phi, `50 <= flen g j -> bytes_at m phi (t_g (g_in g) j)`,
   follows from FTURN's frame bytes, so no frame cut carries it as a bundle of its own: t_g j = fr50 (t_phi j) is
   the first 50 bytes of t_phi j when t_phi j has at least 50, and t_phi j has exactly len_j bytes (len_j <= left_j
   - h_j = n - body_j: f_len, f_body and fc's range, as a Theorem Labs lane's f38_fc_range (in a Seg/F38.v not in this delivery)). fturn_g gives
   the prefix on every cut with FTURN (FCUTP and the frame-loop CUTST cuts, 0x81f78 to the end of the turn). *)
Lemma inb_range : forall inp c, 0 <= inb inp c < 256.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros inp c. unfold inb, RcIdentModel.bz.
  pose proof (bv_unsigned_in_range 8 (RcIdentModel.nthb inp (Z.to_nat c))) as H.
  unfold bv_modulus in H. cbn in H. lia.
Qed.

Lemma fc_range : forall inp j, 0 <= fc inp j <= nlen inp.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros inp j. induction j as [|j IH].
  - cbn [fc]. unfold c0, nlen. lia.
  - rewrite fc_S.
    assert (HL : 0 <= f_L inp (fc inp j)).
    { unfold f_L. pose proof (inb_range inp (fc inp j)). pose proof (inb_range inp (fc inp j + 1)).
      destruct (2 <=? f_left inp (fc inp j)); lia. }
    unfold f_next, f_body, f_len, f_h, f_left in *. lia.
Qed.

Lemma t_phi_length : forall inp j, length (t_phi inp j) = Z.to_nat (t_len inp j).
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros inp j. pose proof (fc_range inp j) as R.
  assert (HL : 0 <= f_L inp (fc inp j)).
  { unfold f_L. pose proof (inb_range inp (fc inp j)). pose proof (inb_range inp (fc inp j + 1)).
    destruct (2 <=? f_left inp (fc inp j)); lia. }
  unfold t_phi, t_len, f_phi. rewrite length_firstn, length_skipn.
  unfold f_body, f_len, f_h, f_left, nlen in *. lia.
Qed.

Lemma t_g_of_phi : forall m phi inp j, bytes_at rsegs m phi (t_phi inp j) -> 50 <= t_len inp j ->
  bytes_at rsegs m phi (t_g inp j).
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros m phi inp j H H50.
  assert (HL : (50 <= length (t_phi inp j))%nat) by (rewrite t_phi_length; lia).
  assert (E : t_g inp j = firstn 50 (t_phi inp j)).
  { unfold t_g, fr50. rewrite firstn_app. replace (50 - length (t_phi inp j))%nat with 0%nat by lia.
    rewrite firstn_O, app_nil_r. reflexivity. }
  rewrite E. rewrite <- (firstn_skipn 50 (t_phi inp j)) in H. apply bytes_at_app in H. exact (proj1 H).
Qed.

Lemma fturn_g : forall g j phi regs m, FTURN g j phi regs m -> 50 <= t_len (g_in g) j ->
  bytes_at rsegs m phi (t_g (g_in g) j).
Proof. intros g j phi regs m (_ & _ & H & _) H50. exact (t_g_of_phi m phi (g_in g) j H H50). Qed.
(* B: s2 holds Phi (0x81f50 mv s2,a0 after the malloc 0x81f4c; not rewritten in the frame loop) *)
Definition FT (g : ghost) (fr : Z) (j : nat) (phi : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  LK g fr j regs m /\ FC g fr j regs m /\ rg regs 18 phi /\ bytes_at rsegs m phi (t_phi (g_in g) j).
(* B: s8 holds k (0x81fbc mv s8,a0 after the parse 0x81fb8) *)
Definition V7 (g : ghost) (j : nat) (regs : bvmap 5 word) : Prop := rg regs 24 (t_k (g_in g) j).
Definition pBb (g : ghost) (fr : Z) (j : nat) (m : word -> option byte) : Prop :=
  bytes_at rsegs m (fr + 176) (t_B (g_in g) j).
(* B: blk is spilled at A+312 (0x820d8 sd t0,312(s1) with t0 = s2 + 18 from 0x82074; 0x82054 sd zero,312(s1) on the
   len < 50 arm), from 0x820d8 on *)
Definition FB (g : ghost) (fr : Z) (j : nat) (phi : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  FT g fr j phi regs m /\ V7 g j regs /\ spill regs m 312 (if t_big (g_in g) j then phi + 18 else 0) /\ pBb g fr j m.
Definition PORTS (g : ghost) (fr : Z) (j : nat) (m : word -> option byte) : Prop :=
  (t_rp (g_in g) j = 0 ->
     u32 m (fr + 128) (4 * RcLeaf.n_in (t_pbs (g_in g) j)) /\
     u32 m (fr + 132) (4 * RcLeaf.n_out (t_pbs (g_in g) j)) /\
     u32 m (fr + 136) (16 * RcLeaf.bt (t_pbs (g_in g) j) 7)) /\
  (t_rp (g_in g) j <> 0 -> u32 m (fr + 128) (-7) /\ u32 m (fr + 132) (-7) /\ u32 m (fr + 136) (-7)).
Definition FIRSTb (g : ghost) (fr : Z) (j : nat) (m : word -> option byte) : Prop :=
  b8 m (fr + 160) (t_first (g_in g) j).

(* Frame-loop variables read on the F15 / F16 close path (0x82380-0x823d8). The fragment scratch buffer sits at
   fragb fr = fr + 2768 (= [A+208], set 0x81508 with a1 = a3 + 592, a3 = fr+2176, never rewritten); its three
   derived pointers are spilled once in the frame-loop prologue 0x81e58-0x81e70 ([A+208]+8 -> [A+256], +19 ->
   [A+128], +15 -> [A+120]; not rewritten in the frame loop). The identity_fragment call 0x82358 writes, into the
   output cells pp = [A+304] = fr+272 and pn = [A+296] = fr+304 (pointers set 0x8147c / 0x81484, never rewritten),
   the pl pointer fragb fr + 19 and the pll f_pll (= fg_T - 13) when it opens a record (t_rf j = 1): the
   0x823c4-0x823c8 check [A+128] = [pp] and the 0x82380-0x823b4 bounds 0 <= [pp]-[A+256] <= 64 and
   64 - ([pp]-[A+256]) >= [pn]+2 follow. *)
(* B: fragb+15 at A+120 (0x81e70), fragb+19 at A+128 (0x81e68), fragb+8 at A+256 (0x81e60), pp at A+304 (0x81480),
   pn at A+296 (0x81488) *)
Definition FLV (g : ghost) (fr : Z) (j : nat) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  spill regs m 120 (fragb fr + 15) /\ spill regs m 128 (fragb fr + 19) /\ spill regs m 256 (fragb fr + 8) /\
  spill regs m 304 (fr + 272) /\ spill regs m 296 (fr + 304) /\
  (t_rf (g_in g) j = 1 ->
     q64 m (fr + 272) (fragb fr + 19) /\
     q64 m (fr + 304) (f_pll (t_FG (g_in g) j) (t_g (g_in g) j))).

(* FLV's five pointer spills over one named spill base A = s1 (a Theorem Labs lane, lib/B/Prog/Seg/F7.v / F8.v): set in the
   frame-loop prologue (0x81e60 / 0x81e68 / 0x81e70) and before the loops (0x81480 / 0x81488), not written from
   there to F16. Carried by the F7 / F8 cuts (0x8215c, 0x82174, 0x82180). *)
Definition FLVsp (A fr : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  rg regs 9 A /\ q64 m (A + 120) (fragb fr + 15) /\ q64 m (A + 128) (fragb fr + 19) /\
  q64 m (A + 256) (fragb fr + 8) /\ q64 m (A + 304) (fr + 272) /\ q64 m (A + 296) (fr + 304).

(* The frame-loop record length of turn j. *)
Definition flen (g : ghost) (j : nat) : Z := t_len (g_in g) j.

(* The fragment model of the turn's F15 record compare (a7, lib/B/Prog/Seg/F15.v): the class the
   reac_ctrl_identity_fragment call site decides from its five pointers (the scratch fragb fr, Phi, and
   fr + 256 / fr + 272 / fr + 304) and the record bytes it writes. Moved here next to the bundles. *)
Definition frcl (g : ghost) (j : nat) (fr phi : Z) : RcFrag.fg_case :=
  RcFrag.fg_class (fragb fr) phi (fr + 256) (fr + 272) (fr + 304) (flen g j) (t_FG (g_in g) j) (t_g (g_in g) j).
Definition frrec (g : ghost) (j : nat) (fr phi : Z) : list byte :=
  fg_next (t_FG (g_in g) j) (t_g (g_in g) j) (frcl g j fr phi).

(* FM (a Theorem Labs lane's working note, section 2-3, not in this delivery): the per-turn registers and spills of the frame-loop body from the join of the two
   length arms at 0x8214c up to F23's register swap at 0x8284c. v1.9.0: the fill flag is the spill [A+184]
   (0x8204c `sd zero,184(s1)` on the len < 50 arm, 0x82100 `sd zero,184(s1)` when byte 16 <> 0, 0x8212c
   `sd a0,184(s1)` after 0x82128 `seqz a0,a0`; no other store in the loop), s8 = k (0x82058 / 0x81fbc; no write to
   0x8284c), s6 = 1 (0x81ea0 `li s6,1`, the constant the loop head 0x81ed0 and the have store 0x825e8 read; F16
   restores it at 0x82424 after borrowing s6), the sum flag s9 (0x8205c `mv s9,zero` on the len < 50 arm, 0x82140
   `seqz s9,a0` on the other; F16 restores it at 0x8242c) and the block pointer [A+312] (0x82054 zero on the
   len < 50 arm, 0x820d8 sd t0,312(s1) with t0 = Phi + 18 on the other; t_big j = (50 <=? t_len j) tells the arms
   apart). The patched image had the fill flag in s5, the record pointer fr + 176 in s6 and the sum flag in
   [A+288]; no v1.9.0 register holds fr + 176 (only [A+280], FLI). *)
Definition FM (g : ghost) (j : nat) (phi fr : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  spill regs m 184 (b2z (t_tfill (g_in g) j)) /\ rg regs 24 (t_k (g_in g) j) /\ rg regs 22 1 /\
  rg regs 25 (b2z (t_sum_ok (g_in g) j)) /\
  spill regs m 312 (if t_big (g_in g) j then phi + 18 else 0).

(* FTL: the same state after F23's swap (v1.9 0x82848 sd s8,272(s1); 0x8284c mv s8,s9) and before F29 undoes it
   (0x82ab4 mv s9,s8; 0x82ab8 ld s8,272(s1)): k is in the spill [A+272], s8 holds the sum flag, and the fill flag
   stays in its spill [A+184] (0x8212c / 0x8204c / 0x82100, no other store in the loop). No register holds the
   record pointer fr + 176 in v1.9 (only [A+280], FLI); position 1 (patched s5 = fr + 176) holds s5's v1.9 value,
   the ports pointer fr + 128 (0x82868 `ld s5,104(s1)`; s5 is not written again before F29, so it holds at every
   FTL cut 0x82878-0x82aa4); the positions of the fill flag (2), k (3), the sum flag (4) and the block (5) are kept. *)
Definition FTL (g : ghost) (j : nat) (phi fr : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  rg regs 21 (fr + 128) /\ spill regs m 184 (b2z (t_tfill (g_in g) j)) /\
  spill regs m 272 (t_k (g_in g) j) /\ rg regs 24 (b2z (t_sum_ok (g_in g) j)) /\
  spill regs m 312 (if t_big (g_in g) j then phi + 18 else 0).

(* FTK: the state from F29's restore (0x82ab0 `li s6,1`; 0x82ab4 `mv s9,s8`; 0x82ab8 `ld s8,272(s1)`) to the row
   loop's own uses of the registers (0x82bd0 `mv s5,a0` -> CAT; 0x82c18 `ld s6,152(s1)`): s6 = 1, s9 = the sum flag
   and s8 = k again, with k still in [A+272] and the fill flag in [A+184]. (a Theorem Labs lane's X30 at 0x82abc reads the fill
   flag; a Theorem Labs lane's F31 reads it and s8; F32's 0x82b3c-0x82b40 `ld a0,184(s1); or a0,a0,s9` is the TF test.) The
   patched image had the fill flag in s5, fr + 176 in s6 and the sum flag in [A+288]. *)
Definition FTK (g : ghost) (j : nat) (fr : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  spill regs m 184 (b2z (t_tfill (g_in g) j)) /\ rg regs 22 1 /\ rg regs 24 (t_k (g_in g) j) /\
  spill regs m 272 (t_k (g_in g) j) /\ rg regs 25 (b2z (t_sum_ok (g_in g) j)).

(* The record invariant (a Theorem Labs lane, lib/B/Prog/Seg/F18.v) at Phi (= s2), the spill base A (= s1) and the record
   pointer kp (= [A+280] = fr + 176 in v1.9.0; the patched image had it in s6), carried by the F18 cuts
   (0x82634, 0x8264c) to the F20 checks (0x82668-0x82720 read Phi+14..Phi+17 and their shadow bytes, the u16 at
   kp+20 through 0x82690 `ld a2,280(s1)`, and k = s8) and the F21 checks (Phi+18.. the record body, whose pointer
   Phi+18 is the spill [A+312], FB). The sum flag F21 reads is s9 in v1.9.0 (0x82728 `addi a1,s9,-1`; FM), not
   the patched spill [A+288]; the inner position 1 that held it now holds the spill of 1 - sum_ok, [A+248]
   (0x82148 `sd a0,248(s1)`, the only store in the loop; FS9). *)
Definition rec_inv (g : ghost) (j : nat) (phi A kp : Z) (m : word -> option byte) : Prop :=
  0 < phi /\ phi + 50 <= 2 ^ 64 /\ (50 <= flen g j)%Z /\ 0 <= t_k (g_in g) j < 2 ^ 64 /\
  (forall a, phi <= a < phi + 50 -> app_mem a) /\
  q64 m (A + 312) (phi + 18) /\
  bytes_at rsegs m (phi + 18) (t_blk (g_in g) j) /\
  bytes_at rsegs m (phi + 34) (RcFrag.bsl (t_g (g_in g) j) 34 6) /\
  (exists (field16 v14 v15 v16 v17 : Z),
     q64 m (A + 248) (1 - b2z (t_sum_ok (g_in g) j)) /\ u16 m (kp + 20) field16 /\ (kp + 22 <= 2 ^ 64) /\ 0 <= kp /\
     b8 m (phi + 14) v14 /\ b8 m (phi + 15) v15 /\ b8 m (phi + 16) v16 /\ b8 m (phi + 17) v17 /\
     0 <= v14 < 256 /\ 0 <= v15 < 256 /\ 0 <= v16 < 256 /\ 0 <= v17 < 256 /\
     b8 m (Z.shiftr (phi + 14) 3 + ASAN_K) 0 /\ b8 m (Z.shiftr (phi + 15) 3 + ASAN_K) 0 /\
     b8 m (Z.shiftr (phi + 16) 3 + ASAN_K) 0 /\ b8 m (Z.shiftr (phi + 17) 3 + ASAN_K) 0 /\
     field16 = v14 + 256 * v15 /\
     (if v16 =? 0 then (if v17 =? 0 then 1 else 0) else 0) = (if t_k (g_in g) j =? 1 then 1 else 0)).

(* The record bundles the F16 / F17 entry cuts read and F13-F15 carry (a Theorem Labs lane's retired Seg/F15.v (not in this delivery), f52ea940d3c:
   f15_rb / f15_rx, the text F14's exits give), with image A's short-arm guards (push 6c5b, A/Prog/Seg/F13.v (a version not in this delivery)
   Inv_A820a0_loc; from a working branch d70d9f3807). Every frame reaches 0x82340 .. 0x8237c: the short arm
   (len < 50: 0x81f7c bltu -> 0x82020, parse kind 0, reply_ret 0, 0x821f0 bne -> 0x82308 -> memcpy 0x8233c) and the
   long arm whose bytes 12 / 13 are not 0x88 / 0x19 as well (the fragment call returns 0 for FgNone, so the
   `bltz a0` at 0x8235c falls through). [A+272] = b2z (t_8819 j) (0x82018 seqz on the byte-13 test after the
   byte-12 test 0x81fe8; 0 at 0x82050 on the short arm and at 0x82068 when byte 12 is not 0x88; no other store
   before 0x82848), so: the [A+272] word is pinned by t_8819 in image A's form; the phi + 50 placements are under
   `50 <= flen g j ->`; the record invariant (its u16 at kp + 20 is the parsed struct's, which matches Phi's bytes
   14 / 15 only for a parsed header, t_8819 = cp_hdr) and the two 6-byte compare operands F18 / F19 read are under
   `t_8819 (g_in g) j = true ->`. kp is the record pointer [A+280] = fr + 176 (FLI). The first-fragment window
   these placements keep the reads apart from is v1.9.0's local `first`, [fr + 2880, fr + 2920), which
   opens_record writes at 0x825e8 / 0x82610 / 0x82630 before F18-F20 read Phi, kp + 20 and the operands (the
   patched image's window was the spill range [A+112, A+144) of its first-fragment spills 0x82598-0x825b0). The
   operands are [A+112] = fr + 186 = kp + 10 and [A+96] = fr + 180 = kp + 4 (FLI; patched [A+88] / [A+80]).
   Position 1 (v1.9): the window's bytes are app memory above the image (fra_app: GT <= fr, every frame byte app
   memory). The patched spill range lay above sp >= HIGHMEM_BEG; v1.9's `first` is a frame byte, and on FRA's side arm
   the frame is in the FakeStack, which a_laws_fs_place puts only at or above GT (a Theorem Labs lane, decision a Theorem Labs lane). *)
Definition FRB (g : ghost) (j : nat) (fr phi A kp : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  (forall a, fr + 2880 <= a < fr + 2920 -> app_mem a /\ AC.GT <= a) /\
  (exists w272, q64 m (A + 272) w272 /\ 0 <= w272 < 2 ^ 64 /\
     (t_8819 (g_in g) j = true -> w272 <> 0) /\ (t_8819 (g_in g) j = false -> w272 = 0)) /\
  (kp + 22 <= fr + 2880 \/ fr + 2920 <= kp + 20) /\
  (kp + 22 <= AC.aspZ regs - BW.BCMP_WRAP_K \/ AC.aspZ regs <= kp) /\
  (kp + 22 <= fr + 2688 \/ fr + 2688 + 38 <= kp + 20) /\
  (50 <= flen g j ->
     (phi + 50 <= fr + 2880 \/ fr + 2920 <= phi) /\
     (phi + 50 <= AC.aspZ regs - BW.BCMP_WRAP_K \/ AC.aspZ regs <= phi)) /\
  (t_8819 (g_in g) j = true ->
     rec_inv g j phi A kp m /\
     (exists (L : Z) (ls rs : list byte),
        q64 m (A + 112) L /\ bytes_at rsegs m L ls /\ length ls = 6%nat /\
        bytes_at rsegs m phi rs /\ length rs = 6%nat /\ SF.memcmp_model ls rs 6 = Some 0 /\
        addressable m L 6 /\ app_mem (L + 6) /\ app_mem (L + 7) /\
        (L + 6 <= AC.aspZ regs - BW.BCMP_WRAP_K \/ AC.aspZ regs <= L) /\
        (L + 6 <= fr + 2880 \/ fr + 2920 <= L) /\
        (L + 6 <= fr + 2688 \/ fr + 2688 + 38 <= L)) /\
     (exists (L2 : Z) (ls2 rs2 : list byte),
        q64 m (A + 96) L2 /\ bytes_at rsegs m L2 ls2 /\ length ls2 = 6%nat /\
        bytes_at rsegs m (phi + 6) rs2 /\ length rs2 = 6%nat /\ SF.memcmp_model ls2 rs2 6 = Some 0 /\
        addressable m L2 6 /\ app_mem (L2 + 6) /\ app_mem (L2 + 7) /\
        (L2 + 6 <= AC.aspZ regs - BW.BCMP_WRAP_K \/ AC.aspZ regs <= L2) /\
        (L2 + 6 <= fr + 2880 \/ fr + 2920 <= L2) /\
        (L2 + 6 <= fr + 2688 \/ fr + 2688 + 38 <= L2))).
(* FRB over the spill base s1 = A and the record pointer kp = fr + 176: the range bundle of 0x82340 (F12's exit)
   to 0x8237c (F14's exits). *)
Definition FRBA (g : ghost) (j : nat) (fr phi : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  exists A, rg regs 9 A /\ 0 <= A < 2 ^ 64 /\ FRB g j fr phi A (fr + 176) regs m.
(* a Theorem Labs lane's f15_rx, guarded: the 50 record bytes at Phi with their addressability and frame placement on a long frame,
   the record buffer's post bytes (frrec, the fragment call's) with its 72 addressable bytes, the identity record's
   38 cells at fr + 2688, and, when the turn closes a record (t_rf j = 1, the only arm that runs F16's reads
   0x823e4-0x82440), the first-fragment state's have and the address check F16 makes. v1.9.0 (fuzz_ctrl.c
   v1.9.0:398-400): F16 compares the parser's address cell [fr + 256] (0x823f0-0x823f4 `ld a0,288(s1)`;
   `lhu s5,0(a0)`) with joined_byte (first, block, 9) << 8 | joined_byte (first, block, 10) (the calls 0x82414 /
   0x82438, a0 = [A+168] = fr + 2880, a1 = [A+312] = Phi + 18), after `first->have` (0x823e4-0x823ec); the
   patched image read the two address bytes from its first-fragment spills or from fragb fr + 17 / + 18. The range
   bundle of 0x8235c (F13's exit) to 0x8237c. Position 6 keeps its six inner positions: have's range, have <> 0
   (the test 0x823ec), then n's range in place of nb's, the ranges of the two joined address bytes (joined_byte 9 /
   10) in place of a0 / a1's, and the address equation with its three inner positions. *)
Definition FRX (g : ghost) (j : nat) (fr phi : Z) (m : word -> option byte) : Prop :=
  (50 <= flen g j ->
     bytes_at rsegs m phi (t_g (g_in g) j) /\ addressable m phi 50 /\ (phi + 50 <= fr \/ fr + FRAME_BYTES <= phi)) /\
  bytes_at rsegs m (fragb fr) (frrec g j fr phi) /\ addressable m (fragb fr) 72 /\
  (exists idb, length idb = 38%nat /\ LSt.rw_cells rsegs m (fr + 2688) [LCl.CB 38 idb]) /\
  addressable m (fr + 2688) 38 /\
  (t_rf (g_in g) j = 1 ->
     0 <= fs_have (fst_at (g_in g) j) < 2 ^ 64 /\ fs_have (fst_at (g_in g) j) <> 0 /\
     0 <= fs_n (fst_at (g_in g) j) < 256 /\
     0 <= joined_byte (fst_at (g_in g) j) (t_g (g_in g) j) 9 < 256 /\
     0 <= joined_byte (fst_at (g_in g) j) (t_g (g_in g) j) 10 < 256 /\
     (exists AD, u16 m (fr + 256) AD /\ 0 <= AD < 65536 /\
        AD = joined_addr (fst_at (g_in g) j) (t_g (g_in g) j))).

(* ---- Adopt 7: the sources of FRBA upstream of 0x82340, carried by range. F12 (0x82304 / 0x82308 -> 0x82340)
   builds FRB from them, from FM / f10_K ([A+312], s8 = k), from the Phi bytes under 50 <= flen, and from
   FRA (the window [fr + 2880, fr + 2920), the kp / L / L2 / Phi placements, Phi's alignment from the live
   list). *)
(* FPS: the parse struct of turn j at kp = fr + 176 ([A+280]) and its 36 bytes marked usable. The shadow stores
   0x81f94-0x81fa8 (long arm) / 0x82020-0x82034 (short arm) set S(fr) + 22 .. 25 to 0 and S(fr) + 26 to 4, so
   [fr + 176, fr + 212) is addressable (next stores 0x82cf4-0x82d10, at the end of the turn); the reac_ctrl_parse
   call with a2 = [A+280] (0x81fb4 / 0x82040 `ld a2,280(s1)`; 0x81fb8 long arm, 0x82044 short arm) writes the 36 bytes snd (ctrlparse len G) = t_B j (the
   zero struct when len < 50). The third parse call 0x82158 has a2 = 0; no store of 0x81fbc .. 0x8233c and no
   callee there (kind_name; identity_reply: fr + 256 / 272 / 304; record_sum_closes; reac_identity_ingest:
   fr + 2688; the memcpy 0x8233c: fr + 336) writes [fr + 176, fr + 212). FRB reads it under t_8819 = true (cp_hdr,
   so ctrlparse_fields): the u16 at kp + 20 = Phi's bytes 14 / 15, and the compare operands [A+112] = kp + 10
   (bytes 10 .. 15 = Phi's 0 .. 5) and [A+96] = kp + 4 (bytes 4 .. 9 = Phi's 6 .. 11) with their 6 addressable
   bytes. From 0x81fbc / 0x82048 to 0x82308. *)
Definition FPS (g : ghost) (fr : Z) (j : nat) (m : word -> option byte) : Prop :=
  pBb g fr j m /\ addressable m (fr + 176) 36.
(* F272: [A+272] = b2z (t_8819 j): 0x82018 `sd a0,272(s1)`, a0 = seqz (byte 13 - 25), after byte 12 = 0x88
   (0x81fe8) on a long frame; 0x82068 `sd zero,272(s1)` when byte 12 <> 0x88; 0x82050 `sd zero,272(s1)` on the short
   arm (t_big false). Next store 0x82848. FRB's [A+272] conjunct is its t_8819 form. From 0x82098 (long arm only)
   and 0x8215c (both arms) to 0x82308. *)
Definition F272 (g : ghost) (j : nat) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  spill regs m 272 (b2z (t_8819 (g_in g) j)).
(* RCA: the three reply cells marked usable by F9's shadow stores 0x821bc `sb a0,32(s3)` (a0 = 2: [fr + 256,
   fr + 258)), 0x821c8 `sb zero,34(s3)` ([fr + 272, fr + 280)) and 0x821d4 `sb zero,38(s3)` ([fr + 304,
   fr + 312)); next stores 0x82cf8-0x82d00. From 0x821ec to 0x82308 (0x82340 spells them out). *)
Definition RCA (fr : Z) (m : word -> option byte) : Prop :=
  addressable m (fr + 256) 2 /\ addressable m (fr + 272) 8 /\ addressable m (fr + 304) 8.
(* FS9: [A+248] = 1 - sum_ok (v1.9.0 0x82144 `snez a0,a0` / 0x82148 `sd a0,248(s1)`, the only store to that slot;
   read at 0x8246c `ld a1,248(s1)` before 0x82470 `or a0,a0,a1`; the patched image kept it in s9, which v1.9.0
   uses for sum_ok itself, FM). Adopt 10 (prover a Theorem Labs lane, the twin of image A's push-13 s4 fix): the range bundle of the
   cuts 0x82304 .. 0x82468; 0x8215c / 0x82174 / 0x82180 and f10_K (0x821ec / 0x8226c / 0x82308) spell it out. *)
Definition FS9 (g : ghost) (j : nat) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  spill regs m 248 (1 - b2z (t_sum_ok (g_in g) j)).

(* ---- F10 (a Theorem Labs lane, lib/B/Prog/Seg/F10.v, whose source is not in this delivery): the state the three F10 cuts (0x821ec, 0x8226c, 0x82308) carry
   unchanged over the reac_ctrl_identity_reply result. s2 = phi, s4 = len, s6 = 1, s8 = k, s9 = sum_ok; the FLV
   pointer spills over the named base A (= s1, FLVsp) and the frame spills [A+288] = pa = fr+256, [A+176] =
   fr+2688, [A+200] = fr+336, [A+208] = fr+2768, [A+184] = tfill, [A+248] = 1 - sum_ok, [A+312] = blk;
   reply_args of the identity_reply call. (f10_FLVsp of F10.v is the official FLVsp.) The patched image had
   tfill in s5, fr + 176 in s6, 1 - sum_ok in s9 and sum_ok in [A+288]. Positions kept: the sum-flag pair swaps
   homes (inner 7: the spill, now [A+248] = 1 - sum_ok; position 8: s9, now sum_ok), position 10 is the fill
   flag (now the spill [A+184]) and position 11 is s6 (now the constant 1). *)
Definition f10_K (g : ghost) (j : nat) (phi fr : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  g_n g < 2 ^ 26 /\ (j <= 255)%nat /\ HB m phi (flen g j) /\ LK g fr j regs m /\
  (exists A, FLVsp A fr regs m /\ 0 <= A < 2 ^ 64 /\
     q64 m (A + 288) (fr + 256) /\ q64 m (A + 176) (fr + 2688) /\
     q64 m (A + 200) (fr + 336) /\ q64 m (A + 208) (fr + 2768) /\
     q64 m (A + 248) (1 - b2z (t_sum_ok (g_in g) j)) /\
     q64 m (A + 312) (if t_big (g_in g) j then phi + 18 else 0)) /\
  rg regs 18 phi /\ rg regs 20 (flen g j) /\ rg regs 25 (b2z (t_sum_ok (g_in g) j)) /\
  rg regs 24 (t_k (g_in g) j) /\ spill regs m 184 (b2z (t_tfill (g_in g) j)) /\ rg regs 22 1 /\
  RcReply.reply_args phi (fr + 256) (fr + 272) (fr + 304) = true.

(* The three reply cells of the identity_reply post under reply_ok (B/Prog/reac_ctrl_identity_reply_c.v:91-94), with
   pa = fr+256, pp = fr+272, pn = fr+304 and the record fr := phi. *)
Definition f10_RPost (phi fr : Z) (G : list byte) (m : word -> option byte) : Prop :=
  LSt.rw_cells rsegs m (fr + 256) [LCl.CB 2 (RcReply.reply_addr G)] /\
  LSt.rw_cells rsegs m (fr + 272) [LCl.CB 8 (le8 (Z_to_bv 64 (phi + 38)))] /\
  LSt.rw_cells rsegs m (fr + 304) [LCl.CB 8 (le8 (Z_to_bv 64 (RcReply.ir_s G - 13)))].

(* ---- F31 (a Theorem Labs lane, lib/B/Prog/Seg/F31.v): the state F31 reads and passes through to F32. Phi s2, k s8, len s4,
   the spills fr+64 [A+152], blk [A+312], fr+32 [A+160], the Phi bytes, the frame. *)
Definition PT32 (g : ghost) (j : nat) (phi fr : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  rg regs 18 phi /\ rg regs 24 (t_k (g_in g) j) /\ rg regs 20 (t_len (g_in g) j) /\
  spill regs m 152 (fr + 64) /\ spill regs m 312 (if t_big (g_in g) j then phi + 18 else 0) /\
  bytes_at rsegs m phi (t_phi (g_in g) j) /\ (Z.of_nat (length (t_phi (g_in g) j)) <= flen g j) /\
  spill regs m 160 (fr + 32) /\
  stk rsegs m fr (fr + FRAME_BYTES).

(* ---- F33 (a Theorem Labs lane, lib/B/Prog/Seg/F33.v): the row-loop pass-through PTL and the row-loop state RL (shared with
   F34 / F35 / F36). Phi s2, len s4, fr+64 [A+152], Phi+18 [A+312], fr+32 [A+160] with the count 11 at fr+32.
   (aspZ <= APPMEM_END dropped: push-5 FRA gives it.) *)
Definition PTL (g : ghost) (j : nat) (phi fr : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  t_rowsel (g_in g) j = true /\
  rg regs 18 phi /\ rg regs 20 (t_len (g_in g) j) /\ spill regs m 152 (fr + 64) /\ spill regs m 312 (phi + 18) /\
  bytes_at rsegs m phi (t_phi (g_in g) j) /\ (Z.of_nat (length (t_phi (g_in g) j)) <= flen g j) /\
  spill regs m 160 (fr + 32) /\ q64 m (fr + 32) 11 /\
  stk rsegs m fr (fr + FRAME_BYTES).
Definition RL (g : ghost) (j i : nat) (phi fr : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  (i <= 10)%nat /\ rg regs 23 (CAT + CAT_ROW * Z.of_nat i) /\ rg regs 25 (Z.of_nat i) /\ rg regs 21 CAT /\
  rg regs 10 (CAT_ROW * Z.of_nat i) /\ rg regs 11 0 /\ rg regs 12 0 /\
  (forall i', (i' < i)%nat -> t_blk (g_in g) j <> decl_i (Z.of_nat i')) /\ PTL g j phi fr regs m.
(* RLc (prover a Theorem Labs lane, lib/B/Prog/Seg/F34.v on a working branch 44ac51d3f4, verbatim): row i of row_of_block at the
   return point 0x82c24 of declaration_of (W03, i = 0 .. 10), carried on to 0x82c38: RL without the row head's three
   overflow-check operands (a0 is the call's result, a1 and a2 are gone), with the row pointer now in both s7 and
   the checked sum s8 (0x82c08 add s8,a0,s5; F36's `bnez s8` at 0x82c38 reads it, trap row T72), and the row slot
   fr + 64 in s6 (0x82c18 ld s6,152(s1); F35's `mv a1,s6` at 0x82c30). *)
Definition RLc (g : ghost) (j i : nat) (phi fr : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  (i <= 10)%nat /\ rg regs 23 (CAT + CAT_ROW * Z.of_nat i) /\ rg regs 24 (CAT + CAT_ROW * Z.of_nat i) /\
  rg regs 25 (Z.of_nat i) /\ rg regs 21 CAT /\ rg regs 22 (fr + 64) /\
  (forall i', (i' < i)%nat -> t_blk (g_in g) j <> decl_i (Z.of_nat i')) /\ PTL g j phi fr regs m.

(* ---- F26 / F27 (a Theorem Labs lane, lib/B/Prog/Seg/F27.v): F27K the check_ports window state (LK, s2 = phi, s11 = -8, the
   32 block bytes, blk [A+312], k [A+272], sum_ok in s8 (v1.9: F23's 0x8284c mv s8,s9), the ports pointer fr+128
   [A+104], the first pointer fr+160 [A+136]). *)
Definition F27K (g : ghost) (j : nat) (phi fr : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  LK g fr j regs m /\ rg regs 18 phi /\ rg regs 27 (-8) /\
  0 < phi /\ phi + 50 <= 2 ^ 64 /\ 50 <= flen g j /\
  bytes_at rsegs m (phi + 18) (t_blk (g_in g) j) /\
  spill regs m 312 (phi + 18) /\ spill regs m 272 (t_k (g_in g) j) /\
  rg regs 24 (b2z (t_sum_ok (g_in g) j)) /\
  spill regs m 104 (fr + 128) /\ spill regs m 136 (fr + 160).

(* ---- A region (plan 3.3): the pre-frame cuts carry no FRA (the frame is not built yet); the FRA cuts start at
   A4 (0x81220) after the 392 shadow bytes are written. A1's request cut and A2/A3 are the asan-only entry cuts. *)

(* Pre-frame subset of FRA (fr-independent; threaded through the A2 and A3 cuts so A3 assembles FRA with sl_fr_of,
   fix a1.4): the asan runtime at sp, the heap and runtime cells, the spill base A = s1 and entry sp S = s0, gp / tp /
   s10 = K, the slot window and errno writable, the 13 saved caller registers, the stack-low bound and alignments.
   Push 5c adds FRA's frame-independent additions: the whole slot window addressable (no frame shadow is written
   yet before A3's poisoning run, so the entry pre's addressability still holds of the whole window; the FRA form
   excludes the frame) and the three ENTRY stack-top facts. PREF also carries FRA's input facts (the input bytes at
   p and, for n > 0, the block (p, n) live and addressable), which the entry pre gives and A3 hands to sl_fr_of. *)
Definition PREF (g : ghost) (A sp : Z) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop :=
  AsanRTInv.RT sp mem md /\
  AC.aa_AH AC.ASYMS AsanRTInv.RT API (g_H g) mem md /\
  ro_agree rsegs mem /\ sink_none B mem md /\ m_halted md = None /\ G_img_c B AF.frame_RELRO mem /\
  getr regs 2 = Z_to_bv 64 sp /\ sp mod 16 = 0 /\ AC.aspZ regs = sp /\
  AC.aa_stklo AC.ASYMS AsanRTInv.RT API mem md <= g_S g - AF.SLOT_STACK /\
  getr regs 4 = Z_to_bv 64 (AC.as_tp AC.ASYMS) /\
  rg regs 8 (g_S g) /\ rg regs 9 A /\ getr regs 3 = getr (g_regs g) 3 /\ rg regs 26 ASAN_K /\
  A mod 32 = 0 /\ A <= g_S g /\ g_S g - 464 <= A /\ sp <= A /\ A + 448 <= g_S g /\
  g_S g - 4096 < sp /\ g_S g < APPMEM_END /\
  stk rsegs mem (g_S g - AF.SLOT_STACK) (g_S g) /\
  bytes_at rsegs mem (g_S g - 104) (saved_bytes g) /\
  (forall a, AC.a_errno AC.ASYMS <= a < AC.a_errno AC.ASYMS + 4 -> writable_at rsegs mem a) /\
  (forall a, in_globals AF.frame_AG a -> addressable mem a 1) /\
  (forall a, g_S g - AF.SLOT_STACK <= a < g_S g -> addressable mem a 1) /\
  g_S g <= AC.aa_stkhi AC.ASYMS AsanRTInv.RT API (g_mem g) (g_md g) /\
  AC.aa_stkhi AC.ASYMS AsanRTInv.RT API (g_mem g) (g_md g) <= APPMEM_END /\
  (forall a, g_S g <= a < AC.aa_stkhi AC.ASYMS AsanRTInv.RT API (g_mem g) (g_md g) ->
     exists b, mbyte rsegs (g_mem g) a = Some b) /\
  g_n g <= AC.ANMAX /\
  AC.a_live_bytes (g_H g) <= 5 * 2 ^ 30 /\
  bytes_at rsegs mem (g_p g) (g_in g) /\ (0 < g_n g -> In (g_p g, g_n g) (g_H g) /\ addressable mem (g_p g) (g_n g)).

(* A2 (0x81090): the arm selection, at the `mv s8,a0` that takes the frame request's result r in a0 (0 = no side
   frame, else the side frame's base, 32-aligned and in FS above the FakeStack metadata); the pre-frame subset
   threaded (fix a1.4), with the input pointer s6 = p and size s2 = n of 0x8107c / 0x81060. ENT is threaded from
   A1 on (push 5c): the frame request is a callee run, so ent_call / ent_store carry the entry relation across it,
   and A3 hands it to the first FRA cut unchanged. *)
(* v1.9 pc 0x81090 *)
Definition Inv_B81090 (g : ghost) (c : config) : Prop :=
  exists regs mem md A r,
    c = mkCfg (mkst regs (Z_to_bv 64 0x81090) mem (seg_rom segs)) md /\
    PREF g A A regs mem md /\ ENT g [] mem md /\ rg regs 10 r /\ 0 <= r < 2 ^ 64 /\
    rg regs 22 (g_p g) /\ rg regs 18 (g_n g) /\
    (r = 0 \/ (r mod 32 = 0 /\
       (forall FS, word_mem rsegs mem (AC.as_tp AC.ASYMS) FS -> 0 <= FS < 2 ^ 64 -> FS + 6328320 <= r) /\
       (forall a, r <= a < r + FRAME_BYTES -> AC.a_in_fs AC.ASYMS mem a) /\ FSREC r mem)).

(* A3 (0x810c4): the side-arm join (0x810a0 bnez s8,0x810c4); fr fixed, about to write the header and the 392 shadow
   bytes. The pre-frame subset threaded (fix a1.4) plus fr (v1.9.0 in s9; patched s7) and the frame-location
   disjunction, told apart by s8 (real arm s8 = 0, sp lowered to fr; side arm s8 = fr, sp = A). No s3 = S(fr) yet
   (set at 0x810d4 / 0x810fc, fix a1.5). fr + 3136 <= A, which FRAS needs at A4: real arm fr = (A - 3136) & -32
   (0x810a4-0x810ac with sp = A); side arm the frame is in FS, below stklo <= S - SLOT_STACK < A. *)
(* v1.9 pc 0x810c4 *)
Definition Inv_B810c4 (g : ghost) (c : config) : Prop :=
  exists regs mem md A fr sp s8,
    c = mkCfg (mkst regs (Z_to_bv 64 0x810c4) mem (seg_rom segs)) md /\
    PREF g A sp regs mem md /\ ENT g [] mem md /\ rg regs 25 fr /\ fr mod 32 = 0 /\ rg regs 24 s8 /\ 0 <= fr < 2 ^ 64 /\ fr + FRAME_BYTES <= A /\
    (s8 = 0 \/ s8 = fr) /\ rg regs 22 (g_p g) /\ rg regs 18 (g_n g) /\
    ((s8 = 0 /\ sp = fr /\ (forall a, fr <= a < fr + FRAME_BYTES ->
        AC.aa_stklo AC.ASYMS AsanRTInv.RT API mem md <= a < APPMEM_END)) \/
     (s8 = fr /\ sp = A /\
        (forall FS, word_mem rsegs mem (AC.as_tp AC.ASYMS) FS -> 0 <= FS < 2 ^ 64 -> FS + 6328320 <= fr) /\
        (forall a, fr <= a < fr + FRAME_BYTES -> AC.a_in_fs AC.ASYMS mem a) /\ FSREC fr mem)).

(* A4 (0x81220): first FRA cut, taken on FRAS because the selector is not spilled to [A + 48] until 0x815a8 (in the
   A5 / R1 segments); the size test 0x81424-0x8144c is in this segment (fall-through n < 2^26 to A5, branch
   n >= 2^26 to Jrel by slot_early with the selector in register 24 only). Register pins: every callee-saved
   register seg_A4 (0x81220-0x81544) and the cuts after it read, all set before the call at 0x8121c -- s4 = -8
   and s5 = -14 (0x810dc / 0x810d8, the 64-bit two's complements), s8 = the selector (0x81090 / 0x81098), s9 = fr
   (0x8109c / 0x810ac; patched s7), s6 = p (0x8107c, read by A5 at 0x8154c), s2 = n (0x81060), s11 = S(fr) + 68
   (0x81210 addi s11,s3,68; read by R2 at 0x81634 / 0x81638; patched s9). s3 = S(fr) is already in FRAS. *)
(* v1.9 pc 0x81220 *)
Definition Inv_B81220 (g : ghost) (c : config) : Prop :=
  CUTST0 g 0x81220 [] (fun fr sel regs _ =>
    g_n g <= AC.ANMAX /\
    rg regs 20 (-8) /\ rg regs 21 (-14) /\ rg regs 24 sel /\ rg regs 25 fr /\
    rg regs 22 (g_p g) /\ rg regs 18 (g_n g) /\ rg regs 27 (Sfr fr + 68)) c.
(* A5 (0x81548): the our[] loop head, turn t (0 <= t <= 5). FRAS, since the loop exit stores fr to [A + 40]
   (0x815ac sd s9,40(s1)) and the selector to [A + 48] (0x815a8 sd s8,48(s1)), both from registers. The
   identity / fragment record pointers [A + 144] = fr + 2176 and [A + 112] = fr + 2256 are spilled in A4
   (0x81534 sd a3,144(s1) / 0x814c0 sd a1,112(s1), a3 = fr + 2176 from 0x814b4) and read at R3 / R4. Also spilled
   in A4 (a Theorem Labs lane): [A + 312] = fr + 544 (0x814a4 addi a0,s9,544 / 0x814a8 sd a0,312(s1)) and [A + 264] = fr + 2624
   (0x814f4 addi a2,a3,448 / 0x81544 sd a2,264(s1)), the build_as arguments R6 reads; and s4 = fr + 2656
   (0x814f8 addi s4,a3,480), the catalogue's output cell, which no instruction up to R2 rewrites (a Theorem Labs lane). *)
(* The code-byte pointer fr + 3040 (v1.9.0's `code`; patched fr + 2960 in s11) is the spill [A + 56] from A4 on
   (0x8152c addi a1,a3,864 / 0x81530 sd a1,56(s1)); R1's tail reloads it into s8 (0x815e4 ld s8,56(s1)) for R2
   only, and P2 reloads it at 0x81cac (`ld s8,56(s1)`) for P3-P11 (XC); the R region uses s8 as the -8 poison
   constant from 0x816d0.
   our[]'s six bytes are addressable from A4 on (prover a Theorem Labs lane): the shadow store 0x814b8 `sb a0,328(s3)` (a0 = 6 from
   0x814b0) marks the granule S(fr) + 328 and nothing up to the epilogue 0x82f14 writes it, so A5, R1-R4 carry
   it. R3 and R4 also carry the catalogue row s2 = mrow (0x8162c add s2,a0,a1 in R2's segment; R3 / R4 do not
   write s2). The B3 spills [A + 96] = decl_slot fr (0x814f0 sd a1,96(s1)) and [A + 120] = fr + 2528 (0x814e8
   sd a1,120(s1)) are set in A4 and not stored again before the frame-loop prologue (0x81e70 / 0x81e90), so A5 and
   R1-R5 carry them and RBE holds them in the loop (prover a Theorem Labs lane, adopt 5). The same holds for the three reply-slot
   spills [A + 240] = fr + 2448, [A + 232] = fr + 2464 and [A + 224] = fr + 2496 (0x814cc-0x814e0: addi a1,a3,272 /
   sd a1,240(s1), addi a1,a3,288 / sd a1,232(s1), addi a1,a3,320 / sd a1,224(s1), a3 = fr + 2176; next stores
   0x81f40 / 0x81f44 / 0x81f60 in the frame loop), which R10 (0x817dc-0x817e4), R11 (0x81840-0x81850) and R15
   (0x81904-0x8190c) read (prover a Theorem Labs lane, lib/B/Prog/Seg/R11.v (not in this delivery) on a working branch b0de306812).
   LOOPB (prover a Theorem Labs lane, seg_A5 + seg_R1 Qed on a working branch e316ddb751, lib/B/Prog/Seg/A5.v, verbatim) is
   the loop body every turn carries: the facts above (our[] as the first t OUR bytes followed by 6 - t unread
   bytes, which the store at turn t replaces), plus the loop registers of turn t, all set in A4 and rewritten only
   by the loop: a0 = 6 - t (0x814b0 li a0,6; the store count, 0x81580), a1 = 1 (0x81540, the T01 constant),
   a2 = fr + 2624 + t (0x814f4 addi a2,a3,448; the store pointer, 0x81584), a7 = fr + 64 (0x81458 addi a7,s9,64;
   spilled to [A + 152] at 0x815a0) and a6 = fr + 32 (0x81454 addi a6,s9,32; spilled to [A + 160] at 0x815a4;
   the patched A4 spilled it at once, 0x81400), s2 = left = n - min t n (0x81060 / 0x8156c) and s6 = cursor = p +
   min t n (0x8107c / 0x81570), s11 = S(fr) + 68 (0x81210; R2's cut reads it); the record spills [A + 176] =
   fr + 2688 and [A + 208] = fr + 2768 (0x81500 / 0x81508); and the input block's bytes and, when n > 0, that it
   is a live entry block and addressable (the cursor's shadow check 0x81560 and the mode byte's 0x815cc).
   Positions: the v1.8 positions are kept (position 17, the patched code-byte pointer s11 = fr + 2960, is now the
   spill [A + 56] = fr + 3040); a6 = fr + 32 is new in v1.9.0 and is position 31. *)
Definition LOOPB (g : ghost) (t fr sel : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
    g_n g < 2 ^ 26 /\ 0 <= t <= 5 /\ rg regs 24 sel /\ rg regs 25 fr /\
    spill regs m 144 (fr + 2176) /\ spill regs m 112 (fr + 2256) /\
    spill regs m 312 (fr + 544) /\ spill regs m 264 (fr + 2624) /\ rg regs 20 (fr + 2656) /\
    rg regs 10 (6 - t) /\ rg regs 11 1 /\ rg regs 12 (fr + 2624 + t) /\ rg regs 17 (fr + 64) /\
    rg regs 18 (g_n g - Z.min t (g_n g)) /\ rg regs 22 (g_p g + Z.min t (g_n g)) /\ rg regs 27 (Sfr fr + 68) /\
    spill regs m 56 (fr + 3040) /\ spill regs m 184 (fr + 2368) /\
    spill regs m 176 (fr + 2688) /\ spill regs m 208 (fr + 2768) /\ addressable m (fr + 2624) 6 /\
    spill regs m 96 (decl_slot fr) /\ spill regs m 120 (fr + 2528) /\
    spill regs m 240 (fr + 2448) /\ spill regs m 232 (fr + 2464) /\ spill regs m 224 (fr + 2496) /\
    spill regs m 64 (fr + 3056) /\
    bytes_at rsegs m (g_p g) (g_in g) /\
    (0 < g_n g -> In (g_p g, g_n g) (g_H g) /\ addressable m (g_p g) (g_n g)) /\
    (exists junk, length junk = Z.to_nat (6 - t) /\
       bytes_at rsegs m (fr + 2624) (firstn (Z.to_nat t) (OUR (g_in g)) ++ junk)) /\
    rg regs 16 (fr + 32).
(* Adopt 9: A5 and R1 carry PRA (A4's 0x81460-0x81510) next to LOOPB. *)
(* v1.9 pc 0x81548 *)
Definition Inv_B81548_at (g : ghost) (t : Z) (c : config) : Prop :=
  CUTST0 g 0x81548 [] (fun fr sel regs m => LOOPB g t fr sel regs m /\ PRA fr regs m) c.
(* v1.9 pc 0x81548 *)
Definition Inv_B81548 (g : ghost) (c : config) : Prop := exists t, Inv_B81548_at g t c.

(* ---- Round trip (R1-R21), turn b : nat. R1 is the catalogue setup; R7 malloc gains the buffer Phi_r, R20 free
   drops it. The image-B twins of the lib/A cuts (cut list: plan-asan-ubsan 3.3, checked against the A->B call map),
   with the registers pinned to image B: b in s6 (reg 22), the cursor / left in s7 / s9 (CUR), Phi_r in s4. *)
(* R1 (0x81550): after the our[] loop head's left test (0x81548 beqz s2,81578), on each turn with left <> 0; mode is
   not yet read here, so the round-trip facts start at R2. Image A's R1 (0x813e4) is the head of an A-only
   zero-fill loop; image B fills the our[] tail inside the A5 loop (0x81578). FRAS like A5: the R1 segment runs to
   the loop exit 0x815a0 and the stores 0x815a0-0x815ac of fr + 64 (a7), fr + 32 (a6), the selector (s8) and fr
   (s9). Prover a Theorem Labs lane's body: the
   head's state of turn t after the head's test fell through (left > 0, so t < n) and 0x8154c computed the bumped
   cursor a3 = p + t + 1. *)
(* v1.9 pc 0x81550 *)
Definition Inv_B81550_at (g : ghost) (t : Z) (c : config) : Prop :=
  CUTST0 g 0x81550 [] (fun fr sel regs m =>
    LOOPB g t fr sel regs m /\ PRA fr regs m /\ t < g_n g /\ rg regs 13 (g_p g + t + 1)) c.
(* v1.9 pc 0x81550 *)
Definition Inv_B81550 (g : ghost) (c : config) : Prop := exists t, Inv_B81550_at g t c.
(* R2 (0x815fc): the catalogue result; the shadow-fill call at 0x8163c takes a0 = s11 = S(fr) + 68 (0x81210 addi
   s11,s3,68; 0x81638 mv a0,s11), which is still in its register here (spilled to [A + 8] at 0x81634, after this
   cut). CUR g 7 from 0x815b4 addi s7,s6,1 / 0x815e0 addi s9,s2,-1; the A4 spills [A + 144] / [A + 112]. The
   code-byte pointer is the spill [A + 56] (the patched R2 saved s11 to [A + 24] at 0x815a8; v1.9.0 has no such
   store, and s8 = fr + 3040 from 0x815e4 is dead here).
   s4 = fr + 2656 (callee-saved across the catalogue call 0x815f8, which got a0 = s4 after 0x815f0 sd zero,0(s4))
   and the count the catalogue's post writes there (reac_box_catalogue_c.v: le8 11 = CAT_N at c <> 0), which R2
   reads at 0x81604 (ld a1,0(s4)): the abort branch 0x8160c is not taken and 0x81614 divides by CAT_N (a Theorem Labs lane).
   s6 = mode (prover a Theorem Labs lane, the twin of image A's rg regs 23 (mode) on Inv_A814f8): set by the R1 tail 0x815d8
   lbu s6,0(s6) (s6 = p + 6 there, 7 <= n) and not written again before 0x815fc (the catalogue call keeps the s
   registers); R2 forms s2 = mrow from it (0x81610 srli a2,s6,1, 0x81614 remu, 0x8161c mul, 0x8162c add s2,a0,a1). *)
(* v1.9 pc 0x815fc *)
Definition Inv_B815fc (g : ghost) (c : config) : Prop :=
  CUTST g 0x815fc [] (fun fr regs m => g_n g < 2 ^ 26 /\ a0v regs CAT /\ OURb g fr m /\
    rg regs 27 (Sfr fr + 68) /\ CUR g 7 regs /\ spill regs m 144 (fr + 2176) /\ spill regs m 112 (fr + 2256) /\
    spill regs m 312 (fr + 544) /\ spill regs m 264 (fr + 2624) /\
    rg regs 20 (fr + 2656) /\ q64 m (fr + 2656) CAT_N /\ spill regs m 56 (fr + 3040) /\
    spill regs m 184 (fr + 2368) /\ addressable m (fr + 2624) 6 /\
    spill regs m 96 (decl_slot fr) /\ spill regs m 120 (fr + 2528) /\
    spill regs m 240 (fr + 2448) /\ spill regs m 232 (fr + 2464) /\ spill regs m 224 (fr + 2496) /\
    spill regs m 176 (fr + 2688) /\ spill regs m 208 (fr + 2768) /\ spill regs m 64 (fr + 3056) /\
    PRA fr regs m /\ spill regs m 152 (fr + 64) /\
    rg regs 22 (mode (g_in g)) /\
    spill regs m 160 (fr + 32)) c.
(* R3 (0x81640): the identity-record init call at 0x81688 takes a0 = [A + 144] = fr + 2176 (0x814b4 addi a3,a1,129
   with a1 = s9 + 2047; 0x81534 sd a3,144(s1); 0x81684 ld a0,144(s1)), the identity buffer IDBr sits on; R4's
   memset reads [A + 112]. *)
(* v1.9 pc 0x81640 *)
Definition Inv_B81640 (g : ghost) (c : config) : Prop :=
  CUTST g 0x81640 [] (fun fr regs m => g_n g < 2 ^ 26 /\ CUR g 7 regs /\ OURb g fr m /\
    spill regs m 144 (fr + 2176) /\ spill regs m 112 (fr + 2256) /\
    spill regs m 312 (fr + 544) /\ spill regs m 264 (fr + 2624) /\ spill regs m 56 (fr + 3040) /\
    spill regs m 184 (fr + 2368) /\ addressable m (fr + 544) 1488 /\ spill regs m 8 (Sfr fr + 68) /\
    rg regs 18 (mrow (g_in g)) /\ addressable m (fr + 2624) 6 /\
    spill regs m 96 (decl_slot fr) /\ spill regs m 120 (fr + 2528) /\
    spill regs m 240 (fr + 2448) /\ spill regs m 232 (fr + 2464) /\ spill regs m 224 (fr + 2496) /\
    spill regs m 176 (fr + 2688) /\ spill regs m 208 (fr + 2768) /\ spill regs m 64 (fr + 3056) /\
    PRA fr regs m /\ spill regs m 152 (fr + 64) /\ spill regs m 160 (fr + 32)) c.
(* OUTA (image A push 6a, a Theorem Labs lane): out[]'s 1492 bytes at fr + 544 are addressable. The R3 fill (0x8163c
   meta_fill_00, 186 shadow bytes) and the R4 store 0x81658 make them so before the b loop, and no instruction in
   0x816ec-0x81ac8 stores to their shadow bytes S(fr) + 68 .. S(fr) + 254 (the loop's direct shadow stores are at
   296..323(s3): 0x8177c-0x81790, 0x817a8-0x817b0, 0x81870 / 0x81874, 0x81a34-0x81a40, 0x81a70-0x81a84,
   0x81aa0-0x81abc). *)
Definition OUTA (fr : Z) (m : word -> option byte) : Prop := addressable m (fr + 544) 1492.

(* RBE (prover a Theorem Labs lane, read off 0x816ec-0x81ac8 of the listing: no instruction in that range stores to (s1),
   so every spill the loop head 0x816ec carries holds at each R cut and the R6 back edge 0x81ac8 re-establishes
   it): the magic word [A+128] = 0xe38f0000 (0x816c4 / 0x816e4 / 0x816e8, read 0x8173c), the copy source
   [A+312] = fr + 544 (0x814a8), the catalogue row pointer [A+272] = mrow (0x816b0 / read 0x816f0), the our[] pointer
   [A+264] = fr + 2624 (0x81544), [A+256] = 0x21140 (0x816d4 / 0x816d8) and [A+248] = 0x1234
   (0x816dc / 0x816e0), the code-byte pointer [A+56] = fr + 3040 (A4's 0x81530, the only store to that slot;
   P2 reloads it at 0x81cac for the P region's XC), and, for R7's n_b = 0 arm and the loop
   tail (prover a Theorem Labs lane, seg_R6), the identity-record pointer [A+144] = fr + 2176 (0x81534 sd a3,144(s1); next store
   0x81e9c in the frame-loop prologue) and the frame-shadow pointer [A+8] = S(fr) + 68 (0x81634 sd s11,8(s1),
   the only store to that slot; read by P1 at 0x81ca0). Prover a Theorem Labs lane, adopt 5: R5's [A+32] = mrow mod 8 = 0
   (0x816a0 andi a0,s2,7 / 0x816a4 sd a0,32(s1), the only store to that slot; s2 = mrow and CAT, CAT_ROW = 296
   are multiples of 8; read by the ubsan check at 0x81b10 ld a0,32(s1), after the loop exit), and the B3 spills,
   set before the loop:
   the catalogue-row fields [A+24] = mrow + 16 (0x816a8 addi a0,s2,16 / 0x816ac sd a0,24(s1)) and
   [A+16] = mrow + 20 (0x816b4 addi s2,s2,20 / 0x816b8 sd s2,16(s1)), the only stores to those slots, the
   declaration slot [A+96] = decl_slot fr (0x814ec addi a1,a3,384 / 0x814f0 sd a1,96(s1); next store 0x81e90 in
   the frame-loop prologue) and the ports buffer [A+120] = fr + 2528 (0x814e4 addi a1,a3,352 / 0x814e8 sd
   a1,120(s1); next store 0x81e70), with a3 = fr + 2176 (0x814b4 addi a3,a1,129, not rewritten up to 0x81534).
   Prover a Theorem Labs lane (seg_R6, lib/B/Prog/Seg/R6.v on a working branch 96ceb6489e, Inv_B81688_loc): the row-name
   clause, a fact the loop does not change, so RBE carries it to the latch: when the catalogue row names a row
   name, its bytes and placement (R6X states the same clause only on the identity turns b = 5 / 6). a Theorem Labs lane's second
   loop fact (out[] apart from the thread cells of the side stack, fp_tls) is not carried: it follows from FRA alone
   at every cut (Seg/Tac_fsfree.v tls_fra / fra_rbe_tls, also prover a Theorem Labs lane's r13_tls_fra on a working branch
   6a3ed3e194: the thread cells are image cells below GT, or the allocator's bytes, or below stklo and outside FS,
   and no frame byte is any of those). Adopt FSFREE: RBE also carries
   R6X's loop-invariant facts - our[] addressable (no loop store to its shadow granule 328(s3), see R5), the row
   table at BA_FR + 72, the box bytes at BOXA and the catalogue row at mrow (image bytes; no loop store is below
   GT) - so R6X at any turn, in particular R6X g (S b) at R21's back edge, follows from RBE (r6x_of_rbe).
   Prover a Theorem Labs lane (seg_R11, lib/B/Prog/Seg/R11.v (not in this delivery) on a working branch b0de306812): the three reply-slot spills
   [A + 240] = fr + 2448, [A + 232] = fr + 2464, [A + 224] = fr + 2496 (A4's 0x814d0 / 0x814d8 / 0x814e0; no loop
   store to (s1); read 0x817dc-0x817e4, 0x81824-0x8182c, 0x81840-0x81850, 0x81904-0x8190c), and the identity
   record fr + 2176 addressable for 38 bytes (R3's shadow stores 0x8165c-0x8166c `sb zero,272..275(s3)` /
   `sb a1,276(s3)` with a1 = 6; no store to 272..276(s3) in 0x81670-0x81ac8; read by the ingest call 0x8185c).
   Adopt 9: RBE also carries PRA, [A+152] = fr + 64 and [A+160] = fr + 32 (0x815a0 / 0x815a4), PRO's spills that
   its other conjuncts lack (no store to (s1) in 0x816ec-0x81ac8), so PRO holds at every R cut from R6 on and at
   the latch; and (prover a Theorem Labs lane, seg_R10) the fragment-record pointer [A+112] = fr + 2256 (A4's 0x814c0, the only
   store before the frame-loop prologue's 0x81e88), which R10's fragment arms reload at 0x81818 / 0x818f8. Adopt
   10 (prover a Theorem Labs lane's R9 chain, a working branch be153b10cd): the fragment record fr + 2256 addressable for 72
   bytes (R4 / R5's entry facts; the only shadow stores in 0x816ec-0x81ac8 are 296..300 / 306 / 308 / 312 / 316 /
   317 / 320..323(s3), none in the record's granules 282..290), which R9's exit Inv_B817a4_at asks for. *)
Definition RBE (g : ghost) (fr : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  spill regs m 128 0xe38f0000 /\ spill regs m 312 (fr + 544) /\ spill regs m 272 (mrow (g_in g)) /\
  spill regs m 264 (fr + 2624) /\ spill regs m 256 0x21140 /\ spill regs m 248 0x1234 /\
  spill regs m 56 (fr + 3040) /\ spill regs m 184 (fr + 2368) /\
  spill regs m 144 (fr + 2176) /\ spill regs m 8 (Sfr fr + 68) /\
  spill regs m 32 0 /\ spill regs m 24 (mrow (g_in g) + 16) /\ spill regs m 16 (mrow (g_in g) + 20) /\
  spill regs m 96 (decl_slot fr) /\ spill regs m 120 (fr + 2528) /\
  spill regs m 240 (fr + 2448) /\ spill regs m 232 (fr + 2464) /\ spill regs m 224 (fr + 2496) /\
  spill regs m 176 (fr + 2688) /\ spill regs m 208 (fr + 2768) /\ spill regs m 64 (fr + 3056) /\
  OUTA fr m /\ addressable m (fr + 2176) 38 /\
  (RS6.has (rt_mb (g_in g)) <> 0 /\ RS6.rname (rt_mb (g_in g)) <> 0 ->
     RBx.name_ok (rt_nb (g_in g)) /\ bytes_at rsegs m (RS6.rname (rt_mb (g_in g))) (rt_nb (g_in g)) /\
     addressable m (RS6.rname (rt_mb (g_in g))) (Z.of_nat (length (rt_nb (g_in g)))) /\
     0 < RS6.rname (rt_mb (g_in g)) /\
     RS6.rname (rt_mb (g_in g)) + Z.of_nat (length (rt_nb (g_in g))) <= AC.GT) /\
  addressable m (fr + 2624) 6 /\ bytes_at rsegs m (BAC.BA_FR + 72) BAP.ba_tbl /\ bytes_at rsegs m BOXA box6 /\
  bytes_at rsegs m (mrow (g_in g)) (rt_mb (g_in g)) /\
  PRA fr regs m /\ spill regs m 152 (fr + 64) /\ spill regs m 112 (fr + 2256) /\ addressable m (fr + 2256) 72 /\
  spill regs m 160 (fr + 32).

(* R6X (prover a Theorem Labs lane, the XB set of his local cut Inv_B81688_loc, in lib/B/Prog/Seg/R6.v (a version not in this delivery)): what
   the reac_ctrl_build_as call at 0x8170c needs and FRA does not give. The out[] buffer fr + 544 (1492 bytes) and
   our[] fr + 2624 (6 bytes) are frame variables, whose addressability FRA carries only as the frame's 392 shadow
   bytes; the row table at BA_FR + 72, the box bytes at BOXA and the catalogue row at mrow are image bytes, and
   FRA's image agreement is RELRO-only; the row name's bytes and name_ok are needed on the identity turns b = 5
   and b = 6. The call's side-stack package (fp [0; 1] with W = r6_W, D = r6_D, reac_ctrl_build_as_tls, the frame
   and its shadow apart from fp_w [0; 1]) is NOT carried: the call site rebuilds it from FRA (Seg/Tac_fsfree.v
   fra_fp; adopt FSFREE). Of a Theorem Labs lane's XB this drops `mem_inv rsegs m` (MemNorm.evt_normalize gives it from ro_agree,
   push 5c) and the callee window's addressability (FRA's entry-anchored window gives it). Every conjunct is also
   one of RBE's (r6x_of_rbe below). *)
Definition r6_W (g : ghost) (b : nat) (fr S : Z) : list ivl :=
  [(S - BAC.REAC_CTRL_BUILD_AS_K, S); (fr + 544, fr + 544 + rnb g b)].
Definition r6_D (g : ghost) (b : nat) (fr : Z) : list ivl :=
  [(BAC.BA_FR + 72, BAC.BA_FR + 240); (mrow (g_in g), mrow (g_in g) + 296);
   (fr + 2624, fr + 2624 + 6); (BOXA, BOXA + 6); (fr + 544, fr + 544 + rnb g b)].
Definition R6X (g : ghost) (b : nat) (fr : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  addressable m (fr + 544) 1492 /\
  addressable m (fr + 2624) 6 /\
  bytes_at rsegs m (BAC.BA_FR + 72) BAP.ba_tbl /\
  bytes_at rsegs m BOXA box6 /\
  bytes_at rsegs m (mrow (g_in g)) (rt_mb (g_in g)) /\
  ((Z.of_nat b = 5 \/ Z.of_nat b = 6) /\ RS6.has (rt_mb (g_in g)) <> 0 /\ RS6.rname (rt_mb (g_in g)) <> 0 ->
     RBx.name_ok (rt_nb (g_in g)) /\ bytes_at rsegs m (RS6.rname (rt_mb (g_in g))) (rt_nb (g_in g)) /\
     addressable m (RS6.rname (rt_mb (g_in g))) (Z.of_nat (length (rt_nb (g_in g)))) /\
     0 < RS6.rname (rt_mb (g_in g)) /\
     RS6.rname (rt_mb (g_in g)) + Z.of_nat (length (rt_nb (g_in g))) <= AC.GT).

(* R6X at any turn from RBE (adopt FSFREE): RBE carries every conjunct of R6X; R6X's row-name clause is RBE's
   restricted to the identity turns. *)
Lemma r6x_of_rbe : forall g b fr regs m, RBE g fr regs m -> R6X g b fr regs m.
Proof.
  intros g b fr regs m H.
  destruct H as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HOUT & _ & Hrow &
    Hour & Htbl & Hbox & Hmrow & _).
  unfold R6X, OUTA in *. split; [exact HOUT|]. split; [exact Hour|]. split; [exact Htbl|]. split; [exact Hbox|].
  split; [exact Hmrow|]. intros (_ & Hh). exact (Hrow Hh).
Qed.

(* R4 (0x8168c) / R5 (0x8169c): the b = 0 straight line. Turn state of the ubsan twins R03/R04 (CUR, our[], the
   identity and fragment records of turn 0); R4's memset at 0x81698 takes the fragment record address spilled at
   [A + 112] (0x814c0 sd a1,112(s1), a1 = a3 + 80 = fr + 2256 = FGBr's base; 0x81690 ld a0,112(s1)) and fills its
   72 bytes, so at R4 the record bytes are only addressable; FGBr first holds at R5. Adopt FSFREE: the build_as
   side-stack package (prover a Theorem Labs lane's R4X) is no longer carried here; the R6 call site rebuilds it from FRA
   (Seg/Tac_fsfree.v fra_fp), so R3 (which has no allocator call) need not create one. *)
(* v1.9 pc 0x8168c *)
Definition Inv_B8168c (g : ghost) (c : config) : Prop :=
  CUTST g 0x8168c [] (fun fr regs m => g_n g < 2 ^ 26 /\ CUR g 7 regs /\ OURb g fr m /\
    IDBr g fr (RID (g_in g) 0) m /\ addressable m (fr + 2256) 72 /\ spill regs m 112 (fr + 2256) /\
    spill regs m 312 (fr + 544) /\ spill regs m 264 (fr + 2624) /\ spill regs m 56 (fr + 3040) /\
    spill regs m 184 (fr + 2368) /\ addressable m (fr + 544) 1492 /\ addressable m (fr + 2176) 38 /\
    spill regs m 144 (fr + 2176) /\ spill regs m 8 (Sfr fr + 68) /\
    rg regs 18 (mrow (g_in g)) /\ addressable m (fr + 2624) 6 /\
    spill regs m 96 (decl_slot fr) /\ spill regs m 120 (fr + 2528) /\
    spill regs m 240 (fr + 2448) /\ spill regs m 232 (fr + 2464) /\ spill regs m 224 (fr + 2496) /\
    spill regs m 176 (fr + 2688) /\ spill regs m 208 (fr + 2768) /\ spill regs m 64 (fr + 3056) /\
    PRA fr regs m /\ spill regs m 152 (fr + 64) /\ spill regs m 160 (fr + 32)) c.

(* R5 (0x8169c): the b = 0 entry. The catalogue row s2 = mrow (0x8162c add s2,a0,a1 in R2's segment; R5 reads it
   at 0x816a0-0x816b0 and rewrites s2 at 0x816b4, so the fact is R5's entry fact only), and out[] / our[]
   addressable (no shadow store in 0x8169c-0x816ec; 328(s3), our[]'s granule, is written only at 0x814b8 and
   0x82f14). R5 also carries R6's row-name clause (see RBE), which R6 needs on entry (prover a Theorem Labs lane, seg_R6 on
   a working branch 96ceb6489e). Adopt FSFREE: the build_as
   side-stack package (prover a Theorem Labs lane's R5X) is no longer carried; the R6 call site rebuilds it from FRA
   (Seg/Tac_fsfree.v fra_fp). R5 also carries the identity record fr + 2176 addressable for 38 bytes (R3's shadow
   stores 0x8165c-0x8166c, see RBE) and (adopt 10) the fragment record fr + 2256 addressable for 72 bytes (R4's
   entry has it; R4's memset changes no shadow byte), which RBE holds from R6 on. *)
(* v1.9 pc 0x8169c *)
Definition Inv_B8169c (g : ghost) (c : config) : Prop :=
  CUTST g 0x8169c [] (fun fr regs m => g_n g < 2 ^ 26 /\ CUR g 7 regs /\ OURb g fr m /\
    IDBr g fr (RID (g_in g) 0) m /\ FGBr g fr (RFG (g_in g) 0) m /\
    spill regs m 312 (fr + 544) /\ spill regs m 264 (fr + 2624) /\ spill regs m 56 (fr + 3040) /\
    spill regs m 184 (fr + 2368) /\ spill regs m 144 (fr + 2176) /\ spill regs m 8 (Sfr fr + 68) /\
    rg regs 18 (mrow (g_in g)) /\ addressable m (fr + 2624) 6 /\ OUTA fr m /\
    spill regs m 96 (decl_slot fr) /\ spill regs m 120 (fr + 2528) /\
    spill regs m 240 (fr + 2448) /\ spill regs m 232 (fr + 2464) /\ spill regs m 224 (fr + 2496) /\
    spill regs m 176 (fr + 2688) /\ spill regs m 208 (fr + 2768) /\ spill regs m 64 (fr + 3056) /\
    PRA fr regs m /\ spill regs m 152 (fr + 64) /\ spill regs m 112 (fr + 2256) /\
    addressable m (fr + 2176) 38 /\ addressable m (fr + 2256) 72 /\
    (RS6.has (rt_mb (g_in g)) <> 0 /\ RS6.rname (rt_mb (g_in g)) <> 0 ->
       RBx.name_ok (rt_nb (g_in g)) /\ bytes_at rsegs m (RS6.rname (rt_mb (g_in g))) (rt_nb (g_in g)) /\
       addressable m (RS6.rname (rt_mb (g_in g))) (Z.of_nat (length (rt_nb (g_in g)))) /\
       0 < RS6.rname (rt_mb (g_in g)) /\
       RS6.rname (rt_mb (g_in g)) + Z.of_nat (length (rt_nb (g_in g))) <= AC.GT) /\
    spill regs m 160 (fr + 32)) c.

(* R6 (0x816ec): the round-trip loop head (back edge 0x81ac8 bne s6,a0,816ec); the build_as call's argument
   spills, read at 0x816ec-0x81700: [A + 312] = fr + 544 (0x814a4/0x814a8), [A + 272] = the catalogue box
   (0x816b0), [A + 264] = fr + 2624 = our[] (0x814f4/0x81544), [A + 256] = round_trip.box 0x21140
   (0x816d4/0x816d8), [A + 248] = 0x1234 (0x816dc/0x816e0). The last conjunct is prover a Theorem Labs lane's Inv_B81688_loc
   addition (seg_R6, lib/B/Prog/Seg/R6.v on a working branch 96ceb6489e); RBE also holds it.
   Adopt 10 (prover a Theorem Labs lane's R14X / R16 text: the constant 32, read by the trap tests 0x818ac / 0x81950 `bne a5,s11`):
   every R cut from here to the latch (Inv_B816ec_at .. Inv_B81ac0_at) carries `rg regs 27 32` (v1.9.0's s11;
   the patched image had s2) as its last conjunct (on R14 / R16 after a3). Its source is R5's 0x816cc `li
   s11,32`; the listing has no write to s11 in 0x816d0-0x81e50 (the next is the frame-loop prologue's 0x81e54
   `li s11,-8`), and every callee in the loop keeps s11 (AC.a_regs_kept, a_callee_saved 18..27). *)
(* v1.9 pc 0x816ec *)
Definition Inv_B816ec_at (g : ghost) (b : nat) (c : config) : Prop :=
  CUTST g 0x816ec [] (fun fr regs m => g_n g < 2 ^ 26 /\ RS g fr b regs m /\
    RBE g fr regs m /\ rg regs 21 36 /\ R6X g b fr regs m /\
    (RS6.has (rt_mb (g_in g)) <> 0 /\ RS6.rname (rt_mb (g_in g)) <> 0 ->
       RBx.name_ok (rt_nb (g_in g)) /\ bytes_at rsegs m (RS6.rname (rt_mb (g_in g))) (rt_nb (g_in g)) /\
       addressable m (RS6.rname (rt_mb (g_in g))) (Z.of_nat (length (rt_nb (g_in g)))) /\
       0 < RS6.rname (rt_mb (g_in g)) /\
       RS6.rname (rt_mb (g_in g)) + Z.of_nat (length (rt_nb (g_in g))) <= AC.GT) /\ rg regs 27 32) c.
(* v1.9 pc 0x816ec *)
Definition Inv_B816ec (g : ghost) (c : config) : Prop := exists b, Inv_B816ec_at g b c.
(* R7 (0x81710): the allocation cut, the image-B twin of a Theorem Labs lane's validated Inv_A81594_loc. Not a CUTST: it
   names the model md for the allocation's ROOM side, which comes from FRA's live-bytes bound. Push 5c drops the
   a_call_pre conjunct: fra_call_pre builds it from FRA + ENT at K = AC.AK_MALLOC = 4096 <= FN_STACK, with ret_ok
   from the segment's own `jal` at 0x81760. The request a0 = rt_n(in, b) is bounded so that ContractPlace's
   a_place_room_of_alive applies to a_size of it (the frame's ALIVE_MAX premise stays FRA's a_live_bytes (g_H g) <= 5 * 2^30, v1.9 FrameAPI alib_pre). The three inline checks at
   0x81718-0x81758 read the reciprocal s5 = 36 (0x816c8) and the magic word at [A + 128] = 0xe38f0000
   (0x816c4/0x816e4/0x816e8, read 0x8173c). The n_b = 0 arm (image A's Theorem Labs lane 05:46Z twin): build_as may return 0,
   so R7's `beqz a0,81ac0` (0x81710) is live and goes to the latch; the row / our[] / box / 0x1234 spills of image
   A's arm and [A+144] / [A+8] are RBE's. Adopt 10 (prover a Theorem Labs lane's R9 chain, a working branch be153b10cd):
   the turn-b identity / fragment records on both arms (from R6's entry RS; build_as writes neither), and on the
   n_b <> 0 arm out[]'s frame bytes rt_F: build_as's post gives bytes_at o (em_fr db sb (a5 mod 65536) 205 234
   (ba_X md mb nb b) len) only under go && E, and E is n_b <> 0, so the conjunct is guarded here; R8 reads them. *)
(* v1.9 pc 0x81710 *)
Definition Inv_B81710_at (g : ghost) (b : nat) (c : config) : Prop :=
  exists regs mem md fr A,
    c = mkCfg (mkst regs (Z_to_bv 64 0x81710) mem (seg_rom segs)) md /\
    FRA g fr [] regs mem md /\ ENT g [] mem md /\
    g_n g < 2 ^ 26 /\ (b <= 6)%nat /\ 0 <= rnb g b <= AC.ANMAX /\
    0 <= AC.a_size (rnb g b) <= 616472576 /\
    0 <= A < 2 ^ 64 /\ rg regs 9 A /\ rg regs 21 36 /\ a0v regs (rnb g b) /\ q64 mem (A + 128) 0xe38f0000 /\
    RBE g fr regs mem /\
    IDBr g fr (RID (g_in g) b) mem /\ FGBr g fr (RFG (g_in g) b) mem /\
    (rnb g b <> 0 -> bytes_at rsegs mem (fr + 544) (rt_F (g_in g) (Z.of_nat b))) /\
    rg regs 22 (Z.of_nat b) /\ OURb g fr mem /\ CUR g 7 regs /\
    (* prover a Theorem Labs lane: out[]'s 1492 bytes (also in RBE), and on the zero-count edge to the latch (which reads R6X at
       turn S b) the next turn's build_as package. *)
    OUTA fr mem /\
    (rnb g b = 0 -> R6X g (S b) fr regs mem) /\ rg regs 27 32.
(* v1.9 pc 0x81710 *)
Definition Inv_B81710 (g : ghost) (c : config) : Prop := exists b, Inv_B81710_at g b c.
(* R8 (0x81764): the copy into the fresh buffer Phi. The count is in s2 (0x81714 mv s2,a0, read 0x81774 mv a2,s2)
   and the source pointer is the spill [A + 312] = fr + 544 (0x81770), whose rnb bytes the copy reads; the
   checked copy 0x81778 also needs those rnb source bytes addressable, which FRA does not give (a Theorem Labs lane). Adopt FSFREE:
   parse's side-stack package (prover a Theorem Labs lane's R8FP) is no longer carried; the R9 call site rebuilds it from FRA.
   Adopt 10 (prover a Theorem Labs lane's R9 chain): the turn-b records and out[]'s frame bytes rt_F (R7's a0 <> 0 arm), which
   replace the earlier `exists src` at out[] (rt_F has n_b bytes when n_b <> 0). *)
(* v1.9 pc 0x81764 *)
Definition Inv_B81764_at (g : ghost) (b : nat) (c : config) : Prop :=
  exists phi, CUTST g 0x81764 (hb1 phi (rnb g b)) (fun fr regs m => g_n g < 2 ^ 26 /\ (b <= 6)%nat /\ rnb g b <> 0 /\
    a0v regs phi /\ HB m phi (rnb g b) /\ rg regs 18 (rnb g b) /\ RBE g fr regs m /\ rg regs 21 36 /\
    IDBr g fr (RID (g_in g) b) m /\ FGBr g fr (RFG (g_in g) b) m /\ bytes_at rsegs m (fr + 544) (rt_F (g_in g) (Z.of_nat b)) /\
    rg regs 22 (Z.of_nat b) /\ OURb g fr m /\ CUR g 7 regs /\
    addressable m (fr + 544) (rnb g b) /\ rg regs 27 32) c.
(* R9 (0x8177c, prover a Theorem Labs lane's R9_entry of lib/B/Prog/Seg/R9.v (a version not in this delivery)): the reac_ctrl_parse call
   0x817a0 takes a0 = s4 = Phi (0x81794), a1 = s2 = n_b (0x81798) and a2 = the parse record [A + 184] = fr + 2368
   (0x8179c; stored 0x814c4 addi a1,a3,192 / 0x814c8 with a3 = fr + 2176). Adopt FSFREE: its class-1 side-stack
   package (fp [1] with W = reac_ctrl_parse_W, D = reac_ctrl_parse_D, reac_ctrl_parse_tls, the class-1 frames
   below fr) is rebuilt at the call from FRA (Seg/Tac_fsfree.v fra_fp), not carried. FRA's window conjunct plus
   fra_frame give [sp - K, sp) addressable for every K <= FN_STACK (fra_call_pre's own window clause), and
   REAC_CTRL_PARSE_K = 8800. `rnb g b <> 0` holds on this arm only (R7's a0 <> 0 edge), which is why
   Inv_B81710_at does not carry it. Adopt 10: a Theorem Labs lane's R9_entry (R9.v on a working branch be153b10cd) verbatim -
   the turn records, the frame bytes rt_F at Phi (R8's copy post) and the fragment record's 72 addressable bytes
   (also RBE's), which the exit's RF, a0 = rt_k and addressable (fr + 2256) 72 need. *)
(* v1.9 pc 0x8177c *)
Definition Inv_B8177c_at (g : ghost) (b : nat) (c : config) : Prop :=
  exists phi, CUTST g 0x8177c (hb1 phi (rnb g b)) (fun fr regs m => g_n g < 2 ^ 26 /\ (b <= 6)%nat /\ HB m phi (rnb g b) /\ rg regs 22 (Z.of_nat b) /\ OURb g fr m /\ CUR g 7 regs /\ RBE g fr regs m /\ rg regs 21 36 /\
    rnb g b <> 0 /\ rg regs 20 phi /\ rg regs 18 (rnb g b) /\ spill regs m 184 (fr + 2368) /\
    IDBr g fr (RID (g_in g) b) m /\ FGBr g fr (RFG (g_in g) b) m /\
    bytes_at rsegs m phi (rt_F (g_in g) (Z.of_nat b)) /\ addressable m (fr + 2256) 72 /\ rg regs 27 32) c.
(* v1.9 pc 0x8177c *)
Definition Inv_B8177c (g : ghost) (c : config) : Prop := exists b, Inv_B8177c_at g b c.
(* R10 (0x817a4, after reac_ctrl_parse; the 5-arm dispatch 0x817b8-0x81808 on b; prover a Theorem Labs lane): a0 = the parse result
   rt_k, the turn's RF facts (s4 = Phi_r 0x8176c, s2 = n_b 0x81714, rnb <> 0 on R7's a0 <> 0 arm), the catalogue
   spills [A+24] = mrow + 16 / [A+16] = mrow + 20 (0x816ac / 0x816b8), [A+96] = decl_slot fr (0x814f0),
   [A+120] = fr + 2528 (0x814e8), the fragment record addressable (R4), and for the b in {3, 4} arm the
   reac_ctrl_identity_reply call 0x817e8 (a0 = Phi_r, a1 = n_b, a2 / a3 / a4 = [A+240] / [A+232] / [A+224] =
   fr + 2448 / fr + 2464 / fr + 2496, stored 0x814d0 / 0x814d8 / 0x814e0). Adopt FSFREE: the call's class-1
   side-stack package is rebuilt at the call from FRA (Seg/Tac_fsfree.v fra_fp), not carried. *)
(* v1.9 pc 0x817a4 *)
Definition Inv_B817a4_at (g : ghost) (b : nat) (c : config) : Prop :=
  exists phi, CUTST g 0x817a4 (hb1 phi (rnb g b)) (fun fr regs m => g_n g < 2 ^ 26 /\ (b <= 6)%nat /\ HB m phi (rnb g b) /\ rg regs 22 (Z.of_nat b) /\ OURb g fr m /\ CUR g 7 regs /\ RBE g fr regs m /\ rg regs 21 4 /\
    a0v regs (rt_k (g_in g) (Z.of_nat b)) /\ RF g fr b phi regs m /\
    spill regs m 24 (mrow (g_in g) + 16) /\ spill regs m 16 (mrow (g_in g) + 20) /\
    spill regs m 96 (decl_slot fr) /\ spill regs m 120 (fr + 2528) /\
    addressable m (fr + 2256) 72 /\
    (b = 5%nat -> fg_rf (rnb g 5) (RFG (g_in g) 5) (rt_g (g_in g) 5) = 0) /\ rg regs 27 32) c.
(* v1.9 pc 0x817a4 *)
Definition Inv_B817a4 (g : ghost) (c : config) : Prop := exists b, Inv_B817a4_at g b c.
(* R11 (0x817ec, after the reac_ctrl_identity_reply call 0x817e8 of the turns b = 3, 4), prover a Theorem Labs lane's R11_entry
   (lib/B/Prog/Seg/R11.v (not in this delivery) on a working branch b0de306812, seg_R11) after the earlier official body: b = 3 or
   4, the turn records RF (s4 = Phi, s2 = n_b, the frame bytes at Phi), a0 = the reply result (read by 0x817f0 beq a0,a1,81840) and, under reply_ok, the three reply cells (R10's reply post), which R11's 0x81844 / 0x8184c /
   0x81854 load for the ingest call. The reply-slot spills and the identity record's addressability are RBE's. *)
(* v1.9 pc 0x817ec *)
Definition Inv_B817ec_at (g : ghost) (b : nat) (c : config) : Prop :=
  exists phi, CUTST g 0x817ec (hb1 phi (rnb g b)) (fun fr regs m => g_n g < 2 ^ 26 /\ (b <= 6)%nat /\ HB m phi (rnb g b) /\ rg regs 22 (Z.of_nat b) /\ OURb g fr m /\ CUR g 7 regs /\ RBE g fr regs m /\ rg regs 21 36 /\
    (b = 3 \/ b = 4)%nat /\ RF g fr b phi regs m /\
    a0v regs (RcReply.reply_ret phi (rnb g b) (fr + 2448) (fr + 2464) (fr + 2496) (rt_g (g_in g) (Z.of_nat b))) /\
    (RcReply.reply_ok phi (rnb g b) (fr + 2448) (fr + 2464) (fr + 2496) (rt_g (g_in g) (Z.of_nat b)) = true ->
       LSt.rw_cells rsegs m (fr + 2448) [LCl.CB 2 (RcReply.reply_addr (rt_g (g_in g) (Z.of_nat b)))] /\
       LSt.rw_cells rsegs m (fr + 2464) [LCl.CB 8 (le8 (Z_to_bv 64 (phi + 38)))] /\
       LSt.rw_cells rsegs m (fr + 2496) [LCl.CB 8 (le8 (Z_to_bv 64 (RcReply.ir_s (rt_g (g_in g) (Z.of_nat b)) - 13)))]) /\
    rg regs 27 32) c.
(* v1.9 pc 0x817ec *)
Definition Inv_B817ec (g : ghost) (c : config) : Prop := exists b, Inv_B817ec_at g b c.
(* R12 (0x81834, after reac_ctrl_identity_fragment FRAG@0x81830 on R10's b = 6 arm 0x8180c-0x81830; only b = 6
   reaches it, b = 5 goes to 0x81914): prover a Theorem Labs lane's R12X (lib/B/Prog/Seg/R12.v (not in this delivery) on a working branch
   35bb4f952f, R12_entry, a Theorem Labs lane's refit) after the earlier official body: b = 6, n_b <> 0, s4 = Phi_r, the identity
   record RID b at fr + 2176, the fragment call's new record RFG (S b) at fr + 2256 and its 72 bytes addressable,
   a0 = fg_rf (the call's result, tested 0x81838), and on the closing class (fg_rf = 1) the three out cells of the
   FgClose post (reac_ctrl_identity_fragment_c.v fg_mem) that 0x81840-0x81854 load for the ingest call: the u16
   fg_addr at fr + 2448, the word fr + 2256 + 19 at fr + 2464 and the word fg_T - 13 at fr + 2496. The reply-slot
   spills and the identity record's addressability are RBE's. *)
(* v1.9 pc 0x81834 *)
Definition Inv_B81834_at (g : ghost) (b : nat) (c : config) : Prop :=
  exists phi, CUTST g 0x81834 (hb1 phi (rnb g b)) (fun fr regs m => g_n g < 2 ^ 26 /\ (b <= 6)%nat /\ HB m phi (rnb g b) /\ rg regs 22 (Z.of_nat b) /\ OURb g fr m /\ CUR g 7 regs /\ RBE g fr regs m /\ rg regs 21 36 /\
    b = 6%nat /\ rnb g b <> 0 /\ rg regs 20 phi /\
    IDBr g fr (RID (g_in g) b) m /\ FGBr g fr (RFG (g_in g) (S b)) m /\ addressable m (fr + 2256) 72 /\
    a0v regs (fg_rf (rnb g b) (RFG (g_in g) b) (rt_g (g_in g) (Z.of_nat b))) /\
    (fg_rf (rnb g b) (RFG (g_in g) b) (rt_g (g_in g) (Z.of_nat b)) = 1 ->
       u16 m (fr + 2448) (RcFrag.fg_addr (RFG (g_in g) b) (rt_g (g_in g) (Z.of_nat b))) /\
       q64 m (fr + 2464) (fr + 2256 + 19) /\
       q64 m (fr + 2496) (RcFrag.fg_T (RFG (g_in g) b) (rt_g (g_in g) (Z.of_nat b)) - 13)) /\
    rg regs 27 32) c.
(* v1.9 pc 0x81834 *)
Definition Inv_B81834 (g : ghost) (c : config) : Prop := exists b, Inv_B81834_at g b c.
(* R13 (0x81860, after reac_identity_ingest; prover a Theorem Labs lane's Inv_B817fc_loc of lib/B/Prog/Seg/R13.v (a version not in this delivery),
   written on a working branch 6a3ed3e194, verbatim): the code tests the result (0x81860 li a1,1; 0x81864 beq a0,a1,81a98; the fall-through 0x81868 `j 0x82fa4` is the abort branch), so the cut carries a0 = 1. The result
   is ingest_ret (reac_identity_ingest_c.v:17-18): -1 when the call is refused, else fst (ING idb ad pb), which is
   0 unless ad is ADDR_FIRMWARE, ADDR_MODEL_NAME or ADDR_REAC_VERSION with a payload long enough for that branch
   (RcIdentModel.v:72-76); seg_R12 has to show turn b's record meets that condition. The records are turn S b's:
   the identity record after the ingest (0x8185c writes fr + 2176) and the fragment record after R11's fragment
   call; s4 = Phi_r (0x8176c), which the free call of R13 releases. *)
(* v1.9 pc 0x81860 *)
Definition Inv_B81860_at (g : ghost) (b : nat) (c : config) : Prop :=
  exists phi, CUTST g 0x81860 (hb1 phi (rnb g b)) (fun fr regs m => g_n g < 2 ^ 26 /\ (b <= 6)%nat /\ HB m phi (rnb g b) /\ rg regs 22 (Z.of_nat b) /\ OURb g fr m /\ CUR g 7 regs /\ RBE g fr regs m /\ rg regs 21 36 /\
    IDBr g fr (RID (g_in g) (S b)) m /\ FGBr g fr (RFG (g_in g) (S b)) m /\ rg regs 20 phi /\ a0v regs 1 /\ rg regs 27 32) c.
(* v1.9 pc 0x81860 *)
Definition Inv_B81860 (g : ghost) (c : config) : Prop := exists b, Inv_B81860_at g b c.
(* rsum: the unsigned sum of the first i of the 32 block bytes Phi_r[18..] of turn b (image A's rsum of a Theorem Labs lane's
   Seg/B3Cuts.v (not in this delivery); rt_g is lib/B/Prog/SlotModel.v's, with image A's meaning). *)
Definition rsum (g : ghost) (b i : nat) : Z := RcModel.psum (skipn 18 (rt_g (g_in g) (Z.of_nat b))) i.
(* R14 (0x818a8): the 32-byte block-sum loop head (back edge 0x818d8 bnez a4,818a8); a0 = a2 = Phi_r + 18 + i. *)
(* B: a4 holds 32 - i at 0x818a8 (0x818a0 li a4,32; 0x818c8 addi a4,a4,-1) *)
(* a Theorem Labs lane's Seg/B3Cuts.v body (not in this delivery; image A's Inv_A81768_at), re-pinned: the running sum is a1 (0x81884 li a1,0, 0x818d0
   add a1,a1,a5) where image A uses the same register; the catalogue-row spills [A+112] / [A+8] / [A+0] of
   image A are image B's [A+272] (in RBE) / [A+24] (0x816ac) / [A+16] (0x816b8), the declaration slot [A+200] is
   [A+96] (0x814f0) and the ports buffer [A+216] is [A+120] (0x814e8); the 12 ports bytes at fr + 2528 are
   addressable from the shadow stores 0x81870 / 0x81874. Adopt 10 (prover a Theorem Labs lane's R14X, lib/B/Prog/Seg/R14.v on
   a working branch b086914ea7): a3 = -(Phi_r + 18), the room word R10 computes on the b = 0 arm (0x81888
   li a0,-18 / 0x8188c sub a0,a0,s4 / 0x81894 sltiu / 0x81898 neg / 0x8189c and, with s4 = Phi_r from the RF of
   R10's entry; one edge 0x817a4 -> 0x817c4 -> 0x8186c -> 0x818a8, no cut between), read at 0x818a8 and not
   written in the loop; and s11 = 32 (see R6). a Theorem Labs lane's third R14X fact, want CAT n_0 (rt_g 0) = mrow (the exit's
   a0 = mrow), holds for every input: lemma rnb_want0 below, not a conjunct. *)
(* v1.9 pc 0x818a8 *)
Definition Inv_B818a8_at (g : ghost) (b : nat) (c : config) : Prop :=
  exists phi i, CUTST g 0x818a8 (hb1 phi (rnb g b)) (fun fr regs m => g_n g < 2 ^ 26 /\ (b <= 6)%nat /\ HB m phi (rnb g b) /\ rg regs 22 (Z.of_nat b) /\ OURb g fr m /\ CUR g 7 regs /\ RBE g fr regs m /\ rg regs 21 36 /\ (i <= 32)%nat /\ rg regs 10 (phi + 18 + Z.of_nat i) /\ rg regs 12 (phi + 18 + Z.of_nat i) /\ rg regs 14 (32 - Z.of_nat i) /\
    b = 0%nat /\ (i < 32)%nat /\ rg regs 11 (rsum g b i) /\ RF g fr b phi regs m /\
    spill regs m 24 (mrow (g_in g) + 16) /\ spill regs m 16 (mrow (g_in g) + 20) /\
    spill regs m 96 (decl_slot fr) /\ spill regs m 120 (fr + 2528) /\
    addressable m (fr + 2528) 12 /\ rg regs 13 (- (phi + 18)) /\ rg regs 27 32) c.
(* v1.9 pc 0x818a8 *)
Definition Inv_B818a8 (g : ghost) (c : config) : Prop := exists b, Inv_B818a8_at g b c.
(* R15 (0x81914): after reac_ctrl_identity_fragment; the turn-(S b) records, s4 = Phi_r (image A's s8), a0 = 0. *)
(* v1.9 pc 0x81914 *)
Definition Inv_B81914_at (g : ghost) (b : nat) (c : config) : Prop :=
  exists phi, CUTST g 0x81914 (hb1 phi (rnb g b)) (fun fr regs m => g_n g < 2 ^ 26 /\ (b <= 6)%nat /\ HB m phi (rnb g b) /\ rg regs 22 (Z.of_nat b) /\ OURb g fr m /\ CUR g 7 regs /\ RBE g fr regs m /\ rg regs 21 36 /\
    RB g fr b (RID (g_in g) (S b)) (RFG (g_in g) (S b)) regs m /\ rg regs 20 phi /\ a0v regs 0 /\ rg regs 27 32) c.
(* v1.9 pc 0x81914 *)
Definition Inv_B81914 (g : ghost) (c : config) : Prop := exists b, Inv_B81914_at g b c.
(* R16 (0x8194c): the second block-sum loop head (back edge 0x8197c bnez a4,8194c); a0 = a2 = Phi_r + 18 + i. *)
(* B: a4 holds 32 - i at 0x8194c (0x81944 li a4,32; 0x8196c addi a4,a4,-1) *)
(* Adopt 10 (prover a Theorem Labs lane's R16 lane, the R14X pair word for word): a3 = -(Phi_r + 18) from R10's b = 1, 2 arm
   (0x8192c li a0,-18 / 0x81930 sub a0,a0,s4 / 0x81938 sltiu / 0x8193c neg / 0x81940 and; one edge 0x817a4 ->
   0x817c4 -> 0x8186c -> 0x8191c -> 0x81928 -> 0x8194c, no cut between), not written in the loop; s11 = 32 (see R6). *)
(* v1.9 pc 0x8194c *)
Definition Inv_B8194c_at (g : ghost) (b : nat) (c : config) : Prop :=
  exists phi i, CUTST g 0x8194c (hb1 phi (rnb g b)) (fun fr regs m => g_n g < 2 ^ 26 /\ (b <= 6)%nat /\ HB m phi (rnb g b) /\ rg regs 22 (Z.of_nat b) /\ OURb g fr m /\ CUR g 7 regs /\ RBE g fr regs m /\ rg regs 21 36 /\ (i <= 32)%nat /\ rg regs 10 (phi + 18 + Z.of_nat i) /\ rg regs 12 (phi + 18 + Z.of_nat i) /\ rg regs 14 (32 - Z.of_nat i) /\
    (b = 1 \/ b = 2)%nat /\ (i < 32)%nat /\ rg regs 11 (rsum g b i) /\
    RFb g fr b (RID (g_in g) b) (RFG (g_in g) b) phi regs m /\ rg regs 13 (- (phi + 18)) /\ rg regs 27 32) c.
(* v1.9 pc 0x8194c *)
Definition Inv_B8194c (g : ghost) (c : config) : Prop := exists b, Inv_B8194c_at g b c.
(* B: [A+120] holds fr + 2528 at 0x819a8 (0x814e8 sd a1,120(s1); read 0x819c8 for the ports_parse call) *)
(* R17 (0x819a8): after reac_box_catalogue_match; a0 = the matched row. *)
(* v1.9 pc 0x819a8 *)
Definition Inv_B819a8_at (g : ghost) (b : nat) (c : config) : Prop :=
  exists phi, CUTST g 0x819a8 (hb1 phi (rnb g b)) (fun fr regs m => g_n g < 2 ^ 26 /\ (b <= 6)%nat /\ HB m phi (rnb g b) /\ rg regs 22 (Z.of_nat b) /\ OURb g fr m /\ CUR g 7 regs /\ spill regs m 120 (fr + 2528) /\ RBE g fr regs m /\ rg regs 21 36 /\
    b = 0%nat /\ RFb g fr b (RID (g_in g) b) (RFG (g_in g) b) phi regs m /\ a0v regs (mrow (g_in g)) /\
    spill regs m 24 (mrow (g_in g) + 16) /\ spill regs m 16 (mrow (g_in g) + 20) /\
    spill regs m 96 (decl_slot fr) /\ addressable m (fr + 2528) 12 /\ rg regs 27 32) c.
(* v1.9 pc 0x819a8 *)
Definition Inv_B819a8 (g : ghost) (c : config) : Prop := exists b, Inv_B819a8_at g b c.
(* B: [A+96] holds decl_slot fr at 0x819d0 (0x814f0 sd a1,96(s1); read 0x81a48 for declaration_of) *)
(* R18 (0x819d0): after reac_ports_parse; the two port words at fr + 2528 / fr + 2532, s2 = Phi_r + 18 (image A's
   s11), a0 = 0. *)
(* v1.9 pc 0x819d0 *)
Definition Inv_B819d0_at (g : ghost) (b : nat) (c : config) : Prop :=
  exists phi, CUTST g 0x819d0 (hb1 phi (rnb g b)) (fun fr regs m => g_n g < 2 ^ 26 /\ (b <= 6)%nat /\ HB m phi (rnb g b) /\ rg regs 22 (Z.of_nat b) /\ OURb g fr m /\ CUR g 7 regs /\ spill regs m 96 (decl_slot fr) /\ RBE g fr regs m /\ rg regs 21 36 /\
    b = 0%nat /\ RFb g fr b (RID (g_in g) b) (RFG (g_in g) b) phi regs m /\ rg regs 18 (phi + 18) /\
    a0v regs 0 /\
    u32 m (fr + 2528) (4 * RcLeaf.n_in (rt_pbs (g_in g))) /\
    u32 m (fr + 2532) (4 * RcLeaf.n_out (rt_pbs (g_in g))) /\
    spill regs m 120 (fr + 2528) /\ spill regs m 24 (mrow (g_in g) + 16) /\
    spill regs m 16 (mrow (g_in g) + 20) /\ rg regs 27 32) c.
(* v1.9 pc 0x819d0 *)
Definition Inv_B819d0 (g : ghost) (c : config) : Prop := exists b, Inv_B819d0_at g b c.
(* B: s2 holds Phi_r + 18 at 0x81a50 (0x819c0 addi s2,s4,18); no register holds decl_slot fr at 0x81a50, it is
   reloaded from [A+96] at 0x81a60 *)
(* R19 (0x81a50): after declaration_of; a0 = vd <> 0 as a 64-bit word, the 32 declaration bytes addressable. *)
(* v1.9 pc 0x81a50 *)
Definition Inv_B81a50_at (g : ghost) (b : nat) (c : config) : Prop :=
  exists phi vd, CUTST g 0x81a50 (hb1 phi (rnb g b)) (fun fr regs m => g_n g < 2 ^ 26 /\ RFb g fr b (RID (g_in g) b) (RFG (g_in g) b) phi regs m /\ rg regs 10 vd /\ vd <> 0 /\ rg regs 18 (phi + 18) /\ spill regs m 96 (decl_slot fr) /\ bytes_at rsegs m (decl_slot fr) (RcDecl.decl (rt_mb (g_in g))) /\ RBE g fr regs m /\ rg regs 21 36 /\
    b = 0%nat /\ HB m phi (rnb g b) /\ 0 <= vd < 2 ^ 64 /\
    length (RcDecl.decl (rt_mb (g_in g))) = 32%nat /\ addressable m (decl_slot fr) 32 /\ rg regs 27 32) c.
(* v1.9 pc 0x81a50 *)
Definition Inv_B81a50 (g : ghost) (c : config) : Prop := exists b, Inv_B81a50_at g b c.
(* R20 (0x81a68): after the bcmp wrapper; a0 = 0. *)
(* v1.9 pc 0x81a68 *)
Definition Inv_B81a68_at (g : ghost) (b : nat) (c : config) : Prop :=
  exists phi, CUTST g 0x81a68 (hb1 phi (rnb g b)) (fun fr regs m => g_n g < 2 ^ 26 /\ (b <= 6)%nat /\ HB m phi (rnb g b) /\ rg regs 22 (Z.of_nat b) /\ OURb g fr m /\ CUR g 7 regs /\ RBE g fr regs m /\ rg regs 21 36 /\
    b = 0%nat /\ RFb g fr b (RID (g_in g) b) (RFG (g_in g) b) phi regs m /\ a0v regs 0 /\ rg regs 27 32) c.
(* v1.9 pc 0x81a68 *)
Definition Inv_B81a68 (g : ghost) (c : config) : Prop := exists b, Inv_B81a68_at g b c.
(* R21 (0x81aa0): after wrapper_free; the turn-(S b) records feed the latch into Inv_B816ec_at at turn S b. *)
(* v1.9 pc 0x81aa0 *)
Definition Inv_B81aa0_at (g : ghost) (b : nat) (c : config) : Prop :=
  CUTST g 0x81aa0 [] (fun fr regs m => g_n g < 2 ^ 26 /\ (b <= 6)%nat /\ rg regs 22 (Z.of_nat b) /\ OURb g fr m /\ RBE g fr regs m /\ rg regs 21 36 /\
    RB g fr b (RID (g_in g) (S b)) (RFG (g_in g) (S b)) regs m /\ rg regs 27 32) c.
(* v1.9 pc 0x81aa0 *)
Definition Inv_B81aa0 (g : ghost) (c : config) : Prop := exists b, Inv_B81aa0_at g b c.
(* The round-trip latch (0x81ac0 `addiw s6,s6,1`, 0x81ac4 `li a0,7`, 0x81ac8 `bne s6,a0,816ec`), a new cut
   (prover a Theorem Labs lane, owner a Theorem Labs lane): two edges reach it - R21's fall-through and R7's `beqz a0` at 0x81710, which is
   taken when build_as returns 0 (catalogue rows 0, 2 and 3 have em_hid = 0, so rnb g b = 0 for b = 5 and b = 6;
   that is why R7's cut no longer carries rnb g b <> 0). s6 still holds b here, and the turn's records are the
   ones turn b produced, i.e. the state turn b + 1 starts from, so the latch segment 0x81ac0 -> 0x816ec re-enters
   Inv_B816ec_at g (S b) after the increment (and leaves the loop when b + 1 = 7). It therefore carries R6's own
   entry set at index b + 1 (RBE, the divisor pin and R6X) next to the end-of-turn loop state. *)
(* v1.9 pc 0x81ac0 *)
Definition Inv_B81ac0_at (g : ghost) (b : nat) (c : config) : Prop :=
  CUTST g 0x81ac0 [] (fun fr regs m => g_n g < 2 ^ 26 /\ (b <= 6)%nat /\
    rg regs 22 (Z.of_nat b) /\ CUR g 7 regs /\ OURb g fr m /\
    IDBr g fr (RID (g_in g) (S b)) m /\ FGBr g fr (RFG (g_in g) (S b)) m /\
    RBE g fr regs m /\ rg regs 21 36 /\ R6X g (S b) fr regs m /\ rg regs 27 32) c.
(* v1.9 pc 0x81ac0 *)
Definition Inv_B81ac0 (g : ghost) (c : config) : Prop := exists b, Inv_B81ac0_at g b c.

(* PL0 (a Theorem Labs lane, lib/B/Prog/Seg/P7.v): the turn-0 frame-loop facts that P12's exit Inv_B81ec4_at g 0 reads -
   CUR at c0 = t_c (g_in g) 0, the identity record ID0 and the fragment record z72 in the frame. P7 / P8 / P9
   carry them because no cut between 0x81d80 and 0x81dd4 produces them and their callees keep them (each writes
   only its own stack window, which fra_frame puts apart from the frame). Adopt 7: and RAD, the records'
   addressable bytes (P3's shadow stores 0x81cb0-0x81cfc), which FLI carries in the loop. Adopt 8: and the
   identity record pointer spill [A+176] = fr + 2688 (A4 0x81500; FLI's in the loop), which P12's other exit
   Inv_B82eac reads: when left_0 = n - c0 = 0 (n <= 7) P12's run goes on through 0x81ec4 (`bnez s9` not taken)
   and 0x81ec8 to 0x82eac (x1_entry_of_pl0). Adopt 9: and the fragment record pointer spill [A+208] = fragb fr
   (A4 0x81508; FLI's in the loop), which the prologue reads at 0x81e58 for [A+256] / [A+128] / [A+120]; P6 / P7
   state only that the slot holds some value. The only store to [s1 + 208] is A4's 0x81508. v1.9.0: and the
   first-fragment state of turn 0, FSj g fr 0 (the local `first` zeroed by P3's checked_memset 0x81d0c, a0 =
   [A+168] = fr + 2880, a2 = 40: have = 0, n = 0, fs0; no store to [fr + 2880, fr + 2920) up to the loop head;
   the patched image zeroed its first-fragment spills in the frame-loop prologue instead). *)
Definition PL0 (g : ghost) (fr : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  CUR g (c0 (g_in g)) regs /\ IDBe g fr RcIdentModel.ID0 m /\ FGBe g fr z72 m /\ RAD fr m /\
  spill regs m 176 (fr + 2688) /\ spill regs m 208 (fragb fr) /\ FSj g fr 0 regs m.
(* ---- Init and P8 (P1-P12). P1 (0x81c58) re-poisons out[]; P2 (0x81ca8) is the init join. P3-P12 ~ P01-P09.
   Adopt 6 (prover a Theorem Labs lane, P1-P6 Qed on a working branch 3cf40d7a82, Seg/P2.v / P4.v / P6.v): P2 gains the record
   pointer spills [A+176] = fr + 2688 / [A+208] = fr + 2768 (A4 0x81500 / 0x81508), P4 gains D = fr + 2768 and
   [A+64] = fr + 3056 (A4 0x8153c), P6 gains [A+64], PL0 and the kind-name table addressable. Their sources are
   threaded by range: the three spills from A4 (LOOPB, R2-R5, RBE, P1, P1', P2, P3; no store to 64 / 176 / 208(s1)
   in 0x81548-0x81ec4), PL0's parts CUR g c0 from R1's 0x815b4 / 0x815e0 (the R cuts carry CUR g 7, and 7 <= n
   there), the kind-name table from P1 on, the identity record ID0 from P4 on (P3's reac_identity_init 0x81d14)
   and the fragment record z72 from P5 on (P4's checked_memset 0x81d24).
   Adopt 7: RAD (P3's shadow stores 0x81cb0-0x81cfc) by range: P4 gains `addressable (fr + 2688) 38` (its
   addressable D 72 is the fragment record's), P5 gains RAD, PL0 holds it from P6 on.
   Adopt 8: the spill [A+176] = fr + 2688 by range past P3 (P3 has it as q64 (A + 176)): P4 and P5 gain it, PL0
   holds it from P6 on. The only store to [s1 + 176] is A4's 0x81500, and P3-P12's callees write only their own
   stack windows below sp <= A and the frame.
   Adopt 9: every P cut carries PRO (see PRA / PRO above), and P5 gains [A+208] = fragb fr (P4 has it as the
   cell at A + 208 holding D = fr + 2768), which PL0 holds from P6 on. v1.9.0: P3's run also zeroes the local
   `first` (0x81d00-0x81d0c checked_memset, a0 = [A+168] = fr + 2880, a1 = 0, a2 = 40, after the shadow stores
   0x81cdc / 0x81ce0 / 0x81cf4-0x81cfc mark its 40 bytes usable), so P4 and P5 gain FSj g fr 0 and PL0 holds it
   from P6 on. *)
(* B: [A+8] holds Q = S(fr) + 68 at 0x81c58 (0x81210 addi s11,s3,68; 0x81634 sd s11,8(s1); read 0x81ca0 for the
   meta_fill_f8 call with a1 = 187). Adopt 10 (prover a Theorem Labs lane, seg_P1 / seg_P1_bfc): the bound is Q + 187 <= S(fr) + 328,
   so the 0xf8 fill [Q, Q + 187) of 0x81ca4 stays below S(fr) + 328, the shadow byte of our[] (PRO's addressable
   (fr + 2624) 6); image A did the same on Inv_A81a68 / Inv_A81a70 (4b78298cbd). Q = S(fr) + 68 (RBE's
   [A+8]) meets it: 68 + 187 = 255. *)
(* v1.9 pc 0x81c58 *)
Definition Inv_B81c58 (g : ghost) (c : config) : Prop :=
  CUTST g 0x81c58 [] (fun fr regs m => g_n g < 2 ^ 26 /\ OURb g fr m /\ a0v regs 0 /\
    PRO fr regs m /\
    (exists Q, spill regs m 8 Q /\ Sfr fr <= Q /\ Q + 187 <= Sfr fr + 328) /\
    spill regs m 56 (fr + 3040) /\
    spill regs m 176 (fr + 2688) /\ spill regs m 208 (fr + 2768) /\ spill regs m 64 (fr + 3056) /\
    CUR g (c0 (g_in g)) regs /\ addressable m KNC.KIND_NAME 112) c.
(* XC (the image-B twin of a Theorem Labs lane's XC, image A's Inv_A81bd8..Inv_A81c84): the code byte fr + 3040 (v1.9.0's
   `code`; patched fr + 2960) and its pointer. Image A keeps the pointer in the spill [A + 280] (0x813ac /
   0x813b0), image B in s8 from P2's reload 0x81cac `ld s8,56(s1)` ([A + 56] = fr + 3040 from A4's 0x81530; the R
   region uses s8 as the -8 poison constant from 0x816d0; on the early edge 0x815e8 into P3, s8 is R1's reload
   0x815e4). The byte is written at 0x81d44 `sb a0,0(s8)` and read at 0x81df4 `lbu a0,0(s8)`. These are the two
   conjuncts the P7-P10 cuts already spell out. *)
Definition XC (fr : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  rg regs 24 (fr + 3040) /\ addressable m (fr + 3040) 1.

(* P1' (0x81c60), the image-B twin of a Theorem Labs lane's new image-A cut Inv_A81ac8 (pre-v1.9 0x81a70): the poison block is entered twice, from P1's
   own `beqz a0,81c60` (0x81c58) and from 0x81c0c `beqz a0,81c60` (which skips 0x81c58 and the sink jump
   0x81c5c), so it needs its own cut with P1's body. a0 = 0 on both edges (the taken beqz). *)
(* v1.9 pc 0x81c60 *)
Definition Inv_B81c60 (g : ghost) (c : config) : Prop :=
  CUTST g 0x81c60 [] (fun fr regs m => g_n g < 2 ^ 26 /\ OURb g fr m /\ a0v regs 0 /\
    PRO fr regs m /\
    (exists Q, spill regs m 8 Q /\ Sfr fr <= Q /\ Q + 187 <= Sfr fr + 328) /\
    spill regs m 56 (fr + 3040) /\
    spill regs m 176 (fr + 2688) /\ spill regs m 208 (fr + 2768) /\ spill regs m 64 (fr + 3056) /\
    CUR g (c0 (g_in g)) regs /\ addressable m KNC.KIND_NAME 112) c.
(* v1.9 pc 0x81ca8 *)
Definition Inv_B81ca8 (g : ghost) (c : config) : Prop :=
  CUTST g 0x81ca8 [] (fun fr regs m => g_n g < 2 ^ 26 /\ OURb g fr m /\ spill regs m 56 (fr + 3040) /\
    PRO fr regs m /\
    spill regs m 176 (fr + 2688) /\ spill regs m 208 (fr + 2768) /\
    spill regs m 64 (fr + 3056) /\ CUR g (c0 (g_in g)) regs /\ addressable m KNC.KIND_NAME 112) c.
(* P3 (0x81cb0), the twin of a Theorem Labs lane's cut-P3_entry.v (not in this delivery; image A Inv_A81b14, pre-v1.9 0x81abc): the identity-record init call 0x81d14 and its
   cells. Image B holds the identity record fr + 2688 in the spill [A + 176] (0x814fc / 0x81500, read 0x81d10)
   where image A holds it in s11, and the fragment record fr + 2768 in [A + 208] (0x81508, read 0x81d1c) where
   image A uses [A + 208]. s8 = fr + 3040 is B's own carrier of the code-byte pointer (XC), produced here by
   P2's reload 0x81cac and needed at 0x81d44; on the early edge 0x815e8 it is R1's reload 0x815e4. v1.9.0: P3's
   run also marks the local `first` usable (0x81cdc / 0x81ce0 / 0x81cf4-0x81cfc `sb zero,360..364(s3)`) and zeroes
   it (0x81d00-0x81d0c checked_memset, a0 = [A+168] = fr + 2880 (PRA), a2 = 40), so the cut carries the 40
   cells of `first` that the call writes. *)
(* v1.9 pc 0x81cb0 *)
Definition Inv_B81cb0 (g : ghost) (c : config) : Prop :=
  CUTST g 0x81cb0 [] (fun fr regs m => g_n g < 2 ^ 26 /\ OURb g fr m /\ rg regs 24 (fr + 3040) /\
    PRO fr regs m /\
    spill regs m 64 (fr + 3056) /\ CUR g (c0 (g_in g)) regs /\ addressable m KNC.KIND_NAME 112 /\
    exists (spv A : Z) (idb junk : list byte),
      getr regs 2 = Z_to_bv 64 spv /\ getr regs 9 = Z_to_bv 64 A /\
      0 <= A < 2 ^ 64 /\ 0 <= spv < 2 ^ 64 /\
      q64 m (A + 176) (fr + 2688) /\
      LSt.rw_cells rsegs m (A + 208) [LCl.C8 (Z_to_bv 64 (fr + 2768))] /\
      LSt.rw_cells rsegs m (fr + 2688) [LCl.CB 38 idb] /\
      LSt.rw_cells rsegs m (fr + 2768) [LCl.CB 72 junk] /\
      (exists junkf : list byte, LSt.rw_cells rsegs m (fr + 2880) [LCl.CB 40 junkf])) c.
(* P4 (0x81d18), the twin of a Theorem Labs lane's cut-P4_entry.v (not in this delivery; image A Inv_A81b80, pre-v1.9 0x81b00): the checked_memset call 0x81d24 on the
   72-byte fragment scratch D = [A + 208] (0x81d1c), with the write set W of the call and the cells FRA reads
   outside it. Image B's spill ranges are [A + 336, A + 344) (the fr carrier) and [A + 40, A + 56) (the fr
   reload and the selector; patched [A + 56, A + 72)), the two ranges B's sl_fr_run / sl_fr_meta ask to be
   outside W. v1.9.0: P3's run leaves the local `first` zeroed and usable (FSj g fr 0, 40 addressable bytes). *)
(* v1.9 pc 0x81d18 *)
Definition Inv_B81d18 (g : ghost) (c : config) : Prop :=
  CUTST g 0x81d18 [] (fun fr regs m => g_n g < 2 ^ 26 /\ OURb g fr m /\ rg regs 24 (fr + 3040) /\
    PRO fr regs m /\
    CUR g (c0 (g_in g)) regs /\ addressable m KNC.KIND_NAME 112 /\ IDBe g fr RcIdentModel.ID0 m /\
    addressable m (fr + 2688) 38 /\ spill regs m 176 (fr + 2688) /\
    exists (D spv A : Z) (junk : list byte),
      let W : list ivl := [(D, D + 72); (spv - asan_memset_c.ASAN_MEMSET_K, spv)] in
      getr regs 2 = Z_to_bv 64 spv /\ getr regs 9 = Z_to_bv 64 A /\
      0 <= A < 2 ^ 64 /\ 0 <= D < 2 ^ 64 /\ 0 <= spv < 2 ^ 64 /\
      LSt.rw_cells rsegs m (A + 208) [LCl.C8 (Z_to_bv 64 D)] /\
      LSt.rw_cells rsegs m D [LCl.CB 72 junk] /\ addressable m D 72 /\ end_in_app D 72 /\ app_mem (D + 7) /\
      (D + 72 <= RT_LO \/ RT_HI <= D) /\
      (D + 72 <= spv - asan_memset_c.ASAN_MEMSET_K \/ spv <= D) /\
      (forall x, 0 <= x < 6283264 -> Frame.outside W x) /\
      (forall x, fr <= x < fr + 24 -> Frame.outside W x) /\
      (forall A0, getr regs 9 = Z_to_bv 64 A0 -> 0 <= A0 < 2 ^ 64 ->
         forall x, A0 + 336 <= x < A0 + 344 -> Frame.outside W x) /\
      (forall A0, getr regs 9 = Z_to_bv 64 A0 -> 0 <= A0 < 2 ^ 64 ->
         forall x, A0 + 40 <= x < A0 + 56 -> Frame.outside W x) /\
      (forall x, g_S g - 104 <= x < g_S g -> Frame.outside W x) /\
      (forall x, Sfr fr <= x < Sfr fr + FRAME_SHADOW -> Frame.outside W x) /\
      (forall x, fr + 2624 <= x < fr + 2624 + Z.of_nat (length (OUR (g_in g))) -> Frame.outside W x) /\
      all_app W /\ rt_disjoint W /\
      D = fr + 2768 /\ q64 m (A + 64) (fr + 3056) /\
      FSj g fr 0 regs m /\ addressable m (fr + 2880) 40) c.
(* P5 (0x81d28), the twin of a Theorem Labs lane's cut-P5_entry.v (not in this delivery; image A Inv_A81b90, pre-v1.9 0x81b10): the one code byte at fr + 3040 (written
   0x81d44 through s8) and the 32-byte scratch fr + 3056, whose pointer is the spill [A + 64] (0x81538 /
   0x8153c, read 0x81d5c before the memset 0x81d64 with a2 = 32). Image A holds both as spills ([A + 280],
   [A + 240]). (Patched: fr + 2960 through s11, fr + 2976 at [A + 72].) *)
(* v1.9 pc 0x81d28 *)
Definition Inv_B81d28 (g : ghost) (c : config) : Prop :=
  CUTST g 0x81d28 [] (fun fr regs m => g_n g < 2 ^ 26 /\ OURb g fr m /\
    PRO fr regs m /\
    CUR g (c0 (g_in g)) regs /\ addressable m KNC.KIND_NAME 112 /\ IDBe g fr RcIdentModel.ID0 m /\
    FGBe g fr z72 m /\ RAD fr m /\ spill regs m 176 (fr + 2688) /\ spill regs m 208 (fragb fr) /\
    exists (A : Z) (jy junk : list byte),
      rg regs 9 A /\ 0 <= A /\ rg regs 24 (fr + 3040) /\ q64 m (A + 64) (fr + 3056) /\
      LSt.rw_cells rsegs m (fr + 3040) [LCl.CB 1 jy] /\
      LSt.rw_cells rsegs m (fr + 3056) [LCl.CB 32 junk] /\
      FSj g fr 0 regs m) c.
(* P6 (0x81d68), the twin of a Theorem Labs lane's cut-P6_entry.v (not in this delivery; image A Inv_A81bd8, pre-v1.9 0x81b58): the reac_ctrl_identity_reply call 0x81d7c.
   Adopt FSFREE: the callee's class-1 side-stack package (fp [1], reac_ctrl_identity_reply_tls, the frame apart
   from fp_w [1]) is rebuilt at the call from FRA (Seg/Tac_fsfree.v fra_fp), not carried, so P5 need not create
   it; the window / placement parts are FRA's (fra_frame, fra_call_pre). Image B loads all three record pointers
   from spills - 0x81d70 ld a2,88(s1), 0x81d74 ld a3,80(s1), 0x81d78 ld a4,72(s1) (image A keeps the third in
   s4) - and the fragment pointer P7 reloads is [A + 208] (0x81d8c). *)
(* v1.9 pc 0x81d68 *)
Definition Inv_B81d68 (g : ghost) (c : config) : Prop :=
  CUTST g 0x81d68 [] (fun fr regs m => g_n g < 2 ^ 26 /\ OURb g fr m /\ XC fr regs m /\
    PRO fr regs m /\
    spill regs m 64 (fr + 3056) /\ PL0 g fr regs m /\ addressable m KNC.KIND_NAME 112 /\
    exists (A pa pp pn f : Z),
      rg regs 9 A /\ 0 <= A < 2 ^ 64 /\ 0 <= pa < 2 ^ 64 /\ 0 <= pp < 2 ^ 64 /\ 0 <= pn < 2 ^ 64 /\
      q64 m (A + 88) pa /\ q64 m (A + 80) pp /\ q64 m (A + 72) pn /\ q64 m (A + 208) f /\
      addressable m (AC.aspZ regs - reac_ctrl_identity_reply_c.REAC_CTRL_IDENTITY_REPLY_K)
        reac_ctrl_identity_reply_c.REAC_CTRL_IDENTITY_REPLY_K /\
      addressable m reac_ctrl_parse_c.REAC_CTRL_PARSE_BC 6) c.

(* P7 (0x81d80) and its exit 0x81da8 (P8's entry): a Theorem Labs lane's cut texts (lib/B/Prog/Seg/P7.v). At 0x81d80: a0 = -1
   (the result tested at 0x81d84), the four spills loaded at 0x81d8c-0x81da0 ([A+208], [A+88], [A+80], [A+72];
   with a1 = 0 their values are not read), the spill [A+64] = fr + 3056 (0x8153c sd a1,64(s1) with a1 = a3 + 880,
   a3 = fr + 2176; read by P8 at 0x81db0). The reac_ctrl_identity_fragment call at 0x81da4 takes mem_inv, which
   the segment gets from ro_agree (MemNorm.evt_normalize), not from the cut (push 5c). At 0x81da8: a0 = -1 (the
   callee's result with a1 = 0), s2 = -1 (0x81d80, kept by the callee) and
   [A+64]. FRA gives the rest of the local text: sp <= APPMEM_END (sp <= A <= S < APPMEM_END), and the frame apart
   from the callee's stack window [sp - 4672, sp) (fra_frame at K = 4672 <= FN_STACK).
   Both cuts also carry the four facts P10's entry needs and no cut between 0x81d80 and 0x81dd4 produces
   (a Theorem Labs lane): s8 = fr + 3040 with that byte addressable, the kind-name table addressable, and PL0. *)
(* v1.9 pc 0x81d80 *)
Definition Inv_B81d80 (g : ghost) (c : config) : Prop :=
  CUTST g 0x81d80 [] (fun fr regs m => g_n g < 2 ^ 26 /\ OURb g fr m /\ a0v regs (-1) /\
    PRO fr regs m /\
    (exists v, spill regs m 208 v) /\ (exists v, spill regs m 88 v) /\ (exists v, spill regs m 80 v) /\
    (exists v, spill regs m 72 v) /\ spill regs m 64 (fr + 3056) /\
    rg regs 24 (fr + 3040) /\ addressable m (fr + 3040) 1 /\
    addressable m KNC.KIND_NAME 112 /\ PL0 g fr regs m) c.
(* v1.9 pc 0x81da8 *)
Definition Inv_B81da8 (g : ghost) (c : config) : Prop :=
  CUTST g 0x81da8 [] (fun fr regs m => g_n g < 2 ^ 26 /\ OURb g fr m /\ a0v regs (-1) /\
    PRO fr regs m /\
    rg regs 18 (-1) /\ spill regs m 64 (fr + 3056) /\
    rg regs 24 (fr + 3040) /\ addressable m (fr + 3040) 1 /\
    addressable m KNC.KIND_NAME 112 /\ PL0 g fr regs m) c.
(* P9 (0x81dbc) and its exit 0x81dd4: a Theorem Labs lane's cut texts (lib/B/Prog/Seg/P9.v). At 0x81dbc: a0 = -1 (the
   result of the reac_ports_parse call at 0x81db8, tested at 0x81dc0). At 0x81dd4: a0 = -1 (the callee's result for
   q = 0) and s2 = -1 (0x81dbc, kept by the callee). FRA gives the rest of the local text: sp <= APPMEM_END, and the
   frame apart from the callee's stack window [sp - 16, sp) (fra_frame at K = 16). Both cuts carry the same four
   facts as P7 / P8 (a Theorem Labs lane). *)
(* v1.9 pc 0x81dbc *)
Definition Inv_B81dbc (g : ghost) (c : config) : Prop :=
  CUTST g 0x81dbc [] (fun fr regs m => g_n g < 2 ^ 26 /\ OURb g fr m /\ a0v regs (-1) /\
    PRO fr regs m /\
    rg regs 24 (fr + 3040) /\ addressable m (fr + 3040) 1 /\
    addressable m KNC.KIND_NAME 112 /\ PL0 g fr regs m) c.
(* v1.9 pc 0x81dd4 *)
Definition Inv_B81dd4 (g : ghost) (c : config) : Prop :=
  CUTST g 0x81dd4 [] (fun fr regs m => g_n g < 2 ^ 26 /\ OURb g fr m /\ a0v regs (-1) /\ rg regs 18 (-1) /\
    PRO fr regs m /\
    rg regs 24 (fr + 3040) /\ addressable m (fr + 3040) 1 /\
    addressable m KNC.KIND_NAME 112 /\ PL0 g fr regs m) c.
(* P11 (0x81de8), the twin of a Theorem Labs lane's image-A cut Inv_A81c60: the reac_ports_unknown call 0x81de4 returned -1 for the
   null argument (tested 0x81dec against a1 = -1 from 0x81de8) and left the code byte at fr + 3040 zero, which
   0x81df4 `lbu a0,0(s8)` reads and 0x81df8 tests. Image A reads the same byte through the spill [A + 280].
   P11 and P12 also carry what the B chain into the frame-loop head needs and no cut between produces: the
   kind-name table (the call 0x81e04) and PL0, which Inv_B81ec4_at g 0 reads (a Theorem Labs lane). *)
(* v1.9 pc 0x81de8 *)
Definition Inv_B81de8 (g : ghost) (c : config) : Prop :=
  CUTST g 0x81de8 [] (fun fr regs m => g_n g < 2 ^ 26 /\ OURb g fr m /\ a0v regs (-1) /\
    PRO fr regs m /\
    b8 m (fr + 3040) 0 /\ XC fr regs m /\
    addressable m KNC.KIND_NAME 112 /\ PL0 g fr regs m) c.
(* P12 (0x81e08), after reac_ctrl_kind_name (0x81e00 li a0,14; 0x81e04 jal): prover a Theorem Labs lane's a0 = kind_name_addr 14 =
   KNC.QMARK = 0x211e0 (14 > 13; the contract's a0 post), the string whose two bytes 0x81e08-0x81e4c test.
   Adopt 11: KNT, the kind-name table, which P12 hands to FLI at the loop head (its run 0x81e08-0x81ec0 writes
   only the spills at A + 88 .. 144 and A + 256 and the shadow bytes S(fr) + 370 .. 385). Producer P11: the
   addressability from Inv_B81de8 (the reac_ctrl_kind_name call writes only its stack window [sp - 16, sp), app
   memory, so no shadow byte changes), the bytes from FRA's G_img_c (frame_RELRO; p11_table). *)
(* v1.9 pc 0x81e08 *)
Definition Inv_B81e08 (g : ghost) (c : config) : Prop :=
  CUTST g 0x81e08 [] (fun fr regs m => g_n g < 2 ^ 26 /\ OURb g fr m /\ PRO fr regs m /\ PL0 g fr regs m /\
    a0v regs KNC.QMARK /\ KNT m) c.

(* ---- Frame loop (F1-F38), turn j : nat. F1 malloc gains Phi, F37 free drops it. Each cut carries the turn
   index j (j <= 255) and, on the malloc span, HB(Phi, len) (plan 3.4, FP.4, IC HB(Phi) rows). *)
(* f1_IN (push 5b, image A's f1_IN of a Theorem Labs lane's seg_F1 / image B's Theorem Labs lane's Seg/F1.v local cuts): the input block
   the F1 allocation call keeps live and the two instrumented byte loads of the loop head read. The membership
   is guarded by 0 < g_n g: lib/B/FrameAPI.v:54 gives `In (p, n) H` only on that arm (n = 0 has p = empty).
   (Image A states it unguarded at 6cfbd06ba1; reported to a Theorem Labs lane.) a Theorem Labs lane's f1_WIN / f1_HI are not carried:
   fra_call_pre gives the callee window addressable and off the live blocks at AK_MALLOC = 4096 <= FN_STACK, and
   the three ENTRY stack-top facts are FRA's, moved to the cut's state by ENT. Image A's prologue spill
   [A + 248] = fr + 176 is image B's [A + 168] (0x81470), already in FLI. *)
Definition f1_IN (g : ghost) (m : word -> option byte) : Prop :=
  (0 < g_n g -> In (g_p g, g_n g) (g_H g)) /\ addressable m (g_p g) (g_n g) /\
  bytes_at rsegs m (g_p g) (g_in g).
(* f1_IN from FRA's input facts when n > 0. Not from FRA alone: on the n = 0 arm f1_IN asks for
   `addressable m (g_p g) 0`, so g_p g <= APPMEM_END, which FRA does not give (its addressable conjunct is
   guarded by 0 < g_n g, and bytes_at bounds p by 2^64 only); so the two cuts below keep f1_IN. At the loop head
   LI gives 0 < g_n g (li_n_pos), so a segment that builds Inv_B81ec4_at gets f1_IN from FRA by fra_f1_in. *)
Lemma fra_f1_in : forall g fr hb regs mem md,
  FRA g fr hb regs mem md -> 0 < g_n g -> f1_IN g mem.
Proof.
  intros g fr hb regs mem md HFRA Hn.
  destruct (fra_in g fr hb regs mem md HFRA) as (Hinb & Hinblk).
  destruct (Hinblk Hn) as (Hin & Had).
  split; [intros _; exact Hin | split; [exact Had | exact Hinb]].
Qed.

(* LI's cursor (0 <= c_j, CUR) and its 1 <= left_j = n - c_j give 0 < n. *)
Lemma li_n_pos : forall g fr j regs m, LI g fr j regs m -> 0 < g_n g.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros g fr j regs m (_ & _ & _ & (Hc & _) & Hl & _). unfold t_left, f_left, t_c, g_n in *. lia.
Qed.
(* F1 (0x81ec4): the frame-loop head (back edge 0x82d24 bne a3,a0,81ec4; prologue 0x81e50-0x81ec0 falls in).
   Adopt 10 (prover a Theorem Labs lane), v1.9.0 form: s6 = 1 (P12's 0x81ea0 `li s6,1`; read at the head 0x81ed0 / 0x81eec /
   0x81f00 `bltu s6,s5` / `bne s9,s6` / `bltu s6,a1` and by opens_record's have store 0x825e8 `sw s6,0(a1)`;
   the loop writes s6 only to restore it after borrowing it, 0x823fc / 0x82424, 0x82878 / 0x82ab0, 0x82c18 /
   0x82c50 / 0x82c6c, so it is 1 again at the latch). The patched image read a2 = 1 here (P12's / F38's `li
   a2,1`, both gone in v1.9.0) and carried s6 = fr + 176, which no v1.9.0 register holds ([A+280], FLI).
   Positions: 4 (patched a2 = 1) holds the record pointer's v1.9.0 home [A+280] = fr + 176, 5 (patched s6 = fr +
   176) holds s6 = 1. The same pairing at F7 / F8 (0x8215c / 0x82174 / 0x82180): the inner position of the patched
   s6 = fr + 176 holds q64 (A + 280) (fr + 176), the cell 0x82160 `ld a0,280(s1)` reads. From the row loop on
   (0x82bf4 .. 0x82d1c) the patched sum-flag spill [A+288] position is `True`: v1.9.0 reuses s9 as the row counter
   (0x82bdc `mv s9,zero`), and [A+248] (1 - sum_ok) is read only at 0x81700 and 0x8246c, so no cut from the row
   loop's entry Inv_B82bcc_at on carries it (a Theorem Labs lane via a Theorem Labs lane, 15:3xZ). *)
(* v1.9 pc 0x81ec4 *)
Definition Inv_B81ec4_at (g : ghost) (j : nat) (c : config) : Prop :=
  CUTST g 0x81ec4 [] (fun fr regs m => g_n g < 2 ^ 26 /\ LI g fr j regs m /\ f1_IN g m /\
    spill regs m 280 (fr + 176) /\ rg regs 22 1) c.
(* v1.9 pc 0x81ec4 *)
Definition Inv_B81ec4 (g : ghost) (c : config) : Prop := exists j, Inv_B81ec4_at g j c.
(* F2 (0x81f50, after the malloc 0x81f4c): the turn's records REC0 and first-fragment state FSj j, which LI holds
   at the head (IFS j) and F1 does not write (adopt 6); adopt 10 (a Theorem Labs lane): s6 = 1 from the head (F1 writes no
   s6; malloc keeps it). The parse calls read the record pointer from [A+280] (0x81fb4 / 0x82040 `ld a2,280(s1)`;
   the patched image had `mv a2,s6`). *)
(* v1.9 pc 0x81f50 *)
Definition Inv_B81f50_at (g : ghost) (j : nat) (c : config) : Prop :=
  exists phi, CUTST g 0x81f50 (hb1 phi (AC.a_size (flen g j))) (fun fr regs m => g_n g < 2 ^ 26 /\ (j <= 255)%nat /\ a0v regs phi /\ HB m phi (flen g j) /\ LK g fr j regs m /\ FC g fr j regs m /\ f1_IN g m /\
    FSj g fr j regs m /\ REC0 g fr j m /\ rg regs 22 1) c.
(* v1.9 pc 0x81f50 *)
Definition Inv_B81f50 (g : ghost) (c : config) : Prop := exists j, Inv_B81f50_at g j c.
(* The frame-loop cut shape. Every cut it builds lies past 0x81f60, so besides the turn's heap block it carries
   the facts the whole body holds (a Theorem Labs lane's working note, sections 2-3, not in this delivery): s2 = Phi (0x81f50 mv s2,a0, no further write
   in the loop), s4 = len (0x81f28 / 0x81f30) and FTURN, the cursor spills [A+224] = p + body (0x81f60 sd
   s5,224(s1), read back at 0x82ca8) and [A+232] = left - h (0x81f40, read back at 0x82cb0) with the frame's bytes
   at Phi (F2's memcpy 0x81f74; adopt 6). FCUTP hands Phi to the cut's own predicate as well. *)
Definition FCUTP (g : ghost) (pc : Z) (j : nat) (P : Z -> Z -> bvmap 5 word -> (word -> option byte) -> Prop)
    (c : config) : Prop := exists phi, CUTST g pc (hb1 phi (AC.a_size (flen g j)))
      (fun fr regs m => g_n g < 2 ^ 26 /\ (j <= 255)%nat /\ HB m phi (flen g j) /\
         rg regs 18 phi /\ rg regs 20 (flen g j) /\ FTURN g j phi regs m /\
         P phi fr regs m) c.
Definition FCUT (g : ghost) (pc : Z) (j : nat) (P : Z -> bvmap 5 word -> (word -> option byte) -> Prop)
    (c : config) : Prop := FCUTP g pc j (fun _ fr regs m => P fr regs m) c.
(* v1.9 pc 0x81f78 *)
Definition Inv_B81f78_at (g : ghost) (j : nat) (c : config) : Prop := FCUT g 0x81f78 j (fun fr regs m => LK g fr j regs m /\ FC g fr j regs m /\ rg regs 22 1 /\ FSj g fr j regs m /\ REC0 g fr j m) c.
(* v1.9 pc 0x81f78 *)
Definition Inv_B81f78 (g : ghost) (c : config) : Prop := exists j, Inv_B81f78_at g j c.
(* Adopt 7: FPS from F3's exit 0x81fbc and F5's entry 0x82048 (after the parse calls 0x81fb8 / 0x82044); F6 on
   also F272. Adopt 10 (prover a Theorem Labs lane): both carry the parse result a0 = t_k j (0x81fbc `mv s8,a0`; 0x82048
   `bnez a0,82fa4`), from the parse post. Adopt 11 (prover a Theorem Labs lane): the length branch of the turn, s4 = flen g j
   (FCUTP's rg regs 20). 0x81fbc is the return point of the long-path parse call 0x81fb8, reached only through
   0x81f64 `beqz s4,82020` and 0x81f7c `bltu s4,a0,82020` (a0 = 50, 0x81f78) both not taken: 50 <= flen g j.
   0x82048 is the return point of the short-path parse call 0x82044, reached only through 0x82020, the target of
   those two branches taken (s4 = 0, or s4 < 50 unsigned, and 0 <= flen g j): flen g j < 50. *)
(* v1.9 pc 0x81fbc *)
Definition Inv_B81fbc_at (g : ghost) (j : nat) (c : config) : Prop := FCUT g 0x81fbc j (fun fr regs m => LK g fr j regs m /\ FC g fr j regs m /\ rg regs 22 1 /\ FSj g fr j regs m /\ REC0 g fr j m /\ FPS g fr j m /\ a0v regs (t_k (g_in g) j) /\ 50 <= flen g j) c.
(* v1.9 pc 0x81fbc *)
Definition Inv_B81fbc (g : ghost) (c : config) : Prop := exists j, Inv_B81fbc_at g j c.
(* v1.9 pc 0x82048 *)
Definition Inv_B82048_at (g : ghost) (j : nat) (c : config) : Prop := FCUT g 0x82048 j (fun fr regs m => LK g fr j regs m /\ rg regs 22 1 /\ FSj g fr j regs m /\ REC0 g fr j m /\ FPS g fr j m /\ a0v regs (t_k (g_in g) j) /\ flen g j < 50) c.
(* v1.9 pc 0x82048 *)
Definition Inv_B82048 (g : ghost) (c : config) : Prop := exists j, Inv_B82048_at g j c.
(* F6 (0x82098): the 32-byte block-sum loop (back edge 0x820c4 bnez a4,82098), image A's patched 0x81e28; both arms of F4
   (0x81fe8 bne -> 0x82068, 0x8201c j 0x8206c) reach it, and only they: the short path (F5) leaves 0x82048 by
   0x82064 `j 82148`. Adopt 11 (prover a Theorem Labs lane): the cut is F6's entry, the first turn of the loop, in the FCUTP form
   (Phi = s2), with F4's registers: 50 <= flen g j (both F4 arms are on the long path, past 0x81fbc), s8 = t_k j
   (0x81fbc `mv s8,a0`; no s8 write in 0x81fc0-0x82094), a1 = 0 (0x82070), t0 = Phi + 18 (0x82074), a2 = Phi + 18
   (0x82080), a0 = Phi + 18 (0x82094 `mv a0,a2`), a4 = 32 (0x82090), a7 = 32 (0x8206c) and a3 = -(Phi + 18)
   (0x82078-0x8208c: a0 = -18 - Phi, then a3 = a0 when a0 <u -17, which holds since 0 <= Phi < 2^64 - 18 by
   0x81f88 `bltu s2,a0,81f24` with a0 = -18). The back edge 0x820c4 does not return to this cut (a4 counts down):
   the F6 segment runs the 32 turns itself. *)
(* v1.9 pc 0x82098 *)
Definition Inv_B82098_at (g : ghost) (j : nat) (c : config) : Prop := FCUTP g 0x82098 j (fun phi fr regs m => LK g fr j regs m /\ rg regs 22 1 /\ FSj g fr j regs m /\ REC0 g fr j m /\ FPS g fr j m /\ F272 g j regs m /\
  50 <= flen g j /\ rg regs 24 (t_k (g_in g) j) /\ a0v regs (phi + 18) /\ rg regs 11 0 /\ rg regs 12 (phi + 18) /\
  rg regs 13 (- (phi + 18)) /\ rg regs 14 32 /\ rg regs 17 32 /\ rg regs 5 (phi + 18)) c.
(* v1.9 pc 0x82098 *)
Definition Inv_B82098 (g : ghost) (c : config) : Prop := exists j, Inv_B82098_at g j c.
(* F7 (0x8215c, the parse return point) and F8 (0x82174, the return point of the reac_ctrl_kind_name call 0x82170;
   0x82180, the return point of the call 0x8217c): a Theorem Labs lane's cut texts (lib/B/Prog/Seg/F7.v, F8.v). Phi in s2
   and len in s4; s8 = v (the parse result, below 2^31, a0 = v at 0x8215c) and the record fr + 176 ([A+280], FLI)
   with its first word v (read 0x82160-0x82164 `ld a0,280(s1); lw a0,0(a0)`); s6 = 1 (FM); the call premises FRA does not give (the
   KIND_NAME table bytes and their addressability; mem_inv comes from ro_agree by MemNorm.evt_normalize and the
   frame's app memory above GT from fra_app, push 5c); the FLV spills over the named
   spill base (FLVsp). The calls return a0 = kind_name_addr v; at 0x82180 the name bytes are at that address (the
   contract's post). FRA gives the rest of the local text: sp <= APPMEM_END (sp <= A <= S < APPMEM_END), and the
   frame apart from the callee's stack window [sp - 16, sp) (fra_frame at K = REAC_CTRL_KIND_NAME_FRAME).
   Adopt 6 (a Theorem Labs lane's F8 lane; F6 produces them, F7 / F8 carry them to f10_K at 0x821ec): [A+248] = 1 - sum_ok (v1.9.0
   0x82060 li a0,1 on the len < 50 arm, 0x82144 snez a0,a0 with a0 = the low byte of the block sum on the other,
   then 0x82148 sd a0,248(s1); patched: s9) and, for len >= 50, the frame's first 50 bytes at Phi (outside the
   callee windows and the frame); the per-turn spills FTURN and the records REC0. Adopt 11: the KIND_NAME pair is
   also FLI's KNT (LK); the explicit conjuncts stay as the F7 / F8 lanes state them. *)
(* v1.9 pc 0x8215c *)
Definition Inv_B8215c_at (g : ghost) (j : nat) (c : config) : Prop :=
  exists phi, CUTST g 0x8215c (hb1 phi (AC.a_size (flen g j)))
    (fun fr regs m =>
       g_n g < 2 ^ 26 /\ (j <= 255)%nat /\ HB m phi (flen g j) /\ LK g fr j regs m /\
       rg regs 18 phi /\ rg regs 20 (t_len (g_in g) j) /\ FM g j phi fr regs m /\ FSj g fr j regs m /\
       bytes_at rsegs m KNC.KIND_NAME KNC.kind_name_bytes /\ addressable m KNC.KIND_NAME 112 /\
       spill regs m 248 (1 - b2z (t_sum_ok (g_in g) j)) /\ (50 <= flen g j -> bytes_at rsegs m phi (t_g (g_in g) j)) /\
       FTURN g j phi regs m /\ REC0 g fr j m /\ FPS g fr j m /\ F272 g j regs m /\
       exists A v, FLVsp A fr regs m /\
         rg regs 10 v /\ rg regs 24 v /\ 0 <= v < 2 ^ 31 /\ q64 m (A + 280) (fr + 176) /\
         u32 m (fr + 176) v)
    c.
(* v1.9 pc 0x8215c *)
Definition Inv_B8215c (g : ghost) (c : config) : Prop := exists j, Inv_B8215c_at g j c.
(* v1.9 pc 0x82174 *)
Definition Inv_B82174_at (g : ghost) (j : nat) (c : config) : Prop :=
  exists phi, CUTST g 0x82174 (hb1 phi (AC.a_size (flen g j)))
    (fun fr regs m =>
       g_n g < 2 ^ 26 /\ (j <= 255)%nat /\ HB m phi (flen g j) /\ LK g fr j regs m /\
       rg regs 18 phi /\ rg regs 20 (t_len (g_in g) j) /\ FM g j phi fr regs m /\ FSj g fr j regs m /\
       bytes_at rsegs m KNC.KIND_NAME KNC.kind_name_bytes /\ addressable m KNC.KIND_NAME 112 /\
       spill regs m 248 (1 - b2z (t_sum_ok (g_in g) j)) /\ (50 <= flen g j -> bytes_at rsegs m phi (t_g (g_in g) j)) /\
       FTURN g j phi regs m /\ REC0 g fr j m /\ FPS g fr j m /\ F272 g j regs m /\
       exists A v, FLVsp A fr regs m /\
         rg regs 10 (KNC.kind_name_addr v) /\ rg regs 24 v /\ 0 <= v < 2 ^ 31 /\ q64 m (A + 280) (fr + 176) /\
         u32 m (fr + 176) v)
    c.
(* v1.9 pc 0x82174 *)
Definition Inv_B82174 (g : ghost) (c : config) : Prop := exists j, Inv_B82174_at g j c.
(* v1.9 pc 0x82180 *)
Definition Inv_B82180_at (g : ghost) (j : nat) (c : config) : Prop :=
  exists phi, CUTST g 0x82180 (hb1 phi (AC.a_size (flen g j)))
    (fun fr regs m =>
       g_n g < 2 ^ 26 /\ (j <= 255)%nat /\ HB m phi (flen g j) /\ LK g fr j regs m /\
       rg regs 18 phi /\ rg regs 20 (t_len (g_in g) j) /\ FM g j phi fr regs m /\ FSj g fr j regs m /\
       bytes_at rsegs m KNC.KIND_NAME KNC.kind_name_bytes /\ addressable m KNC.KIND_NAME 112 /\
       spill regs m 248 (1 - b2z (t_sum_ok (g_in g) j)) /\ (50 <= flen g j -> bytes_at rsegs m phi (t_g (g_in g) j)) /\
       FTURN g j phi regs m /\ REC0 g fr j m /\ FPS g fr j m /\ F272 g j regs m /\
       exists A v, FLVsp A fr regs m /\
         rg regs 10 (KNC.kind_name_addr v) /\ rg regs 24 v /\ 0 <= v < 2 ^ 31 /\ q64 m (A + 280) (fr + 176) /\
         u32 m (fr + 176) v /\
         bytes_at rsegs m (KNC.kind_name_addr v) (RcKind.cstr_bytes (RcKind.kind_name v)))
    c.
(* v1.9 pc 0x82180 *)
Definition Inv_B82180 (g : ghost) (c : config) : Prop := exists j, Inv_B82180_at g j c.
(* F10 (0x821ec) and its exits (a Theorem Labs lane, lib/B/Prog/Seg/F10.v, whose source is not in this delivery), over the reac_ctrl_identity_reply result. Entry
   0x821ec: f10_K's carried state, the record bytes, a0 = reply_ret, and the reply cells under reply_ok. Exit
   0x8226c (F11 entry, ir true, sum_ok): the reply cells and a1 = ir_s - 13. Exit 0x82308 (bne a0,a1 at 0x821f0
   taken, ir false; no official cut before). Adopt 6: FTURN, and the records by range: REC0 at 0x821ec / 0x8226c
   (before the reply-path ingest 0x82300), RECR at 0x82304 / 0x82308 / 0x82340. Adopt 7: FPS and F272 (on from
   0x81fbc / 0x82098) and RCA (F9's shadow stores 0x821bc / 0x821c8 / 0x821d4) on 0x821ec, 0x8226c, 0x82304 and
   0x82308, for F12's FRBA at 0x82340. *)
(* v1.9 pc 0x821ec *)
Definition Inv_B821ec_at (g : ghost) (j : nat) (c : config) : Prop :=
  exists phi, CUTST g 0x821ec (hb1 phi (AC.a_size (flen g j)))
    (fun fr regs m =>
       f10_K g j phi fr regs m /\ FSj g fr j regs m /\
       (50 <= flen g j -> bytes_at rsegs m phi (t_g (g_in g) j)) /\
       rg regs 10 (RcReply.reply_ret phi (flen g j) (fr + 256) (fr + 272) (fr + 304) (t_g (g_in g) j)) /\
       (RcReply.reply_ok phi (flen g j) (fr + 256) (fr + 272) (fr + 304) (t_g (g_in g) j) = true ->
          f10_RPost phi fr (t_g (g_in g) j) m) /\
       FTURN g j phi regs m /\ REC0 g fr j m /\ FPS g fr j m /\ F272 g j regs m /\ RCA fr m) c.
(* v1.9 pc 0x821ec *)
Definition Inv_B821ec (g : ghost) (c : config) : Prop := exists j, Inv_B821ec_at g j c.
(* F11 (0x8226c): before the record_sum_closes call 0x82284 (image A inlines the sum; its loop head 0x82044). *)
(* v1.9 pc 0x8226c *)
Definition Inv_B8226c_at (g : ghost) (j : nat) (c : config) : Prop :=
  exists phi, CUTST g 0x8226c (hb1 phi (AC.a_size (flen g j)))
    (fun fr regs m =>
       f10_K g j phi fr regs m /\ FSj g fr j regs m /\
       0 < phi /\ phi + 50 <= 2 ^ 64 /\ 50 <= flen g j /\ t_sum_ok (g_in g) j = true /\
       bytes_at rsegs m phi (t_g (g_in g) j) /\
       RcReply.reply_ok phi (flen g j) (fr + 256) (fr + 272) (fr + 304) (t_g (g_in g) j) = true /\
       f10_RPost phi fr (t_g (g_in g) j) m /\
       rg regs 11 (RcReply.ir_s (t_g (g_in g) j) - 13) /\
       FTURN g j phi regs m /\ REC0 g fr j m /\ FPS g fr j m /\ F272 g j regs m /\ RCA fr m) c.
(* v1.9 pc 0x8226c *)
Definition Inv_B8226c (g : ghost) (c : config) : Prop := exists j, Inv_B8226c_at g j c.
(* F11's exit 0x82304 (after the reply-path ingest 0x82300). Adopt 7: the Phi bytes under 50 <= flen (0x8226c has
   them, F11's two calls read Phi only), FPS, F272 and RCA. Adopt 8 (prover a Theorem Labs lane): a0 = the ingest result r with
   0 <= r < 2^63, which F12's first instruction 0x82304 `bltz a0,82fa4` reads (not taken); F11 gets it from the
   reac_identity_ingest post (ingest_ret is 0 or 1 when the call is not refused; image A's twin is Inv_A820f8_at). *)
(* v1.9 pc 0x82304 *)
Definition Inv_B82304_at (g : ghost) (j : nat) (c : config) : Prop :=
  FCUTP g 0x82304 j (fun phi fr regs m => LK g fr j regs m /\ FM g j phi fr regs m /\ FSj g fr j regs m /\ RECR g fr j m /\
    (50 <= flen g j -> bytes_at rsegs m phi (t_g (g_in g) j)) /\
    FPS g fr j m /\ F272 g j regs m /\ RCA fr m /\
    (exists r, rg regs 10 r /\ 0 <= r < 2 ^ 63) /\ FS9 g j regs m) c.
(* v1.9 pc 0x82304 *)
Definition Inv_B82304 (g : ghost) (c : config) : Prop := exists j, Inv_B82304_at g j c.
(* F10 exit 0x82308 (the bne a0,a1 at 0x821f0 taken; ir false): a new cut, no official cut there before. *)
(* v1.9 pc 0x82308 *)
Definition Inv_B82308_at (g : ghost) (j : nat) (c : config) : Prop :=
  exists phi, CUTST g 0x82308 (hb1 phi (AC.a_size (flen g j)))
    (fun fr regs m =>
       f10_K g j phi fr regs m /\ FSj g fr j regs m /\
       (50 <= flen g j -> bytes_at rsegs m phi (t_g (g_in g) j)) /\
       RcReply.ir (flen g j) (t_g (g_in g) j) = false /\
       FTURN g j phi regs m /\ RECR g fr j m /\ FPS g fr j m /\ F272 g j regs m /\ RCA fr m) c.
(* v1.9 pc 0x82308 *)
Definition Inv_B82308 (g : ghost) (c : config) : Prop := exists j, Inv_B82308_at g j c.
(* F13 (0x82340, the F12 -> F13 boundary): F12's memcpy 0x8232c-0x8233c copies the 72 fragment-record bytes from
   [A + 208] = fr + 2768 (FGBe / fragb) to [A + 200] = fr + 336 (0x82330 ld a0,200(s1) / 0x82334 ld s5,208(s1) /
   0x8233c jal checked_memcpy with a2 = 72), and F13's entry reads them (a1,a2,a3 of the identity_fragment call
   0x82358). The cut carries the copy (two Theorem Labs lanes as provers, a Theorem Labs lane 09:34Z). Prover a Theorem Labs lane's text (lib/B/Prog/Seg/F13.v (a version not in this delivery),
   Inv_B822d0_loc, seg_F13): the first group is the earlier official body; then what the call itself needs: s5 =
   the record fragb fr (patched s7), the record's and Phi's bytes, the addressability of Phi, the record, the copy and the three
   output cells, and the placement of Phi against the frame and against the callee's stack window. The argument
   spills [A+288] / [A+296] / [A+304], [A+208] and [A+200] are FLI's (LK); the sum flag s9 is FM's.
   Adopt 6 short-arm guards (as image A's Inv_A82138_at, pre-v1.9 0x820a0, push 6c5b): every frame reaches 0x82340 (len < 50: parse
   kind 0, reply_ret 0, 0x821f0 bne -> 0x82308, the zero stores to S(fr) + 42 .. 50 and the memcpy 0x8233c), so
   a Theorem Labs lane's 50 <= flen g j becomes the guard of Phi's 50 bytes, their addressability and their two placements; the
   heap list is the a_size form (FCUTP). Also the record range bundles RECR and FRBA (F12 produces FRBA here). *)
(* v1.9 pc 0x82340 *)
Definition Inv_B82340_at (g : ghost) (j : nat) (c : config) : Prop :=
  FCUTP g 0x82340 j
    (fun phi fr regs m =>
       (LK g fr j regs m /\ bytes_at rsegs m (fr + 336) (t_FG (g_in g) j) /\
        FM g j phi fr regs m /\ FSj g fr j regs m) /\
       rg regs 21 (fragb fr) /\
       (50 <= flen g j ->
          (phi + 50 <= fr \/ fr + FRAME_BYTES <= phi) /\
          (phi + 50 <= AC.aspZ regs - RIFC.REAC_CTRL_IDENTITY_FRAGMENT_K \/ AC.aspZ regs <= phi) /\
          bytes_at rsegs m phi (t_g (g_in g) j) /\ addressable m phi 50) /\
       bytes_at rsegs m (fragb fr) (t_FG (g_in g) j) /\
       addressable m (fragb fr) 72 /\ addressable m (fr + 336) 72 /\
       addressable m (fr + 256) 2 /\ addressable m (fr + 272) 8 /\ addressable m (fr + 304) 8 /\
       RECR g fr j m /\ FRBA g j fr phi regs m /\ FS9 g j regs m)
    c.
(* v1.9 pc 0x82340 *)
Definition Inv_B82340 (g : ghost) (c : config) : Prop := exists j, Inv_B82340_at g j c.
(* F14 (0x8235c, the return of the identity_fragment call 0x82358), prover a Theorem Labs lane's text (Seg/F13.v (a version not in this delivery),
   Inv_B822ec_loc): the earlier official body, a0 = the fragment result, the two bcmp operands of F14 with their
   addressability (the copy at fr + 336 and the record at fragb fr with its post bytes frrec), Phi, and the
   fragment's post memory fg_mem, which F15 reads for FLV's conditional part. Adopt 6: every frame reaches
   0x8235c too (the call returns 0 for FgNone, which every short frame is), so Phi's facts are under
   50 <= flen g j as at 0x82340; plus RECF, FRBA and FRX. *)
(* v1.9 pc 0x8235c *)
Definition Inv_B8235c_at (g : ghost) (j : nat) (c : config) : Prop :=
  FCUTP g 0x8235c j
    (fun phi fr regs m =>
       (LK g fr j regs m /\ FM g j phi fr regs m /\ FSj g fr j regs m) /\
       rg regs 10 (RcFrag.fg_ret (frcl g j fr phi)) /\
       (50 <= flen g j ->
          (phi + 50 <= fr \/ fr + FRAME_BYTES <= phi) /\
          (phi + 50 <= AC.aspZ regs - RIFC.REAC_CTRL_IDENTITY_FRAGMENT_K \/ AC.aspZ regs <= phi) /\
          bytes_at rsegs m phi (t_g (g_in g) j) /\ addressable m phi 50) /\
       bytes_at rsegs m (fr + 336) (t_FG (g_in g) j) /\ addressable m (fr + 336) 72 /\
       bytes_at rsegs m (fragb fr) (frrec g j fr phi) /\ addressable m (fragb fr) 72 /\
       RIFC.fg_mem (fragb fr) (fr + 256) (fr + 272) (fr + 304) (t_FG (g_in g) j) (t_g (g_in g) j)
         (frcl g j fr phi) m /\
       RECF g fr j m /\ FRBA g j fr phi regs m /\ FRX g j fr phi m /\ FS9 g j regs m)
    c.
(* v1.9 pc 0x8235c *)
Definition Inv_B8235c (g : ghost) (c : config) : Prop := exists j, Inv_B8235c_at g j c.
(* F15 (0x82378), a Theorem Labs lane's local text (lib/B/Prog/Seg/F15.v seg_F15 Qed, not in this delivery): adds the fragment return value
   s7 = fg_ret (frcl ...) (decides the 0x8237c branch), the compare the call ran (t_sum_ok false, so the class
   is FgNone; the 72-byte memcmp of the copy against the record is Some vcmp = a0). Adopt 6: RECF and a Theorem Labs lane's two
   bundles (FRBA, FRX; Seg/F15.v (not in this delivery) f52ea940d3c Inv_B8230c_rec / Inv_B82310_rec, guarded). *)
(* v1.9 pc 0x82378 *)
Definition Inv_B82378_at (g : ghost) (j : nat) (c : config) : Prop :=
  FCUTP g 0x82378 j (fun phi fr regs m => LK g fr j regs m /\ FLV g fr j regs m /\ FM g j phi fr regs m /\
    FSj g fr j regs m /\ rg regs 23 (RcFrag.fg_ret (frcl g j fr phi)) /\
    t_sum_ok (g_in g) j = false /\
    (exists vcmp : Z,
       SF.memcmp_model (t_FG (g_in g) j) (frrec g j fr phi) 72 = Some vcmp /\ rg regs 10 vcmp) /\
    RECF g fr j m /\ FRBA g j fr phi regs m /\ FRX g j fr phi m /\ FS9 g j regs m) c.
(* v1.9 pc 0x82378 *)
Definition Inv_B82378 (g : ghost) (c : config) : Prop := exists j, Inv_B82378_at g j c.
(* F15 internal split (twin of image A's 0x82154): the identity_fragment-result block (rf <> 1 -> 0x82468, rf = 1 ->
   the ingest checks to F16 0x823d8). v1.9.0 re-anchor: the patched block began at 0x82310 `li a0,1` and compared
   with `bne s7,a0` at 0x82314; v1.9.0 deletes the `li` and compares with the frame-loop constant s6 = 1 (FM) at
   0x8237c `bne s7,s6,82468`, the first instruction of the replacement block, which F15's fall-through (0x82378
   `bnez a0`) and F14's 0x82364 `bnez s9,8237c` (sum_ok set, compare skipped) reach, as before. The patched body
   holds there unchanged (nothing in it named a0 = 1). Carries the frame-loop invariant; entered from F15
   (0x82378), exits to Inv_B82468 or Inv_B823d8. Adopt 6: as 0x82378. *)
(* v1.9 pc 0x8237c *)
Definition Inv_B8237c_at (g : ghost) (j : nat) (c : config) : Prop :=
  FCUTP g 0x8237c j (fun phi fr regs m => LK g fr j regs m /\ FLV g fr j regs m /\ FM g j phi fr regs m /\
    FSj g fr j regs m /\ rg regs 23 (RcFrag.fg_ret (frcl g j fr phi)) /\ RECF g fr j m /\
    FRBA g j fr phi regs m /\ FRX g j fr phi m /\ FS9 g j regs m) c.
(* v1.9 pc 0x8237c *)
Definition Inv_B8237c (g : ghost) (c : config) : Prop := exists j, Inv_B8237c_at g j c.
(* F16 (0x823d8): before the record_sum_closes call 0x823dc (image A inlines the sum; its loop head 0x821ac).
   Adopt 6: a Theorem Labs lane's entry text (lib/B/Prog/Seg/F16.v on a working branch f49d239439, Inv_B82370_loc;
   a Theorem Labs lane's `exists (j : nat)` is the official index j): the F17 entry facts with their placements against the
   identity record [fr + 2688, fr + 2726) the ingest writes, the record_sum_closes argument [A+120] with its N = a1
   bytes and their closing sum, the first-fragment state with the parser's address cell, and the ingest
   arguments with the identity record's 38 cells. Only the turn that closes a record reaches
   0x823d8 (t_rf j = 1: class FgClose, which needs fg_fr, so 50 <= len_j), but fg_fr does not test bytes 12 / 13,
   so [A+272] (= b2z t_8819) is in the t_8819 form and rec_inv / the two compare operands are under
   t_8819 = true (see FRB). Then the conjuncts of prover a Theorem Labs lane's Inv_B82370_loc (Seg/F16.v (a version not in this delivery; written on a working branch e57b0367fa)) that another Theorem Labs lane's
   text lacks: FLV, t_rf j = 1, a1 = pll + 5, the record's post bytes t_FGf with its 72 bytes addressable,
   frag_ok, the address cell [fr+256] = fg_addr, the identity record's 38 bytes; and FTURN, RECF.
   v1.9.0 address check (fuzz_ctrl.c v1.9.0:398-400; 0x823e4-0x82440): `first->have` (0x823e4-0x823ec, a0 =
   [A+168] = fr + 2880; FSj gives the u32 there), the cell [fr + 256] (0x823f0-0x823f4, [A+288] = fr + 256) and
   joined_byte (first, block, 9) << 8 | joined_byte (first, block, 10) (0x82414 / 0x82438 with a0 = [A+168],
   a1 = [A+312] = Phi + 18; the callee reads first's n and body, FSj, and the block bytes, FTURN), so the cut's
   address block (position 13, inner 17) keeps its v1.8 binders HAVE NB AD A0V A1V and 13 inner positions: have
   (u32 at fr + 2880, <> 0, range), n (byte at fr + 2884, range), A0V / A1V now the pointers joined_byte gets
   ([A+168] = fr + 2880, [A+312] = Phi + 18), the cell [fr + 256] and AD = joined_addr (first state, frame
   bytes) in place of the patched two-arm disjunction. The patched image read the two address bytes
   from its first-fragment spills [A+128] / [A+136] when nb > 10 and from fragb fr + 17 / + 18 otherwise (with
   the prologue flag [A+72] = 0); both arms are gone. In v1.9.0 the record pointer kp = fr + 176 is [A+280]
   (patched s6). *)
(* v1.9 pc 0x823d8 *)
Definition Inv_B823d8_at (g : ghost) (j : nat) (c : config) : Prop :=
  exists phi, CUTST g 0x823d8 (hb1 phi (AC.a_size (flen g j)))
    (fun fr regs m =>
       g_n g < 2 ^ 26 /\ (j <= 255)%nat /\ HB m phi (flen g j) /\ LK g fr j regs m /\
       rg regs 20 (flen g j) /\ spill regs m 224 (g_p g + t_body (g_in g) j) /\
       FM g j phi fr regs m /\ FSj g fr j regs m /\
       rg regs 18 phi /\ rg regs 27 (-8) /\ addressable m phi 50 /\
       (exists rb, bytes_at rsegs m phi rb /\ length rb = 38%nat) /\
       (exists A kp,
          rg regs 9 A /\ q64 m (A + 280) kp /\ rg regs 24 (t_k (g_in g) j) /\
          0 <= A < 2 ^ 64 /\ AC.aspZ regs <= A /\ fr + FRAME_BYTES <= A /\
          (forall a, fr + 2880 <= a < fr + 2920 -> app_mem a /\ AC.GT <= a) /\
          (exists w272, q64 m (A + 272) w272 /\ 0 <= w272 < 2 ^ 64 /\
             (t_8819 (g_in g) j = true -> w272 <> 0) /\ (t_8819 (g_in g) j = false -> w272 = 0)) /\
          (phi + 50 <= fr + 2880 \/ fr + 2920 <= phi) /\
          (kp + 22 <= fr + 2880 \/ fr + 2920 <= kp + 20) /\
          (phi + 50 <= AC.aspZ regs - BW.BCMP_WRAP_K \/ AC.aspZ regs <= phi) /\
          (kp + 22 <= AC.aspZ regs - BW.BCMP_WRAP_K \/ AC.aspZ regs <= kp) /\
          (phi + 50 <= fr + 2688 \/ fr + 2688 + 38 <= phi) /\
          (kp + 22 <= fr + 2688 \/ fr + 2688 + 38 <= kp + 20) /\
          (t_8819 (g_in g) j = true ->
             rec_inv g j phi A kp m /\
             (exists (L : Z) (ls rs : list byte),
                q64 m (A + 112) L /\ bytes_at rsegs m L ls /\ length ls = 6%nat /\
                bytes_at rsegs m phi rs /\ length rs = 6%nat /\ SF.memcmp_model ls rs 6 = Some 0 /\
                addressable m L 6 /\ app_mem (L + 6) /\ app_mem (L + 7) /\
                (L + 6 <= AC.aspZ regs - BW.BCMP_WRAP_K \/ AC.aspZ regs <= L) /\
                (L + 6 <= fr + 2880 \/ fr + 2920 <= L) /\
                (L + 6 <= fr + 2688 \/ fr + 2688 + 38 <= L)) /\
             (exists (L2 : Z) (ls2 rs2 : list byte),
                q64 m (A + 96) L2 /\ bytes_at rsegs m L2 ls2 /\ length ls2 = 6%nat /\
                bytes_at rsegs m (phi + 6) rs2 /\ length rs2 = 6%nat /\ SF.memcmp_model ls2 rs2 6 = Some 0 /\
                addressable m L2 6 /\ app_mem (L2 + 6) /\ app_mem (L2 + 7) /\
                (L2 + 6 <= AC.aspZ regs - BW.BCMP_WRAP_K \/ AC.aspZ regs <= L2) /\
                (L2 + 6 <= fr + 2880 \/ fr + 2920 <= L2) /\
                (L2 + 6 <= fr + 2688 \/ fr + 2688 + 38 <= L2))) /\
          (exists (N : Z) (bs : list byte),
             rg regs 11 N /\ q64 m (A + 120) (fragb fr + 15) /\
             1 <= N /\ fragb fr + 15 + N <= fr + FRAME_BYTES /\
             bytes_at rsegs m (fragb fr + 15) bs /\ length bs = Z.to_nat N /\
             RcRec.recsum bs = 0 /\ addressable m (fragb fr + 15) N) /\
          (exists (HAVE NB AD A0V A1V : Z),
             u32 m (fr + 2880) HAVE /\ HAVE <> 0 /\ 0 <= HAVE < 2 ^ 64 /\
             b8 m (fr + 2884) NB /\ 0 <= NB < 2 ^ 64 /\
             q64 m (A + 168) A0V /\ A0V = fr + 2880 /\
             q64 m (A + 312) A1V /\ A1V = phi + 18 /\
             q64 m (A + 288) (fr + 256) /\ u16 m (fr + 256) AD /\ 0 <= AD < 65536 /\
             AD = joined_addr (fst_at (g_in g) j) (t_g (g_in g) j)) /\
          (exists (PLL : Z) (idb pb : list byte),
             q64 m (A + 304) (fr + 272) /\ q64 m (fr + 272) (fragb fr + 19) /\
             q64 m (A + 296) (fr + 304) /\ q64 m (fr + 304) PLL /\
             q64 m (A + 176) (fr + 2688) /\
             0 <= PLL /\ fragb fr + 19 + PLL <= fr + FRAME_BYTES /\
             length pb = Z.to_nat PLL /\ bytes_at rsegs m (fragb fr + 19) pb /\
             addressable m (fragb fr + 19) PLL /\
             length idb = 38%nat /\ LSt.rw_cells rsegs m (fr + 2688) [LCl.CB 38 idb] /\
             addressable m (fr + 2688) 38)) /\
       FLV g fr j regs m /\ t_rf (g_in g) j = 1 /\
       rg regs 11 (f_pll (t_FG (g_in g) j) (t_g (g_in g) j) + 5) /\
       bytes_at rsegs m (fragb fr) (t_FGf (g_in g) j) /\ addressable m (fragb fr) 72 /\
       frag_ok (t_FG (g_in g) j) /\
       u16 m (fr + 256) (RcFrag.fg_addr (t_FG (g_in g) j) (t_g (g_in g) j)) /\
       (exists idb, bytes_at rsegs m (fr + 2688) idb /\ length idb = 38%nat) /\
       FTURN g j phi regs m /\ RECF g fr j m /\ FS9 g j regs m)
    c.
(* v1.9 pc 0x823d8 *)
Definition Inv_B823d8 (g : ghost) (c : config) : Prop := exists j, Inv_B823d8_at g j c.
(* F17 (0x82464) opens_record entry: a Theorem Labs lane's Inv_B823e0_loc (lib/B/Prog/Seg/F17.v (not in this delivery) on a working branch
   f49d239439): s2 = Phi, the first 50 bytes of Phi addressable (v1.9, for opens_record's memcpy 0x82630; patched 40), s11 = -8, the first-fragment window (v1.9: the local
   `first`, [fr + 2880, fr + 2920), app memory above GT; patched: the spills [A+112, A+144) in high app memory), and the
   F18 entry facts (kp = [A+280], k = s8, [A+272], rec_inv, the two bcmp operands [A+112] / [A+96]); for the split
   cut 0x82468 also s4 = len and [A+224] (FCUTP's), FM and FSj. mem_inv,
   GT <= fr, aspZ <= APPMEM_END and the frame-vs-scratch facts come from FRA (not carried). 0x82464 follows F16
   (t_rf j = 1, so 50 <= len_j); [A+272] is in the t_8819 form and rec_inv / the compare operands are under
   t_8819 = true, as at 0x823d8. Adopt 6: FTURN, and the records of turn j + 1 (RECS: the record ingest 0x82460
   has run; the fragment record is the fragment call's). *)
(* v1.9 pc 0x82464 *)
Definition Inv_B82464_at (g : ghost) (j : nat) (c : config) : Prop :=
  exists phi : Z,
    CUTST g 0x82464 (hb1 phi (AC.a_size (flen g j)))
      (fun fr regs m =>
         g_n g < 2 ^ 26 /\ (j <= 255)%nat /\ HB m phi (flen g j) /\ LK g fr j regs m /\
         rg regs 20 (flen g j) /\ spill regs m 224 (g_p g + t_body (g_in g) j) /\
         FM g j phi fr regs m /\ FSj g fr j regs m /\
         rg regs 18 phi /\ addressable m phi 50 /\
         (exists rb, bytes_at rsegs m phi rb /\ (38 <= length rb)%nat) /\
         (exists v0, rg regs 10 v0 /\ 0 <= v0 < 2 ^ 63) /\
         rg regs 27 (-8) /\
         (exists A kp, rg regs 9 A /\ q64 m (A + 280) kp /\
            (forall a, fr + 2880 <= a < fr + 2920 -> app_mem a /\ AC.GT <= a) /\
            (exists w272, q64 m (A + 272) w272 /\ 0 <= w272 < 2 ^ 64 /\
               (t_8819 (g_in g) j = true -> w272 <> 0) /\ (t_8819 (g_in g) j = false -> w272 = 0)) /\
            rg regs 24 (t_k (g_in g) j) /\
            (phi + 50 <= fr + 2880 \/ fr + 2920 <= phi) /\
            (kp + 22 <= fr + 2880 \/ fr + 2920 <= kp + 20) /\
            (phi + 50 <= AC.aspZ regs - BW.BCMP_WRAP_K \/ AC.aspZ regs <= phi) /\
            (kp + 22 <= AC.aspZ regs - BW.BCMP_WRAP_K \/ AC.aspZ regs <= kp) /\
            (t_8819 (g_in g) j = true ->
               rec_inv g j phi A kp m /\
               (exists (L : Z) (ls rs : list byte),
                  q64 m (A + 112) L /\ bytes_at rsegs m L ls /\ (6 <= length ls)%nat /\
                  bytes_at rsegs m phi rs /\ (6 <= length rs)%nat /\ SF.memcmp_model ls rs 6 = Some 0 /\
                  addressable m L 6 /\ app_mem (L + 6) /\ app_mem (L + 7) /\
                  (L + 6 <= AC.aspZ regs - BW.BCMP_WRAP_K \/ AC.aspZ regs <= L) /\
                  (L + 6 <= fr + 2880 \/ fr + 2920 <= L)) /\
               (exists (L2 : Z) (ls2 rs2 : list byte),
                  q64 m (A + 96) L2 /\ bytes_at rsegs m L2 ls2 /\ (6 <= length ls2)%nat /\
                  bytes_at rsegs m (phi + 6) rs2 /\ (6 <= length rs2)%nat /\ SF.memcmp_model ls2 rs2 6 = Some 0 /\
                  addressable m L2 6 /\ app_mem (L2 + 6) /\ app_mem (L2 + 7) /\
                  (L2 + 6 <= AC.aspZ regs - BW.BCMP_WRAP_K \/ AC.aspZ regs <= L2) /\
                  (L2 + 6 <= fr + 2880 \/ fr + 2920 <= L2)))) /\
         FTURN g j phi regs m /\ RECS g fr j m /\ FS9 g j regs m)
      c.
(* v1.9 pc 0x82464 *)
Definition Inv_B82464 (g : ghost) (c : config) : Prop := exists j, Inv_B82464_at g j c.
(* F17 internal split (twin of image A's Inv_A822a0_at, pre-v1.9 0x821c4): the opens_record entry block 0x82468, reached from F15 (rf <> 1
   at 0x8237c) and from F17's fall-through (0x82464). a Theorem Labs lane's Inv_B823e4_loc (Seg/F17.v (not in this delivery), f49d239439): the
   0x82464 text at this pc without its a0 clause, under FCUTP. Every frame reaches 0x82468 (the rf <> 1 edge
   takes the short and the non-8819 frames), so, as image A's Inv_A822a0_at (push 6c5b): Phi's first 50 bytes addressable
   (v1.9: opens_record's checked_memcpy 0x82630 reads [Phi + 27, Phi + 27 + n), n = Phi[26] <= 22 (0x825d4-0x825d8),
   so up to Phi + 48; reached only when len >= 50, 0x82468-0x82474; patched 40) and the Phi placements are under
   50 <= flen g j, [A+272] is in the t_8819 form, and rec_inv / the compare operands are
   under t_8819 = true. Adopt 6: the records of turn j + 1 (RECS) on both edges. *)
(* v1.9 pc 0x82468 *)
Definition Inv_B82468_at (g : ghost) (j : nat) (c : config) : Prop :=
  FCUTP g 0x82468 j
    (fun phi fr regs m =>
       LK g fr j regs m /\ FM g j phi fr regs m /\ FSj g fr j regs m /\
       (50 <= flen g j -> addressable m phi 50 /\ (exists rb, bytes_at rsegs m phi rb /\ (38 <= length rb)%nat)) /\
       rg regs 27 (-8) /\
       (exists A kp, rg regs 9 A /\ q64 m (A + 280) kp /\
          (forall a, fr + 2880 <= a < fr + 2920 -> app_mem a /\ AC.GT <= a) /\
          (exists w272, q64 m (A + 272) w272 /\ 0 <= w272 < 2 ^ 64 /\
             (t_8819 (g_in g) j = true -> w272 <> 0) /\ (t_8819 (g_in g) j = false -> w272 = 0)) /\
          rg regs 24 (t_k (g_in g) j) /\
          (kp + 22 <= fr + 2880 \/ fr + 2920 <= kp + 20) /\
          (kp + 22 <= AC.aspZ regs - BW.BCMP_WRAP_K \/ AC.aspZ regs <= kp) /\
          (50 <= flen g j ->
             (phi + 50 <= fr + 2880 \/ fr + 2920 <= phi) /\
             (phi + 50 <= AC.aspZ regs - BW.BCMP_WRAP_K \/ AC.aspZ regs <= phi)) /\
          (t_8819 (g_in g) j = true ->
             rec_inv g j phi A kp m /\
             (exists (L : Z) (ls rs : list byte),
                q64 m (A + 112) L /\ bytes_at rsegs m L ls /\ (6 <= length ls)%nat /\
                bytes_at rsegs m phi rs /\ (6 <= length rs)%nat /\ SF.memcmp_model ls rs 6 = Some 0 /\
                addressable m L 6 /\ app_mem (L + 6) /\ app_mem (L + 7) /\
                (L + 6 <= AC.aspZ regs - BW.BCMP_WRAP_K \/ AC.aspZ regs <= L) /\
                (L + 6 <= fr + 2880 \/ fr + 2920 <= L)) /\
             (exists (L2 : Z) (ls2 rs2 : list byte),
                q64 m (A + 96) L2 /\ bytes_at rsegs m L2 ls2 /\ (6 <= length ls2)%nat /\
                bytes_at rsegs m (phi + 6) rs2 /\ (6 <= length rs2)%nat /\ SF.memcmp_model ls2 rs2 6 = Some 0 /\
                addressable m L2 6 /\ app_mem (L2 + 6) /\ app_mem (L2 + 7) /\
                (L2 + 6 <= AC.aspZ regs - BW.BCMP_WRAP_K \/ AC.aspZ regs <= L2) /\
                (L2 + 6 <= fr + 2880 \/ fr + 2920 <= L2)))) /\
       RECS g fr j m /\ FS9 g j regs m)
    c.
(* v1.9 pc 0x82468 *)
Definition Inv_B82468 (g : ghost) (c : config) : Prop := exists j, Inv_B82468_at g j c.
(* F18 (0x82634) and its exit 0x8264c (F19's entry, the return point of the wrapper_bcmp call 0x82648): a Theorem Labs lane's
   cut texts (lib/B/Prog/Seg/F18.v). Phi = s2, k = s8, the record pointer kp = s6, the record invariant rec_inv, the
   operands of the two bcmp calls F18 / F19 ([A+88] against Phi, [A+80] against Phi+6: 6 equal bytes, addressable,
   apart from the wrapper's stack scratch [sp - BCMP_WRAP_K, sp)), at 0x82634 the word [A+272] <> 0 (the beqz at
   0x82638 not taken) and at 0x8264c a0 = 0 (this bcmp's result; F19's bnez not taken). FRA / fra_app give the
   frame's app memory above GT and MemNorm.evt_normalize gives mem_inv from ro_agree (push 5c). FRA gives the
   rest of the local text: sp <= APPMEM_END (sp <= A <= S < APPMEM_END), and the
   frame apart from the scratch (fra_frame at K = BCMP_WRAP_K = 4560).
   Adopt 6 short-arm guards (as image A's 0x823a4, push 6c5b): every frame reaches 0x82634 (the bnez at 0x82474
   for len < 50 or sum_ok false, and the opens_record body's exits), and 0x82638 `beqz [A+272]` leaves for 0x82abc
   exactly when t_8819 j is false ([A+272] = b2z t_8819, see FRB). So at 0x82634 the word is pinned by t_8819, and
   a Theorem Labs lane's w272 <> 0, rec_inv and the two compare operands are under t_8819 = true. 0x8264c and later F19-F22 cuts
   lie after the beqz (t_8819 = true, 50 <= len_j) and keep a Theorem Labs lane's unguarded text. *)
(* v1.9 pc 0x82634 *)
Definition Inv_B82634_at (g : ghost) (j : nat) (c : config) : Prop :=
  exists phi : Z,
    CUTST g 0x82634 (hb1 phi (AC.a_size (flen g j)))
      (fun fr regs m =>
         g_n g < 2 ^ 26 /\ (j <= 255)%nat /\ HB m phi (flen g j) /\ LK g fr j regs m /\
         rg regs 20 (flen g j) /\ FM g j phi fr regs m /\
         (exists (A kp w272 : Z),
            rg regs 9 A /\ 0 <= A < 2 ^ 64 /\ AC.aspZ regs <= A /\
            rg regs 18 phi /\ rg regs 24 (t_k (g_in g) j) /\ q64 m (A + 280) kp /\
            q64 m (A + 272) w272 /\ 0 <= w272 < 2 ^ 64 /\
            (t_8819 (g_in g) j = false -> w272 = 0) /\
            (t_8819 (g_in g) j = true ->
               w272 <> 0 /\ rec_inv g j phi A kp m /\
               exists (L L2 : Z) (ls rs ls2 rs2 : list byte),
                 q64 m (A + 112) L /\ 0 <= L < 2 ^ 64 /\
                 bytes_at rsegs m L ls /\ (6 <= length ls)%nat /\ bytes_at rsegs m phi rs /\ (6 <= length rs)%nat /\
                 SF.memcmp_model ls rs 6 = Some 0 /\
                 addressable m L 6 /\ addressable m phi 6 /\
                 app_mem (L + 6) /\ app_mem (L + 7) /\ app_mem (phi + 6) /\ app_mem (phi + 7) /\
                 (L + 6 <= AC.aspZ regs - BW.BCMP_WRAP_K \/ AC.aspZ regs <= L) /\
                 (phi + 6 <= AC.aspZ regs - BW.BCMP_WRAP_K \/ AC.aspZ regs <= phi) /\
                 (phi + 50 <= AC.aspZ regs - BW.BCMP_WRAP_K \/ AC.aspZ regs <= phi) /\
                 (kp + 22 <= AC.aspZ regs - BW.BCMP_WRAP_K \/ AC.aspZ regs <= kp) /\
                 q64 m (A + 96) L2 /\ 0 <= L2 < 2 ^ 64 /\
                 bytes_at rsegs m L2 ls2 /\ (6 <= length ls2)%nat /\ bytes_at rsegs m (phi + 6) rs2 /\
                 (6 <= length rs2)%nat /\
                 SF.memcmp_model ls2 rs2 6 = Some 0 /\
                 addressable m L2 6 /\ addressable m (phi + 6) 6 /\
                 app_mem (L2 + 6) /\ app_mem (L2 + 7) /\ app_mem (phi + 12) /\ app_mem (phi + 13) /\
                 (L2 + 6 <= AC.aspZ regs - BW.BCMP_WRAP_K \/ AC.aspZ regs <= L2) /\
                 (phi + 12 <= AC.aspZ regs - BW.BCMP_WRAP_K \/ AC.aspZ regs <= phi + 6))) /\
         FTURN g j phi regs m /\ IFS g fr (S j) regs m)
      c.
(* v1.9 pc 0x82634 *)
Definition Inv_B82634 (g : ghost) (c : config) : Prop := exists j, Inv_B82634_at g j c.
(* v1.9 pc 0x8264c *)
Definition Inv_B8264c_at (g : ghost) (j : nat) (c : config) : Prop :=
  exists phi : Z,
    CUTST g 0x8264c (hb1 phi (AC.a_size (flen g j)))
      (fun fr regs m =>
         g_n g < 2 ^ 26 /\ (j <= 255)%nat /\ HB m phi (flen g j) /\ LK g fr j regs m /\
         rg regs 20 (flen g j) /\ FM g j phi fr regs m /\
         (exists (A kp L2 : Z) (ls2 rs2 : list byte),
            rg regs 9 A /\ 0 <= A < 2 ^ 64 /\ AC.aspZ regs <= A /\
            rg regs 18 phi /\ rg regs 24 (t_k (g_in g) j) /\ q64 m (A + 280) kp /\ rg regs 10 0 /\
            rec_inv g j phi A kp m /\
            q64 m (A + 96) L2 /\ 0 <= L2 < 2 ^ 64 /\
            bytes_at rsegs m L2 ls2 /\ (6 <= length ls2)%nat /\ bytes_at rsegs m (phi + 6) rs2 /\
            (6 <= length rs2)%nat /\
            SF.memcmp_model ls2 rs2 6 = Some 0 /\
            addressable m L2 6 /\ addressable m (phi + 6) 6 /\
            app_mem (L2 + 6) /\ app_mem (L2 + 7) /\ app_mem (phi + 12) /\ app_mem (phi + 13) /\
            (L2 + 6 <= AC.aspZ regs - BW.BCMP_WRAP_K \/ AC.aspZ regs <= L2) /\
            (phi + 12 <= AC.aspZ regs - BW.BCMP_WRAP_K \/ AC.aspZ regs <= phi + 6) /\
            (phi + 50 <= AC.aspZ regs - BW.BCMP_WRAP_K \/ AC.aspZ regs <= phi) /\
            (kp + 22 <= AC.aspZ regs - BW.BCMP_WRAP_K \/ AC.aspZ regs <= kp)) /\
         FTURN g j phi regs m /\ IFS g fr (S j) regs m)
      c.
(* v1.9 pc 0x8264c *)
Definition Inv_B8264c (g : ghost) (c : config) : Prop := exists j, Inv_B8264c_at g j c.
(* F20 (0x82668) entry and exit (a Theorem Labs lane, lib/B/Prog/Seg/F20.v), over the reac_ctrl_checksum_verify call. Entry:
   Phi s2, k s8, a0 = 0, the is_8819 record bytes Phi+14..Phi+17 with zero shadow bytes and the field equalities,
   the 32 checksum bytes at Phi+18 and 6 at Phi+34, the sum flag s9, and the Phi
   vs call-window (K = 16) disjunction. Exit patched 0x826a4: a0 = the checksum result. The frame-apart (fra_frame) and
   aspZ <= APPMEM_END facts are dropped (FRA gives them). *)
(* v1.9 pc 0x82668 *)
Definition Inv_B82668_at (g : ghost) (j : nat) (c : config) : Prop :=
  exists phi, CUTST g 0x82668 (hb1 phi (AC.a_size (flen g j)))
    (fun fr regs m =>
       g_n g < 2 ^ 26 /\ (j <= 255)%nat /\ HB m phi (flen g j) /\ LK g fr j regs m /\
       rg regs 20 (flen g j) /\ FM g j phi fr regs m /\
       rg regs 18 phi /\ rg regs 24 (t_k (g_in g) j) /\ rg regs 10 0 /\
       0 < phi /\ phi + 50 <= 2 ^ 64 /\ 50 <= flen g j /\ 0 <= t_k (g_in g) j < 2 ^ 64 /\
       bytes_at rsegs m (phi + 18) (t_blk (g_in g) j) /\
       bytes_at rsegs m (phi + 34) (RcFrag.bsl (t_g (g_in g) j) 34 6) /\
       rg regs 25 (b2z (t_sum_ok (g_in g) j)) /\
       (phi + 50 <= AC.aspZ regs - 16 \/ AC.aspZ regs <= phi + 18) /\
       FTURN g j phi regs m /\ IFS g fr (S j) regs m /\
       (* The kind record is the one [A+280] = fr + 176 points at (FLI; stored 0x81470, loaded 0x82690 `ld a2,280(s1)`; the patched image had it in s6, from the spill [A+168], loaded patched 0x81df8 and not
          written up to 0x82878), so the halfword the check at 0x82694 (lhu a2,20(a2)) reads is fr + 196, and the
          cut names it instead of an existential pointer (item 5, prover a Theorem Labs lane). *)
       exists v14 v15 v16 v17 field16,
          u16 m (fr + 196) field16 /\
          b8 m (phi + 14) v14 /\ b8 m (phi + 15) v15 /\
          b8 m (phi + 16) v16 /\ b8 m (phi + 17) v17 /\
          0 <= v14 < 256 /\ 0 <= v15 < 256 /\ 0 <= v16 < 256 /\ 0 <= v17 < 256 /\
          b8 m (Z.shiftr (phi + 14) 3 + ASAN_K) 0 /\
          b8 m (Z.shiftr (phi + 15) 3 + ASAN_K) 0 /\
          b8 m (Z.shiftr (phi + 16) 3 + ASAN_K) 0 /\
          b8 m (Z.shiftr (phi + 17) 3 + ASAN_K) 0 /\
          field16 = v14 + 256 * v15 /\
          (if v16 =? 0 then (if v17 =? 0 then 1 else 0) else 0) = (if t_k (g_in g) j =? 1 then 1 else 0)) c.
(* v1.9 pc 0x82668 *)
Definition Inv_B82668 (g : ghost) (c : config) : Prop := exists j, Inv_B82668_at g j c.
(* v1.9 pc 0x82728 *)
Definition Inv_B82728_at (g : ghost) (j : nat) (c : config) : Prop :=
  exists phi, CUTST g 0x82728 (hb1 phi (AC.a_size (flen g j)))
    (fun fr regs m =>
       g_n g < 2 ^ 26 /\ (j <= 255)%nat /\ HB m phi (flen g j) /\ LK g fr j regs m /\
       rg regs 20 (flen g j) /\ FM g j phi fr regs m /\
       rg regs 10 (if RcModel.blocksum (t_blk (g_in g) j) =? 0 then 0 else -1) /\
       rg regs 18 phi /\ rg regs 24 (t_k (g_in g) j) /\
       0 < phi /\ phi + 50 <= 2 ^ 64 /\ 50 <= flen g j /\ 0 <= t_k (g_in g) j < 2 ^ 64 /\
       bytes_at rsegs m (phi + 18) (t_blk (g_in g) j) /\
       bytes_at rsegs m (phi + 34) (RcFrag.bsl (t_g (g_in g) j) 34 6) /\
       rg regs 25 (b2z (t_sum_ok (g_in g) j)) /\
       (phi + 50 <= AC.aspZ regs - 16 \/ AC.aspZ regs <= phi + 18) /\
       FTURN g j phi regs m /\ IFS g fr (S j) regs m) c.
(* v1.9 pc 0x82728 *)
Definition Inv_B82728 (g : ghost) (c : config) : Prop := exists j, Inv_B82728_at g j c.
(* F22 (0x827f8, the 6-byte sum loop head, back edge 0x8281c bne a0,a7,827f8; image A's Inv_A82554_at, pre-v1.9 0x824a8), its join 0x8283c
   (`mv a0,s2` before the head-amp record call, the join of the loop exit and the skip path; no official cut there
   before) and the call's return point 0x82844 (a Theorem Labs lane, lib/B/Prog/Seg/F21.v, F22.v). At 0x827f8: the turn
   index a0 = 0, the sum a1 = 0, the record base a2 = Phi + 34, the T54 bound a3, a7 = 6, the record bytes
   Phi[18] = 4 / Phi[19] = 3 and the zero shadow bytes of Phi + 34 .. Phi + 39. At 0x8283c and 0x82844:
   s7 = t_want_v; at 0x82844 also a0 = t_want_v (the headamp_record_verify result). The frame-apart (fra_frame at
   K = 16) and aspZ <= APPMEM_END facts are dropped (FRA gives them). *)
(* v1.9 pc 0x827f8 *)
Definition Inv_B827f8_at (g : ghost) (j : nat) (c : config) : Prop :=
  exists phi, CUTST g 0x827f8 (hb1 phi (AC.a_size (flen g j)))
    (fun fr regs m =>
       g_n g < 2 ^ 26 /\ (j <= 255)%nat /\ HB m phi (flen g j) /\ LK g fr j regs m /\
       rg regs 20 (flen g j) /\ FM g j phi fr regs m /\
       rg regs 10 0 /\ rg regs 11 0 /\ rg regs 12 (phi + 34) /\ rg regs 13 (2 ^ 64 - (phi + 35)) /\
       rg regs 17 6 /\ rg regs 18 phi /\ rg regs 24 (t_k (g_in g) j) /\
       0 < phi /\ phi + 50 <= 2 ^ 64 /\ 50 <= flen g j /\ 0 <= t_k (g_in g) j < 2 ^ 64 /\
       RcParse.cp_v (t_g (g_in g) j) 18 = 4 /\ RcParse.cp_v (t_g (g_in g) j) 19 = 3 /\
       bytes_at rsegs m (phi + 18) (t_blk (g_in g) j) /\
       bytes_at rsegs m (phi + 34) (RcFrag.bsl (t_g (g_in g) j) 34 6) /\
       (forall i, 0 <= i < 6 -> b8 m (Z.shiftr (phi + 34 + i) 3 + ASAN_K) 0) /\
       rg regs 25 (b2z (t_sum_ok (g_in g) j)) /\
       (forall a, fr <= a < fr + FRAME_BYTES -> app_mem a) /\
       (phi + 50 <= AC.aspZ regs - 16 \/ AC.aspZ regs <= phi + 18) /\
       FTURN g j phi regs m /\ IFS g fr (S j) regs m) c.
(* v1.9 pc 0x827f8 *)
Definition Inv_B827f8 (g : ghost) (c : config) : Prop := exists j, Inv_B827f8_at g j c.
(* v1.9 pc 0x8283c *)
Definition Inv_B8283c_at (g : ghost) (j : nat) (c : config) : Prop :=
  exists phi, CUTST g 0x8283c (hb1 phi (AC.a_size (flen g j)))
    (fun fr regs m =>
       g_n g < 2 ^ 26 /\ (j <= 255)%nat /\ HB m phi (flen g j) /\ LK g fr j regs m /\
       rg regs 20 (flen g j) /\ FM g j phi fr regs m /\
       rg regs 18 phi /\ rg regs 23 (t_want_v (g_in g) j) /\ rg regs 24 (t_k (g_in g) j) /\
       0 < phi /\ phi + 50 <= 2 ^ 64 /\ 50 <= flen g j /\ 0 <= t_k (g_in g) j < 2 ^ 64 /\
       bytes_at rsegs m (phi + 18) (t_blk (g_in g) j) /\
       bytes_at rsegs m (phi + 34) (RcFrag.bsl (t_g (g_in g) j) 34 6) /\
       rg regs 25 (b2z (t_sum_ok (g_in g) j)) /\
       (forall a, fr <= a < fr + FRAME_BYTES -> app_mem a) /\
       (phi + 50 <= AC.aspZ regs - 16 \/ AC.aspZ regs <= phi + 18) /\
       FTURN g j phi regs m /\ IFS g fr (S j) regs m) c.
(* v1.9 pc 0x8283c *)
Definition Inv_B8283c (g : ghost) (c : config) : Prop := exists j, Inv_B8283c_at g j c.
(* v1.9 pc 0x82844 *)
Definition Inv_B82844_at (g : ghost) (j : nat) (c : config) : Prop :=
  exists phi, CUTST g 0x82844 (hb1 phi (AC.a_size (flen g j)))
    (fun fr regs m =>
       g_n g < 2 ^ 26 /\ (j <= 255)%nat /\ HB m phi (flen g j) /\ LK g fr j regs m /\
       rg regs 20 (flen g j) /\ FM g j phi fr regs m /\
       rg regs 10 (t_want_v (g_in g) j) /\
       rg regs 18 phi /\ rg regs 23 (t_want_v (g_in g) j) /\ rg regs 24 (t_k (g_in g) j) /\
       0 < phi /\ phi + 50 <= 2 ^ 64 /\ 50 <= flen g j /\ 0 <= t_k (g_in g) j < 2 ^ 64 /\
       bytes_at rsegs m (phi + 18) (t_blk (g_in g) j) /\
       bytes_at rsegs m (phi + 34) (RcFrag.bsl (t_g (g_in g) j) 34 6) /\
       rg regs 25 (b2z (t_sum_ok (g_in g) j)) /\
       (forall a, fr <= a < fr + FRAME_BYTES -> app_mem a) /\
       (phi + 50 <= AC.aspZ regs - 16 \/ AC.aspZ regs <= phi + 18) /\
       FTURN g j phi regs m /\ IFS g fr (S j) regs m) c.
(* v1.9 pc 0x82844 *)
Definition Inv_B82844 (g : ghost) (c : config) : Prop := exists j, Inv_B82844_at g j c.
(* F24 (v1.9 0x82878; patched 0x827f8): past F23's register swap (0x82848 sd s8,272(s1); 0x8284c mv s8,s9), so s8
   holds the sum flag and k is in [A+272] (FTL); s6 still holds 1 (the frame-loop constant, 0x81ea0), the
   `ld s6,312(s1)` at 0x82878 itself has not run yet.
   Adopt 8 (prover a Theorem Labs lane, F23 / F24 / F25 Qed on a working branch ff75dcbfe64, lib/B/Prog/Seg/Tac_f23.v): the
   local cuts Inv_B827f8_loc / Inv_B82808_loc, verbatim after the earlier official body: their window shell's F27K
   (a Theorem Labs lane's F27CUT, Seg/F27.v; its heap list hb1 phi (flen g j) is FCUTP's a_size form, equal at 50 <= flen) and
   their bodies. F23GAP is a Theorem Labs lane's pair of frame-byte bundles at Phi: FTURN's frame bytes and their 50-byte prefix
   (fturn_g derives the prefix from FTURN). At 0x82878: s4 = len, the fill flag in [A+184], s5 = fr + 128 (v1.9
   0x82868 `ld s5,104(s1)`, kept by the copy; the patched image had it in s7), s7 = 1 (v1.9 0x82874 `li s7,1`,
   stored as the ports shadow byte at 0x8288c `sb s7,20(s3)`), the three ports words the 12-byte checked_memcpy
   0x82870 wrote (-7, -7, -7: __const.check_ports.ports), those 12 bytes marked usable by the shadow stores
   0x82850 / 0x82858 (S(fr) + 16 = 0, S(fr) + 17 = 4), and the block / call-window disjunction (K = 16).
   At 0x82888 (the return point of reac_ports_parse 0x82884): a0 = r = t_rp, s6 = blk = Phi + 18 (0x82878, kept
   by the call), s5 = fr + 128, s7 = 1 and the ports words in their post-parse form PORTS. *)
Definition F23GAP (g : ghost) (j : nat) (phi : Z) (m : word -> option byte) : Prop :=
  bytes_at rsegs m phi (t_phi (g_in g) j) /\
  (50 <= flen g j -> bytes_at rsegs m phi (t_g (g_in g) j)).
(* v1.9 pc 0x82878 *)
Definition Inv_B82878_at (g : ghost) (j : nat) (c : config) : Prop :=
  FCUTP g 0x82878 j (fun phi fr regs m => LK g fr j regs m /\ FTL g j phi fr regs m /\ rg regs 22 1 /\
    IFS g fr (S j) regs m /\
    F27K g j phi fr regs m /\
    rg regs 20 (flen g j) /\ rg regs 23 1 /\ spill regs m 184 (b2z (t_tfill (g_in g) j)) /\
    rg regs 21 (fr + 128) /\
    u32 m (fr + 128) (-7) /\ u32 m (fr + 132) (-7) /\ u32 m (fr + 136) (-7) /\
    addressable m (fr + 128) 12 /\
    F23GAP g j phi m /\
    (phi + 50 <= AC.aspZ regs - 16 \/ AC.aspZ regs <= phi + 18)) c.
(* v1.9 pc 0x82878 *)
Definition Inv_B82878 (g : ghost) (c : config) : Prop := exists j, Inv_B82878_at g j c.
(* v1.9 pc 0x82888 *)
Definition Inv_B82888_at (g : ghost) (j : nat) (c : config) : Prop :=
  FCUTP g 0x82888 j (fun phi fr regs m => LK g fr j regs m /\ FTL g j phi fr regs m /\ IFS g fr (S j) regs m /\
    F27K g j phi fr regs m /\
    rg regs 10 (t_rp (g_in g) j) /\ rg regs 20 (flen g j) /\ rg regs 23 1 /\
    spill regs m 184 (b2z (t_tfill (g_in g) j)) /\ rg regs 22 (phi + 18) /\
    PORTS g fr j m /\
    F23GAP g j phi m /\
    (phi + 50 <= AC.aspZ regs - 16 \/ AC.aspZ regs <= phi + 18) /\
    rg regs 21 (fr + 128)) c.
(* v1.9 pc 0x82888 *)
Definition Inv_B82888 (g : ghost) (c : config) : Prop := exists j, Inv_B82888_at g j c.
(* F26 (v1.9 0x828a4; patched 0x82828) and F27 (v1.9 0x828b4; patched 0x82838) (a Theorem Labs lane, lib/B/Prog/Seg/F26.v,
   F27.v), over the reac_ports_unknown call. The F27K window state plus: s9 = r = t_rp, a0 / s7 = unk = t_unk,
   s6 = phi + 18 (F26 only), s5 = fr + 128, PORTS, FIRSTb. F26 also carries the block / call-window disjunction
   (K = 16). FRA / fra_frame / fra_app give the frame-apart, aspZ <= APPMEM_END and frame app-memory facts, and
   MemNorm.evt_normalize gives mem_inv from ro_agree.
   v1.9 re-anchor: the patched cut 0x82838 sat on `li t3,12`, which v1.9 deletes there (the patched 0x8283c
   `bne a0,s7` is v1.9 0x828b4); v1.9 sets t3 = 12 at 0x828f0 on the r = 0 arm, inside F27, before F28's head, so
   no conjunct of the cut named it. The cut is the return point of the second reac_ports_unknown call (0x828b0),
   as before. New in v1.9: F27 reads the three ports words through s5 = fr + 128 (0x828c8 / 0x828d4 / 0x828e0
   `lw a0,k(s5)`; the patched F27 reloaded [A+248] at 0x82850 / 0x82860 / 0x82870), so F26 and F27 carry
   rg regs 21 (fr + 128) as their last conjunct; s5 = fr + 176 (the patched FTL) is gone. Positions: v1.8 kept,
   the s5 fact appended (F26 position 15, F27 position 14; F25 position 13). *)
(* v1.9 pc 0x828a4 *)
Definition Inv_B828a4_at (g : ghost) (j : nat) (c : config) : Prop :=
  exists phi, CUTST g 0x828a4 (hb1 phi (AC.a_size (flen g j)))
    (fun fr regs m => g_n g < 2 ^ 26 /\ (j <= 255)%nat /\ HB m phi (flen g j) /\ F27K g j phi fr regs m /\
       rg regs 20 (flen g j) /\ FTL g j phi fr regs m /\
       rg regs 25 (t_rp (g_in g) j) /\ rg regs 10 (t_unk (g_in g) j) /\ rg regs 22 (phi + 18) /\
       PORTS g fr j m /\ FIRSTb g fr j m /\
       (phi + 50 <= AC.aspZ regs - 16 \/ AC.aspZ regs <= phi + 18) /\
       FTURN g j phi regs m /\ IFS g fr (S j) regs m /\
       rg regs 21 (fr + 128)) c.
(* v1.9 pc 0x828a4 *)
Definition Inv_B828a4 (g : ghost) (c : config) : Prop := exists j, Inv_B828a4_at g j c.
Definition Inv_B828b4_at (g : ghost) (j : nat) (c : config) : Prop :=
  exists phi, CUTST g 0x828b4 (hb1 phi (AC.a_size (flen g j)))
    (fun fr regs m => g_n g < 2 ^ 26 /\ (j <= 255)%nat /\ HB m phi (flen g j) /\ F27K g j phi fr regs m /\
       rg regs 20 (flen g j) /\ FTL g j phi fr regs m /\
       rg regs 25 (t_rp (g_in g) j) /\ rg regs 23 (t_unk (g_in g) j) /\ rg regs 10 (t_unk (g_in g) j) /\
       PORTS g fr j m /\ FIRSTb g fr j m /\
       FTURN g j phi regs m /\ IFS g fr (S j) regs m /\
       rg regs 21 (fr + 128)) c.
Definition Inv_B828b4 (g : ghost) (c : config) : Prop := exists j, Inv_B828b4_at g j c.
(* F28 (0x8292c): the port-slot loop head (back edge 0x829b8 bnez a7,8292c), image A's patched 0x825b0.
   Adopt 12 (prover a Theorem Labs lane, F26 / F27 / F29 Qed on a working branch f3d87d8368, lib/B/Prog/Seg/F27.v): F28GAP,
   a Theorem Labs lane's gap of F28's entry, verbatim: the F27K window state, r = t_rp = 0 (0x828c4 `beqz s9` taken), s7 = unk
   (0x828a4 `mv s7,a0`), PORTS, FIRSTb, and the loop registers that patched 0x82838 / 0x828fc-0x82928 set: a0 = a4 =
   blk + 8, a6 = -8 - blk (s11 - blk), a7 = 12, a1 = a2 = a3 = a5 = 0, t3 = 12 (blk = phi + 18).
   The cut is entered once; the 12-turn loop is internal to seg_F28 (Seg/F28.v f28_loop, by induction on the
   turns left, then f28_tail to 0x82aa4), so the back edge 0x829b8 never re-enters 0x8292c through this cut and
   the first-turn values are unconditional here. On turn i the loop head has a0 = a4 = blk + 8 + i, a7 = 12 - i
   and a1 / a2 / a3 / a5 the counts over the first i codes; the body 0x8292c-0x829b8 writes only t0, t1, t2, a0,
   a1, a2, a3, a4, a5, a7 and no memory, so a6, t3, s7, F27K, PORTS and FIRSTb hold on every turn. *)
Definition F28GAP (g : ghost) (j : nat) (phi fr : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  F27K g j phi fr regs m /\
  t_rp (g_in g) j = 0 /\ rg regs 23 (t_unk (g_in g) j) /\
  PORTS g fr j m /\ FIRSTb g fr j m /\
  rg regs 10 (phi + 26) /\ rg regs 14 (phi + 26) /\ rg regs 16 (-8 - (phi + 18)) /\ rg regs 17 12 /\
  rg regs 11 0 /\ rg regs 12 0 /\ rg regs 13 0 /\ rg regs 15 0 /\ rg regs 28 12.
(* v1.9 pc 0x8292c *)
Definition Inv_B8292c_at (g : ghost) (j : nat) (c : config) : Prop :=
  FCUTP g 0x8292c j (fun phi fr regs m => LK g fr j regs m /\ FTL g j phi fr regs m /\ IFS g fr (S j) regs m /\
    F28GAP g j phi fr regs m) c.
(* v1.9 pc 0x8292c *)
Definition Inv_B8292c (g : ghost) (c : config) : Prop := exists j, Inv_B8292c_at g j c.
(* v1.9 pc 0x82aa4 *)
Definition Inv_B82aa4_at (g : ghost) (j : nat) (c : config) : Prop :=
  FCUTP g 0x82aa4 j (fun phi fr regs m => LK g fr j regs m /\ FTL g j phi fr regs m /\ IFS g fr (S j) regs m) c.
(* v1.9 pc 0x82aa4 *)
Definition Inv_B82aa4 (g : ghost) (c : config) : Prop := exists j, Inv_B82aa4_at g j c.
(* X30 (0x82abc, a Theorem Labs lane): F29 has undone F23's swap (0x82ab4 mv s9,s8; patched 0x82a50 mv s5,s8; 0x82ab8
   ld s8,272(s1)), so s9 = the sum flag, s6 = 1 and s8 = k again, with the fill flag in [A+184] (FTK; the patched image had s5 = [tfill], s6 = fr + 176). Adopt 6 (a Theorem Labs lane): the block spill [A+312]
   (FM's / FTL's; stored only at 0x82054 / 0x820d8), which F31's PT32 at 0x82af8 reads; both edges (F29 and
   0x82638 `beqz [A+272]`) carry it. The Phi bytes come with FTURN (FCUTP). *)
(* v1.9 pc 0x82abc *)
Definition Inv_B82abc_at (g : ghost) (j : nat) (c : config) : Prop :=
  FCUTP g 0x82abc j (fun phi fr regs m => LK g fr j regs m /\ FTK g j fr regs m /\ IFS g fr (S j) regs m /\
    spill regs m 312 (if t_big (g_in g) j then phi + 18 else 0)) c.
(* v1.9 pc 0x82abc *)
Definition Inv_B82abc (g : ghost) (c : config) : Prop := exists j, Inv_B82abc_at g j c.
(* F31 (0x82af8) and its exits (a Theorem Labs lane, lib/B/Prog/Seg/F31.v). Entry 0x82af8: the classify result in a0, the
   o / our[] / event spills and bytes, and PT32's pass-through. Exit 0x82b38 (bcmp return): a0 = the compare
   result as the OUR match. Exit 0x82b5c (bnez a0 at 0x82af8; no official cut before). The frame-placement and
   aspZ <= APPMEM_END facts are not carried (FRA / fra_frame give them). *)
(* v1.9 pc 0x82af8 *)
Definition Inv_B82af8_at (g : ghost) (j : nat) (c : config) : Prop :=
  exists phi, CUTST g 0x82af8 (hb1 phi (AC.a_size (flen g j)))
    (fun fr regs m => g_n g < 2 ^ 26 /\ (j <= 255)%nat /\ HB m phi (flen g j) /\ LK g fr j regs m /\
       FTK g j fr regs m /\
       rg regs 10 (RcClassify.cl_r (t_cls (g_in g) j)) /\
       spill regs m 144 (fr + 452) /\ spill regs m 264 (fr + 2624) /\ spill regs m 216 (fr + 448) /\
       bytes_at rsegs m (fr + 448) (t_B (g_in g) j) /\
       addressable m (fr + 452) 6 /\ addressable m (fr + 2624) 6 /\
       spill regs m 184 (b2z (t_tfill (g_in g) j)) /\ rg regs 25 (b2z (t_sum_ok (g_in g) j)) /\
       spill regs m 192 (fr + 528) /\ (forall e, t_cls (g_in g) j = Some e -> u32 m (fr + 528) e) /\
       PT32 g j phi fr regs m /\
       FTURN g j phi regs m /\ IFS g fr (S j) regs m) c.
(* v1.9 pc 0x82af8 *)
Definition Inv_B82af8 (g : ghost) (c : config) : Prop := exists j, Inv_B82af8_at g j c.
(* v1.9 pc 0x82b38 *)
Definition Inv_B82b38_at (g : ghost) (j : nat) (c : config) : Prop :=
  exists phi, CUTST g 0x82b38 (hb1 phi (AC.a_size (flen g j)))
    (fun fr regs m => g_n g < 2 ^ 26 /\ (j <= 255)%nat /\ HB m phi (flen g j) /\ LK g fr j regs m /\
       FTK g j fr regs m /\
       t_cls (g_in g) j <> None /\
       (getr regs 10 = Z_to_bv 64 0 <-> firstn 6 (skipn 4 (t_B (g_in g) j)) = OUR (g_in g)) /\
       spill regs m 184 (b2z (t_tfill (g_in g) j)) /\ rg regs 25 (b2z (t_sum_ok (g_in g) j)) /\
       spill regs m 192 (fr + 528) /\ (forall e, t_cls (g_in g) j = Some e -> u32 m (fr + 528) e) /\
       PT32 g j phi fr regs m /\
       FTURN g j phi regs m /\ IFS g fr (S j) regs m) c.
(* v1.9 pc 0x82b38 *)
Definition Inv_B82b38 (g : ghost) (c : config) : Prop := exists j, Inv_B82b38_at g j c.
(* v1.9 pc 0x82b5c *)
Definition Inv_B82b5c_at (g : ghost) (j : nat) (c : config) : Prop :=
  exists phi, CUTST g 0x82b5c (hb1 phi (AC.a_size (flen g j)))
    (fun fr regs m => g_n g < 2 ^ 26 /\ (j <= 255)%nat /\ HB m phi (flen g j) /\ LK g fr j regs m /\
       FTK g j fr regs m /\
       PT32 g j phi fr regs m /\
       FTURN g j phi regs m /\ IFS g fr (S j) regs m) c.
(* v1.9 pc 0x82b5c *)
Definition Inv_B82b5c (g : ghost) (c : config) : Prop := exists j, Inv_B82b5c_at g j c.
(* F33 (0x82bcc) and the row-loop cuts (a Theorem Labs lane, lib/B/Prog/Seg/F33.v). Entry 0x82bcc: the catalogue result
   a0 = CAT (= BOX_CATALOGUE), s7 = fr + 32 with the count 11 there, and PTL's pass-through state. FRA gives
   aspZ <= APPMEM_END (dropped from the local text). *)
(* v1.9 pc 0x82bcc *)
Definition Inv_B82bcc_at (g : ghost) (j : nat) (c : config) : Prop :=
  exists phi, CUTST g 0x82bcc (hb1 phi (AC.a_size (flen g j)))
    (fun fr regs m =>
       g_n g < 2 ^ 26 /\ (j <= 255)%nat /\ HB m phi (flen g j) /\ LK g fr j regs m /\
       FTK g j fr regs m /\
       t_rowsel (g_in g) j = true /\
       rg regs 10 CAT /\ rg regs 23 (fr + 32) /\ q64 m (fr + 32) 11 /\
       rg regs 18 phi /\ rg regs 20 (t_len (g_in g) j) /\ spill regs m 152 (fr + 64) /\
       bytes_at rsegs m phi (t_phi (g_in g) j) /\
       (Z.of_nat (length (t_phi (g_in g) j)) <= flen g j) /\ spill regs m 160 (fr + 32) /\
       stk rsegs m fr (fr + FRAME_BYTES) /\
       spill regs m 312 (phi + 18) /\
       FTURN g j phi regs m /\ IFS g fr (S j) regs m) c.
(* v1.9 pc 0x82bcc *)
Definition Inv_B82bcc (g : ghost) (c : config) : Prop := exists j, Inv_B82bcc_at g j c.
(* row_of_block (W00) carries the extra row index i : nat (0 <= i <= 10); 0x82bf4 is on the row loop (head 0x82be4,
   back edge 0x82c80 bltu s9,a0,82be4). F34's entry carries RL at row i. Adopt 6 (a Theorem Labs lane): s8 = k only at row 0 -
   F34's 0x82c08 `add s8,a0,s5` sets s8 to row i's address (RLc), and neither F36's path 0x82c38-0x82c80 nor the
   row head 0x82be4-0x82bf0 writes s8 again - so the conjunct is `i = 0 -> s8 = k` (k stays in [A+272]). s6 =
   fr + 176 holds at every row head (patched 0x82bec / patched 0x82c08 `ld s6,168(s1)` undo 0x82c18). *)
(* v1.9 pc 0x82bf4 *)
Definition Inv_B82bf4_at (g : ghost) (j i : nat) (c : config) : Prop :=
  exists phi, CUTST g 0x82bf4 (hb1 phi (AC.a_size (flen g j)))
    (fun fr regs m => g_n g < 2 ^ 26 /\ (j <= 255)%nat /\ HB m phi (flen g j) /\ LK g fr j regs m /\
       rg regs 22 1 /\ (i = 0%nat -> rg regs 24 (t_k (g_in g) j)) /\
       spill regs m 272 (t_k (g_in g) j) /\ True (* v1.9: [A+248] not read after 0x8246c *) /\
       RL g j i phi fr regs m /\
       FTURN g j phi regs m /\ IFS g fr (S j) regs m) c.
(* v1.9 pc 0x82bf4 *)
Definition Inv_B82bf4 (g : ghost) (c : config) : Prop := exists j i, Inv_B82bf4_at g j i c.
(* 0x82c84 (the target of the beqz at 0x82bcc / 0x82bd8 and the row loop's fall-through after 0x82c80; no official
   cut before): no row matched (t_want_m = 0), and PTL. Adopt 10 (a Theorem Labs lane): s6 = 1 (fr + 176 in the patched image, from 0x82bcc's FTK, or the
   row loop's patched 0x82bec / patched 0x82c08 `ld s6,168(s1)`), which 0x82c84 -> 0x82c94 -> patched 0x82c3c keeps. *)
(* v1.9 pc 0x82c84 *)
Definition Inv_B82c84_at (g : ghost) (j : nat) (c : config) : Prop :=
  exists phi, CUTST g 0x82c84 (hb1 phi (AC.a_size (flen g j)))
    (fun fr regs m => g_n g < 2 ^ 26 /\ (j <= 255)%nat /\ HB m phi (flen g j) /\ LK g fr j regs m /\
       spill regs m 272 (t_k (g_in g) j) /\ True (* v1.9: [A+248] not read after 0x8246c *) /\
       t_want_m (g_in g) j = 0 /\ PTL g j phi fr regs m /\
       FTURN g j phi regs m /\ IFS g fr (S j) regs m /\ rg regs 22 1) c.
(* v1.9 pc 0x82c84 *)
Definition Inv_B82c84 (g : ghost) (c : config) : Prop := exists j, Inv_B82c84_at g j c.
(* 0x82c90 (prover a Theorem Labs lane, lib/B/Prog/Seg/F32.v on a working branch fd33f18705, Inv_B82c2c_loc_at): the target of
   the `bne`s at 0x82b60, 0x82b8c and 0x82bb4 (no official cut before; 0x82c90 li s7,0, then the
   reac_box_catalogue_match call 0x82c9c to the cut patched 0x82c3c): the row of the block is not selected (t_want_m = 0),
   Phi not in the FakeStack, and the pass-through state PT32 that the F31 cuts carry. FRA gives a Theorem Labs lane's AC.aspZ regs
   <= APPMEM_END (sp <= A <= S < APPMEM_END), so the cut does not carry it. Adopt 6: FTK (F32's entry 0x82b5c
   carries it and the three edges 0x82b60 / 0x82b8c / 0x82bb4 write only a0 / a1), FTURN and IFS (S j). *)
(* v1.9 pc 0x82c90 *)
Definition Inv_B82c90_at (g : ghost) (j : nat) (c : config) : Prop :=
  exists phi, CUTST g 0x82c90 (hb1 phi (AC.a_size (flen g j)))
    (fun fr regs m => g_n g < 2 ^ 26 /\ (j <= 255)%nat /\ HB m phi (flen g j) /\ LK g fr j regs m /\
       t_want_m (g_in g) j = 0 /\
       ~ AC.a_in_fs AC.ASYMS m phi /\
       PT32 g j phi fr regs m /\
       FTK g j fr regs m /\ FTURN g j phi regs m /\ IFS g fr (S j) regs m) c.
(* v1.9 pc 0x82c90 *)
Definition Inv_B82c90 (g : ghost) (c : config) : Prop := exists j, Inv_B82c90_at g j c.
(* F35 entry (0x82c24, the return point of declaration_of 0x82c20), with prover a Theorem Labs lane's conjuncts of
   Inv_B82bc0_loc_at (Seg/F34.v (a version not in this delivery; from a working branch 44ac51d3f4)): the earlier official body is the first group; then RLc (row i's
   loop state), the call's result a0 = 1 (the beqz at 0x82c24 not taken) and row i's declaration in the slot
   [fr + 64, fr + 96) with the slot addressable, which F35's bcmp reads. *)
(* v1.9 pc 0x82c24 *)
Definition Inv_B82c24_at (g : ghost) (j i : nat) (c : config) : Prop :=
  FCUTP g 0x82c24 j (fun phi fr regs m => LK g fr j regs m /\ (i <= 10)%nat /\
    spill regs m 272 (t_k (g_in g) j) /\ True (* v1.9: [A+248] not read after 0x8246c *) /\
    RLc g j i phi fr regs m /\ rg regs 10 1 /\
    bytes_at rsegs m (fr + 64) (decl_i (Z.of_nat i)) /\ addressable m (fr + 64) 32 /\
    IFS g fr (S j) regs m) c.
(* v1.9 pc 0x82c24 *)
Definition Inv_B82c24 (g : ghost) (c : config) : Prop := exists j i, Inv_B82c24_at g j i c.
(* F36 (0x82c38): inside row_of_block, after the bcmp at 0x82c34; the row latch 0x82c80 goes to the row head 0x82be4
   and on to the F34 cut 0x82bf4 at row i + 1, so the cut carries the row index i like 0x82bf4 / 0x82c24. Prover
   a Theorem Labs lane's conjuncts of Inv_B82bd4_loc_at (in a Seg/F35.v not in this delivery; written on a working branch 44ac51d3f4) after the earlier official body: RLc, the compare
   result in a0 (zero exactly when the block equals row i's declaration; F36's `beqz a0` at 0x82c54), and row i's
   declaration in the slot [fr + 64, fr + 96) with the slot addressable. *)
(* v1.9 pc 0x82c38 *)
Definition Inv_B82c38_at (g : ghost) (j i : nat) (c : config) : Prop :=
  FCUTP g 0x82c38 j (fun phi fr regs m => LK g fr j regs m /\ (i <= 10)%nat /\
    spill regs m 272 (t_k (g_in g) j) /\ True (* v1.9: [A+248] not read after 0x8246c *) /\
    RLc g j i phi fr regs m /\
    (getr regs 10 = Z_to_bv 64 0 <-> t_blk (g_in g) j = decl_i (Z.of_nat i)) /\
    bytes_at rsegs m (fr + 64) (decl_i (Z.of_nat i)) /\ addressable m (fr + 64) 32 /\
    IFS g fr (S j) regs m) c.
(* v1.9 pc 0x82c38 *)
Definition Inv_B82c38 (g : ghost) (c : config) : Prop := exists j i, Inv_B82c38_at g j i c.
(* t_want j = t_want_m j for every input and turn, so no cut has to carry it from an earlier point: the
   catalogue_match result want CAT len g (reac_box_catalogue_match) and the row_of_block result agree. want's gate
   (cp_hdr, bytes 16 / 17 = 0xcd / 0xea, kind 9) is t_rowsel, since kind 9 needs cp_hdr (ctrlparse gives kind 0
   otherwise); both take the block bytes g[18 .. 50); and image B's 11 catalogue declarations decl_i i (the rows
   at CAT + 296 i, frame_RELRO bytes) are RcMatch.DECLS. *)
Lemma decl_i_DECLS : forall i, (i < 11)%nat -> decl_i (Z.of_nat i) = nth i RcMatch.DECLS [].
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  assert (Hinj : forall l1 l2 : list byte, map bv_unsigned l1 = map bv_unsigned l2 -> l1 = l2).
  { induction l1 as [|x l1 IH]; intros [|y l2] H; cbn in H; try discriminate; [reflexivity|].
    injection H as Hxy Hl. f_equal; [apply bv_eq; exact Hxy | exact (IH l2 Hl)]. }
  intros i Hi. apply Hinj.
  do 11 (destruct i as [|i]; [vm_compute; reflexivity|]). lia.
Qed.

Lemma rob_cm_find : forall blk fuel i, (i + fuel = 11)%nat ->
  rob blk i fuel =
  match RcMatch.cm_find blk (skipn i RcMatch.DECLS) with
  | Some k => CAT + 296 * Z.of_nat (i + k) | None => 0 end.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros blk fuel. induction fuel as [|f IH]; intros i Hi.
  - replace i with 11%nat by lia. reflexivity.
  - assert (Hs : skipn i RcMatch.DECLS = nth i RcMatch.DECLS [] :: skipn (S i) RcMatch.DECLS).
    { assert (Hi' : (i < 11)%nat) by lia. clear IH Hi.
      do 11 (destruct i as [|i]; [reflexivity|]). lia. }
    cbn [rob]. rewrite Hs. cbn [RcMatch.cm_find].
    rewrite <- (decl_i_DECLS i) by lia.
    destruct (decide (decl_i (Z.of_nat i) = blk)) as [Heq|Hne].
    + rewrite !bool_decide_true by (first [exact Heq | symmetry; exact Heq]).
      unfold CAT_ROW. rewrite Nat.add_0_r. reflexivity.
    + rewrite !bool_decide_false by (first [exact Hne | intros Hq; apply Hne; symmetry; exact Hq]).
      rewrite (IH (S i)) by lia.
      destruct (RcMatch.cm_find blk (skipn (S i) RcMatch.DECLS)); cbn [option_map]; [lia | reflexivity].
Qed.

Lemma t_want_eq : forall inp j, t_want inp j = t_want_m inp j.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros inp j. unfold t_want, t_want_m, RcMatch.want, RcMatch.cm_gate, t_rowsel, t_k, row_of_block.
  destruct (RcParse.cp_hdr (t_len inp j) (t_g inp j)) eqn:Hh;
    pose proof Hh as Hh'; unfold RcParse.cp_hdr in Hh'; unfold RcParse.ctrlparse; rewrite Hh; cbn [fst];
    rewrite Hh'; cbn [andb].
  - destruct (RcParse.cp_kind (t_g inp j) =? 9); destruct (RcParse.cp_v (t_g inp j) 16 =? 0xcd);
      destruct (RcParse.cp_v (t_g inp j) 17 =? 0xea); cbn [andb]; try reflexivity.
    rewrite (rob_cm_find _ 11 0) by lia. cbn [skipn Nat.add].
    unfold RcMatch.cm_blk, t_blk, RcFrag.bsl. reflexivity.
  - reflexivity.
Qed.

(* Adopt 10 (prover a Theorem Labs lane's third R14X fact, lib/B/Prog/Seg/R14.v on a working branch b086914ea7): the
   catalogue match of turn 0 finds the mode row, for every input. It is the exit Inv_B819a8_at's a0 = mrow after
   R14's reac_box_catalogue_match call (post a0 = want CM_T len fb, CM_T = CAT). Every value in it is a function of
   OUR and i* < 11, so it is computed over the 11 rows with OUR's 6 bytes left as variables (a Theorem Labs lane's
   RtmB.rb_rtm_want, a working branch 35bb4f952f). A lemma, not a conjunct of Inv_B818a8_at. *)
Lemma rt_want0 : forall inp, RcMatch.want CAT (rt_n inp 0) (rt_g inp 0) = mrow inp.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros inp. unfold rt_g, rt_F, rt_X, rt_n, rt_E, rt_uw, rt_nb, rt_mb, mrow.
  pose proof (OUR_length inp) as HL.
  assert (Hi : 0 <= istar inp < 11) by (unfold istar, CAT_N; apply Z.mod_pos_bound; lia).
  revert HL Hi. generalize (OUR inp) (istar inp). intros our i HL Hi.
  destruct our as [|x0 [|x1 [|x2 [|x3 [|x4 [|x5 [|? ?]]]]]]]; try discriminate HL. clear HL.
  assert (E : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9 \/ i = 10)
    by lia.
  clear Hi.
  destruct E as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]; vm_compute; reflexivity.
Qed.

(* rt_want0 in R14X's own form (b = 0 at Inv_B818a8_at). *)
Lemma rnb_want0 : forall g b, b = 0%nat ->
  RcMatch.want CAT (rnb g b) (rt_g (g_in g) (Z.of_nat b)) = mrow (g_in g).
Proof. intros g b ->. exact (rt_want0 (g_in g)). Qed.

(* F37 entry (patched 0x82c3c, the return point of the reac_box_catalogue_match call 0x82c9c): prover a Theorem Labs lane's entry text
   Inv_B82c3c_loc2_at (lib/B/Prog/Seg/F37.v (a version not in this delivery; from a working branch 592d7f08a9), seg_F37 Qed) after the earlier
   official body: F35's conjuncts (the catalogue result a0 = want CAT len (t_g j) that F37's `bne a0,s7` at
   0x82ca4 compares with s7 = t_want_m j, the matched row's address or 0; Phi = s2, len = s4, the spills
   [A + 152] = fr + 64 and [A + 160] = fr + 32, the Phi bytes, the frame), the bne operands equal
   (t_want j = t_want_m j, which t_want_eq proves for every input), and what F37 hands to F38's entry: the
   cursor spills [A + 224] / [A + 232] (FTURN, via FCUTP), [A + 272] = k and IFS (S j) (not [A + 288] = sum_ok, the patched image's: v1.9.0's sum flag is s9, FM).
   Not carried: a Theorem Labs lane's AC.aspZ regs <= APPMEM_END (FRA: sp <= A <= S < APPMEM_END) and a Theorem Labs lane's f1_IN g m (the loop
   head gets it from FRA by fra_f1_in, with 0 < n from its LI by li_n_pos; F38's entry does not carry it).
   Adopt 10 (prover a Theorem Labs lane): s6 = 1 (fr + 176 in the patched image) on every path to the call 0x82c9c - 0x82c84 (Inv_B82c84_at), 0x82c90
   (FTK; 0x82b60 / 0x82b8c / 0x82bb4 write no s6), 0x82c88 via patched 0x82bec `ld s6,168(s1)`; the callee keeps s6 - and
   F37 / F38 write no s6 in patched 0x82c3c-0x82d24, so F38's entry carries it to the loop head. *)
(* v1.9 pc 0x82ca0 *)
Definition Inv_B82ca0_at (g : ghost) (j : nat) (c : config) : Prop :=
  FCUTP g 0x82ca0 j (fun phi fr regs m => LK g fr j regs m /\
    spill regs m 272 (t_k (g_in g) j) /\ True (* v1.9: [A+248] not read after 0x8246c *) /\
    rg regs 10 (t_want (g_in g) j) /\ rg regs 23 (t_want_m (g_in g) j) /\
    rg regs 18 phi /\ rg regs 20 (t_len (g_in g) j) /\ spill regs m 152 (fr + 64) /\
    spill regs m 160 (fr + 32) /\ bytes_at rsegs m phi (t_phi (g_in g) j) /\
    (Z.of_nat (length (t_phi (g_in g) j)) <= flen g j) /\
    stk rsegs m fr (fr + FRAME_BYTES) /\
    t_want (g_in g) j = t_want_m (g_in g) j /\
    IFS g fr (S j) regs m /\ rg regs 22 1) c.
(* v1.9 pc 0x82ca0 *)
Definition Inv_B82ca0 (g : ghost) (c : config) : Prop := exists j, Inv_B82ca0_at g j c.
(* F38 entry (0x82d1c, after the free of F37), with prover a Theorem Labs lane's conjuncts of Inv_B82cb8_loc_at (seg_F38,
   a working branch 359093db9c): s5 = j (0x82ca0 `ld s5,240(s1)`, read by 0x82d1c `addiw a3,s5,1`; the patched image had s9 = j, patched 0x82c3c `ld s9,232(s1)`, read by `addiw a3,s9,1`); s7 = p + body_j +
   len_j and s9 = left_j - h_j - len_j (F37's 0x82ca8-0x82cb4, the cursor of turn j + 1); IFS g fr (S j), the frame
   records and first-frag spills of turn j + 1, which the loop-head cut asks for and the latch hands on. *)
(* v1.9 pc 0x82d1c *)
Definition Inv_B82d1c_at (g : ghost) (j : nat) (c : config) : Prop :=
  CUTST g 0x82d1c [] (fun fr regs m => g_n g < 2 ^ 26 /\ LK g fr j regs m /\
    spill regs m 272 (t_k (g_in g) j) /\ True (* v1.9: [A+248] not read after 0x8246c *) /\
    spill regs m 224 (g_p g + t_body (g_in g) j) /\
    rg regs 21 (Z.of_nat j) /\
    rg regs 23 (g_p g + t_body (g_in g) j + t_len (g_in g) j) /\
    rg regs 25 (t_left (g_in g) j - t_h (g_in g) j - t_len (g_in g) j) /\
    IFS g fr (S j) regs m /\ rg regs 22 1) c.
(* v1.9 pc 0x82d1c *)
Definition Inv_B82d1c (g : ghost) (c : config) : Prop := exists j, Inv_B82d1c_at g j c.

(* ---- X1's entry facts (adopt 8; prover a Theorem Labs lane's gap X1G at 0x82eac, lib/B/Prog/Seg/X12.v on a working branch
   408e729ce0, image A's push-7 text Inv_A82b04, pre-v1.9 0x82a58). The edges into 0x82eac: F38's two exits from Inv_B82d1c_at g j
   (0x82d28 when j = 255; 0x81ec4 / 0x81ec8 when left_(j+1) = 0; a Theorem Labs lane's seg_F38, a working branch 359093db9c)
   and P12's run from Inv_B81e08 when left_0 = n - c0 = 0 (0x81e08 .. 0x81ec4 / 0x81ec8). Inv_B81ec4_at never
   takes 0x81ec8: LI has 1 <= left_j, so `bnez s8` is taken. F38's runs write no memory; P12's run writes the
   spills at A + 72, 80, ..., 136, A + 152 and A + 256 and the shadow bytes S(fr) + 360 .. 375, none of the cells
   of the three facts. The identity bytes come from the record the cuts carry, not from a carried byte list: the
   frame loop rewrites [fr + 2688, fr + 2726) (the reac_identity_ingest calls 0x82300 / 0x82460 take a0 = [A+184];
   reac_identity_ingest_c.v reac_identity_ingest_W), so on F38's edges the record is t_ID (S j) with id_ok
   (IFS g fr (S j), IDb) and on P12's edge ID0 (PL0; id_ok_ID0). id_ok gives byte 19 = 0, a 0 among bytes
   3 .. 19 (x1_name_of_ok); t_ID j has 38 bytes (t_ID_length: ID0 has, and the ingest models rp_id / fg_id keep
   the length, RcIdentModel.ING_length). The 17 bytes at fr + 2691 lie in RAD's 38 at fr + 2688
   (x1_addr_of_rad). The spill [A+184] = fr + 2688 is FLI's (LK) and PL0's. x1_entry_of_lk / x1_entry_of_pl0
   give the three new conjuncts of Inv_B82eac from the two entry bodies. *)
Lemma rp_id_length : forall idb len gb, length idb = RcIdentModel.ID_SIZE ->
  length (rp_id idb len gb) = RcIdentModel.ID_SIZE.
Proof.
  intros idb len gb H. unfold rp_id.
  match goal with |- context [if ?c then _ else _] => destruct c end; [apply RcIdentModel.ING_length|]; exact H.
Qed.

Lemma fg_id_length : forall idb len st gb, length idb = RcIdentModel.ID_SIZE ->
  length (fg_id idb len st gb) = RcIdentModel.ID_SIZE.
Proof.
  intros idb len st gb H. unfold fg_id.
  match goal with |- context [if ?c then _ else _] => destruct c end; [apply RcIdentModel.ING_length|]; exact H.
Qed.

Lemma t_ID_length : forall inp j, length (t_ID inp j) = RcIdentModel.ID_SIZE.
Proof.
  intros inp j. unfold t_ID. induction j as [|j IH]; cbn [fst_at].
  - unfold fs0. cbn [fs_id]. unfold RcIdentModel.ID0. apply repeat_length.
  - unfold turn. cbv zeta.
    match goal with |- context [if ?c then _ else _] => destruct c end; cbn [fs_id];
      apply fg_id_length, rp_id_length, IH.
Qed.

Lemma nthb_ID0 : forall i, RcIdentModel.nthb RcIdentModel.ID0 i = RcIdentModel.zb 0.
Proof. intros i. unfold RcIdentModel.nthb, RcIdentModel.ID0. apply nth_repeat. Qed.

Lemma id_ok_ID0 : RcIdentModel.id_ok RcIdentModel.ID0.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  assert (Hz : RcIdentModel.bz (RcIdentModel.zb 0) = 0) by reflexivity.
  unfold RcIdentModel.id_ok, RcIdentModel.has_fw, RcIdentModel.has_model_name, RcIdentModel.has_reac_version,
    RcIdentModel.fw_milli, RcIdentModel.major, RcIdentModel.minor, RcIdentModel.patch, RcIdentModel.be16.
  rewrite !nthb_ID0, !Hz. repeat split; intros; rewrite ?nthb_ID0, ?Hz; lia.
Qed.

(* An id_ok record of 38 bytes: its first 21 bytes, with a 0 among bytes 3 .. 19 (byte 19). *)
Lemma x1_name_of_ok : forall m a idb, bytes_at rsegs m a idb -> length idb = RcIdentModel.ID_SIZE ->
  RcIdentModel.id_ok idb ->
  exists nm, bytes_at rsegs m a nm /\ length nm = 21%nat /\ SF.find_byte 0 (firstn 17 (skipn 3 nm)) <> None.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros m a idb H HL HOK. exists (firstn 21 idb). split; [|split].
  - rewrite <- (firstn_skipn 21 idb) in H. apply bytes_at_app in H. exact (proj1 H).
  - rewrite length_firstn, HL. reflexivity.
  - destruct HOK as (_ & _ & _ & H19 & _). intro HN.
    assert (Hn : nth_error (firstn 17 (skipn 3 (firstn 21 idb))) 16 = Some (RcIdentModel.nthb idb 19)).
    { rewrite nth_error_firstn, nth_error_skipn, nth_error_firstn.
      change (16 <? 17)%nat with true. change (3 + 16 <? 21)%nat with true. change (3 + 16)%nat with 19%nat.
      cbv beta iota. unfold RcIdentModel.nthb. apply nth_error_nth'. rewrite HL.
      unfold RcIdentModel.ID_SIZE. lia. }
    exact (SF.find_byte_None _ _ HN _ _ Hn H19).
Qed.

Lemma x1_addr_of_rad : forall fr m, RAD fr m -> addressable m (fr + 2691) 17.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros fr m (H & _). replace (fr + 2691) with (fr + 2688 + 3) by lia.
  apply (addressable_sub m (fr + 2688) 38 3 17 H); lia.
Qed.

(* F38's edges: Inv_B82d1c_at's LK and IFS g fr (S j) (its IDj g fr (S j)). *)
Lemma x1_entry_of_lk : forall g fr j k regs m, LK g fr j regs m -> IDj g fr k m ->
  spill regs m 176 (fr + 2688) /\
  (exists nm, bytes_at rsegs m (fr + 2688) nm /\ length nm = 21%nat /\
     SF.find_byte 0 (firstn 17 (skipn 3 nm)) <> None) /\
  addressable m (fr + 2691) 17.
Proof.
  intros g fr j k regs m (_ & _ & _ & HF) (HB & HOK).
  destruct HF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H184 & HF).
  destruct HF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HRAD & _).
  split; [exact H184|]. split.
  - exact (x1_name_of_ok m (fr + 2688) _ HB (t_ID_length (g_in g) k) HOK).
  - exact (x1_addr_of_rad fr m HRAD).
Qed.

(* P12's edge: Inv_B81e08's PL0. *)
Lemma x1_entry_of_pl0 : forall g fr regs m, PL0 g fr regs m ->
  spill regs m 176 (fr + 2688) /\
  (exists nm, bytes_at rsegs m (fr + 2688) nm /\ length nm = 21%nat /\
     SF.find_byte 0 (firstn 17 (skipn 3 nm)) <> None) /\
  addressable m (fr + 2691) 17.
Proof.
  intros g fr regs m (_ & HB & _ & HRAD & H184 & _).
  split; [exact H184|]. split.
  - exact (x1_name_of_ok m (fr + 2688) RcIdentModel.ID0 HB
             ltac:(unfold RcIdentModel.ID0; apply repeat_length) id_ok_ID0).
  - exact (x1_addr_of_rad fr m HRAD).
Qed.

(* ---- Epilogue, release, abort (X1, X2, Jrel, Y). *)
(* X1 entry (0x82eac) and X2 entry (0x82ecc), adopt 8: image A's push-7 texts (Inv_A82b04 / Inv_A82b20, v1.8 Inv_A82a58 / Inv_A82a74) in image
   B's spill, = prover a Theorem Labs lane's X1F / X2G (Seg/X12.v 408e729ce0). X1 reads the identity record pointer spill
   [A + 176] = fr + 2688 (0x82eac / 0x82eb8 `ld a0,176(s1)`), the 21 identity bytes there with a 0 in bytes
   3 .. 19 (0x82eb0 reads byte 20; the memchr wrapper's 17-byte search from fr + 2691 at 0x82ec8 finds the 0) and
   those 17 bytes addressable (the wrapper's check of the bytes it read); producers x1_entry_of_lk (F38) and
   x1_entry_of_pl0 (P12). X2 reads a0 <> 0 (0x82ecc `beqz a0,0x82fa4`, the abort pair, not taken); its producer
   is X1's memchr call 0x82ec8 (a0 = fr + 2691 + i), the only edge into 0x82ecc. *)
(* v1.9 pc 0x82eac *)
Definition Inv_B82eac (g : ghost) (c : config) : Prop :=
  CUTST g 0x82eac [] (fun fr regs m =>
    g_n g < 2 ^ 26 /\ OURb g fr m /\
    spill regs m 176 (fr + 2688) /\
    (exists nm, bytes_at rsegs m (fr + 2688) nm /\ length nm = 21%nat /\
       SF.find_byte 0 (firstn 17 (skipn 3 nm)) <> None) /\
    addressable m (fr + 2691) 17) c.
(* v1.9 pc 0x82ecc *)
Definition Inv_B82ecc (g : ghost) (c : config) : Prop :=
  CUTST g 0x82ecc [] (fun fr regs m =>
    g_n g < 2 ^ 26 /\ OURb g fr m /\ (exists q, a0v regs q /\ 0 < q < 2 ^ 64)) c.
(* Jrel (release join, 0x82f2c): FRA, H = the entry heap (HB = []); reached from X2 (normal return) and from A4
   (n >= 2^26, slot_early, 0x81450 j 0x82f2c). The release writes the sink head to fr then beqz s8 (0x82f38): the side
   arm frees the FS frame (jal frame_release_6, Y1 0x82f48), the real arm clears the frame shadow (jal meta_fill_00,
   Y2 0x82f58); both reach the post-release epilogue (0x82f5c, no FRA). Arms told apart by FRA's frame-location
   disjunction. *)
(* Both edges into 0x82f2c reach it with the selector in register 24 and the frame base in register 23: the early
   edge 0x81450 keeps the 0x81090/0x81098 selector and the 0x8109c/0x810ac frame base, the normal path reloads
   them at 0x82f24 (`ld s8,48(s1)`) and patched 0x82ec4 (`ld s7,56(s1)`). The join reads register 23 at 0x82f34
   (`sd a0,0(s9)`), so the cut pins it; it pins no spill, since the early edge wrote neither [A + 64] nor
   [A + 56]. *)
(* v1.9 pc 0x82f2c *)
Definition Inv_Jrel (g : ghost) (c : config) : Prop :=
  CUTST0 g 0x82f2c [] (fun fr sel regs _ => rg regs 24 sel /\ rg regs 25 fr) c.
(* Y1 (side release call, 0x82f48): a0 = s8 = fr and a1 = 3040 for jal frame_release_6 (the FS frame is freed;
   asan_stack_free_c.v reads the size in a1, 0x82f3c-0x82f40 lui/addiw give 0xbe0 = 3040). Past the header store
   at 0x82f34, so CUTSTR: the frame header word is 0x45e0360e, not 0x41b58ab3. *)
(* v1.9 pc 0x82f48 *)
Definition Inv_B82f48 (g : ghost) (c : config) : Prop :=
  CUTSTR g 0x82f48 [] (fun fr sel regs _ => sel = fr /\ a0v regs fr /\ rg regs 11 FRAME_BYTES) c.
(* Y2 (real release call, 0x82f58): the selector is 0, a0 = s3 = S(fr) and a1 = 380 (0x82f50 li a1,392) for jal
   meta_fill_00; also past the header store. *)
(* v1.9 pc 0x82f58 *)
Definition Inv_B82f58 (g : ghost) (c : config) : Prop :=
  CUTSTR g 0x82f58 [] (fun fr sel regs _ => sel = 0 /\ a0v regs (Sfr fr) /\ rg regs 11 FRAME_SHADOW) c.
(* Y3 (0x82f5c): the post-release epilogue head, reached from Y1 (0x82f4c `j 0x82f5c`) and from Y2's return. No
   FRA: the frame is released (side arm) or its shadow cleared (real arm). It carries what the 13 reloads
   0x82f64-0x82f94 and the slot post need: s0 = S (0x82f60 `addi sp,s0,-448` restores the entry sp), the saved
   caller registers at [S - 104, S), gp and tp still the entry ones (Post's a_regs_kept), the runtime and heap
   invariants, errno writable, the slot window writable and addressable again (alib_post:97; Y1 released the
   frame, Y2 cleared its shadow), and ENT, out of which ent_post (Seg/Tac_slot.v) builds every clause of the post
   that compares the return state with the entry state. a0 is NOT 0 here: 0x82f5c `li a0,0` is the first
   instruction of this segment, so the cut before it holds the callee's result (push 5c; push 5 had a0 = 0). *)
(* v1.9 pc 0x82f5c *)
Definition Inv_B82f5c (g : ghost) (c : config) : Prop :=
  exists regs mem md,
    c = mkCfg (mkst regs (Z_to_bv 64 0x82f5c) mem (seg_rom segs)) md /\
    AsanRTInv.RT (g_S g - 448) mem md /\ AC.aa_AH AC.ASYMS AsanRTInv.RT API (g_H g) mem md /\
    ro_agree rsegs mem /\ sink_none B mem md /\ m_halted md = None /\
    rg regs 8 (g_S g) /\ getr regs 3 = getr (g_regs g) 3 /\ getr regs 4 = getr (g_regs g) 4 /\
    bytes_at rsegs mem (g_S g - 104) (saved_bytes g) /\
    (forall a, AC.a_errno AC.ASYMS <= a < AC.a_errno AC.ASYMS + 4 -> writable_at rsegs mem a) /\
    (forall a, g_S g - AF.SLOT_STACK <= a < g_S g -> writable_at rsegs mem a /\ addressable mem a 1) /\
    ENT g [] mem md.

(* H(X) of plan section 5, for plain cuts and for cuts carrying one or two indices. *)
Definition Hcut (X : ghost -> config -> Prop) : Prop := forall g c, X g c -> SR segs c (Post g).
Definition Hat {I : Type} (X : ghost -> I -> config -> Prop) (i : I) : Prop :=
  forall g c, X g i c -> SR segs c (Post g).
Definition Hat2 {I J : Type} (X : ghost -> I -> J -> config -> Prop) (i : I) (k : J) : Prop :=
  forall g c, X g i k c -> SR segs c (Post g).

(* The slot obligation for this function: G = frame_G = []; GI is the kept-block bound the obligation's TB_bound
   side asks for (FrameAPI TBMAX = 2, TBBYTES = 2^29). *)
Definition slot_goal : Prop :=
  forall j, (j < 4)%nat ->
    @AF.alib_contract fx LS B AsanRTInv.RT API SH SK AF.frame_G AF.frame_RELRO
      (fun _ T _ => (length T <= AF.TBMAX)%nat /\ forall t k, In (t, k) T -> 0 < k <= AF.TBBYTES) j
      AF.ENTRY ra empty AF.SLOT_STACK.

End Slot.

(* Cut invariants of fuzz_ctrl LLVMFuzzerTestOneInput, asan build of libreac v1.9.0, entry function
   [0x80edc, 0x82d58) (slot-plan-asan.md section 3). The image-A twin of lib/U/Prog/SlotInv.v: frame_facts (the
   non-obligation conjuncts of FrameAPI.frame_asan), the ghost values fixed at ENTRY, the frame-and-shadow invariant
   FRA (the 3136-byte side-stack frame, s3 = S(fr), the 392 shadow bytes of FP.4), the per-cut invariants Inv_A<addr>
   of plan section 3, Hcut/Hat/Hat2, and the slot goal. *)
(* DRAFT v1.9 (base pending). The Definitions are re-stated on the v1.9.0 image
   (internal path, sha256 78efaeda1de5...) from the measured table of record
   v190-segment-table.md (a working note, not in this delivery) (v190map/out/asan.json): every pc, cut name, frame constant, frame
   offset and spill slot in the Definition text is the v1.9 one (cut renames: v190-cutnames-A.tsv (a working note, not in this delivery);
   other-function / data addresses from v190-symreloc-map/asan.tsv (a working note, not in this delivery) and the v1.9 .symtab).
   The COMMENTS still cite the v1.8 image (pcs, slots, frame offsets and instruction text of
   (internal path)): map a comment pc through the table. The first-fragment state moved from spills
   into the new local first.sroa.7 (fr + 2880, 35 bytes); FSb is restated on the shared v1.9 fstate
   (v190-model-B.md section 1 (a working note, not in this delivery), in SlotModel.v) and on image A's measured layout. After round 2
   no conjunct is left stopped: every one is either re-stated or kept with its evidence named in its comment. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import Mem Frame Cells Step.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcModel RcRec RcParse RcReply RcIdentModel RcFrag RcLeaf
  RcPorts RcDecl RcClassify RcKind.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import RcAsanFP.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require reac_ctrl_parse_c asan_stack_malloc_c
  asan_memset_c reac_ctrl_identity_reply_c.
(* By full path (lib/Prog and lib/Spec have files of the same names): the bcmp wrapper's scratch size and the
   memcmp model, which the F17-F19 cuts name. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require bcmp_wrap_c memcmp_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Spec Require StrFun.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require reac_box_catalogue_c reac_ctrl_kind_name_c
  reac_ctrl_identity_fragment_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel.
From OSSVerify.libreac.fuzz_ctrl Require Statements.
(* Generation N.1's class accounting (lib/A/ClassConsDef.v a_class_bytes) and the allocator's class table
   (lib/AZ/Spec/AsanCtrl.v K_NUM_CLASSES, size_of_class), for ENT's per-class conjunct. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require ClassConsDef.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.AZ.Spec Require AsanCtrl.
Import ListNotations.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.FrameAPI.
Module SMC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.asan_stack_malloc_c.
Module BWA := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.bcmp_wrap_c.
Module SFA := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Spec.StrFun.
Module CATA := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_box_catalogue_c.
Module KNA := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_ctrl_kind_name_c.
Module FGA := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_ctrl_identity_fragment_c.
Module MCA := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.memcmp_c.

(* The ASan frame of LLVMFuzzerTestOneInput (v1.9.0): FRAME_BYTES bytes from fr, FRAME_SHADOW shadow bytes from
   S(fr). 0x80f48 / 0x80f4c `lui a0,1; addiw a0,a0,-960` and 0x82b90 / 0x82b94 give 4096 - 960 = 3136 (the
   __asan_stack_malloc_6 request and the frame_release_6 size), 0x82ba4 `li a1,392` the meta_fill_00 length;
   the frame description at [fr + 8] has 30 variables, the last `blk` at fr + 3056 (32 bytes). Every frame-size
   occurrence below is written through these names; FRAME_BYTES_val / FRAME_SHADOW_val give lia the numerals. *)
Definition FRAME_BYTES : Z := 3136.
Definition FRAME_SHADOW : Z := FRAME_BYTES / 8.
Lemma FRAME_BYTES_val : FRAME_BYTES = 3136.
Proof. reflexivity. Qed.
Lemma FRAME_SHADOW_val : FRAME_SHADOW = 392.
Proof. reflexivity. Qed.

(* frame_asan (A/FrameAPI.v:147) without its last conjunct (the slot obligation yielding asan_halts); the conjunct
   itself is slot_obligation. frame batch 2 (a Theorem Labs lane 48004cf7bfc) added the sink-env bound (FrameAPI.v:156, after
   `0 < empty < 2 ^ 62`); frame_facts carries it LAST, so the v1.8 positions of frame_facts are kept. Twin of
   lib/B/Prog/SlotInv.v (a working branch 2f906755bcb): same conjunct text, same position. *)
Definition frame_facts (B : malloc_syms) (APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT)
    (LS : lib_shape) (SH : sink_head) (SK : sink_syms) (ra empty : Z) : Prop :=
  ms_segs B = rsegs /\ ra mod 2 = 0 /\
  ms_tp B = AC.as_tp AC.ASYMS /\ ms_errno_off B = -164 /\
  @sk_ofl_head SH = 0x5fbf08 /\ @sk_ofl_lock SK = 0x5fbf00 /\ @sk_threaded SK = 0x5fbaa0 + 1 /\
  empty = 0x5daee0 /\ 0 < empty < 2 ^ 62 /\
  (forall a, in_globals AF.frame_G a -> AC.a_in_img a) /\
  (forall a, in_globals AF.frame_RELRO a -> AC.a_in_img a) /\
  (forall rc H mem md a, AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) H mem md a ->
     ~ in_globals AF.frame_G a /\ ~ in_globals AF.frame_RELRO a) /\
  (forall pl fs K, @LIBK LS pl fs K = K (LL 0 fs [])) /\
  (* frame batch 2 (FrameAPI.v, a Theorem Labs lane's generated set): every sink env cell lies inside the image. Appended last,
     so every positional destruct of frame_facts keeps its components. *)
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
    Statements.asan_halts.

Lemma frame_asan_split : AF.frame_asan -> exists B APIf LS SH SK ra empty,
  frame_facts B APIf LS SH SK ra empty /\ slot_obligation B APIf LS SH SK ra empty.
(* By name: frame_asan is a Theorem Labs lane's generated bundle, so the proof names every conjunct it has and rebuilds
   frame_facts from those names (the v1.8 `tauto` searched the whole bundle and gave up on batch 2's size). The
   rebuild is the twin of lib/B/Prog/SlotInv.v's (a working branch 2f906755bcb): Henv goes last. *)
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
(* Push 7 (a Theorem Labs lane): g_n unfolded to the input's length, for the frame-loop segments that keep f1_IN's input
   bytes across their write windows. *)
Lemma g_n_len : forall g, g_n g = Z.of_nat (length (g_in g)).
Proof. reflexivity. Qed.

(* The slot's OWN share of class c: one slot of class c (the harness holds at most one block of its own at a
   time: fuzz_dup at fuzz_ctrl.c:524 freed at :613 before fuzz_dup at :704 freed at :706), 0 at the classes no
   primary request reaches. The body of a Theorem Labs lane's CtrlClassLive.BC_ctrl (a working branch
   61aba11640, CtrlClassLive.v (not in this delivery)), defined here at top level because CtrlClassLive.v (not in this delivery) Requires this file, so
   CtrlClassLive.BC_ctrl c = BC_ctrl c is reflexivity. Top level, not a section variable: no lemma's arity moves. *)
Definition BC_ctrl (c : Z) : Z :=
  if (c =? 0) || (c =? 5) || (c =? 31) then 0 else AsanCtrl.size_of_class c.

(* ==== The generated allocator laws (lib/A/Contract.v) this bundle takes apart, each destructed ONCE here, by
   statement (a Theorem Labs lane 15:18Z / 15:32Z: a generated conjunction is never destructed by position at a use; one local
   lemma per law). Each lemma matches its record's fields to the law's conjuncts by `eassumption` (after decompose),
   so a conjunct a later generation adds or moves changes neither the lemma nor its users. SlotInv.v, Seg/Tac_slot.v
   and Seg/Tac_fsfree.v read the laws only through these. Image A's copy of image B's section
   (lib/B/Prog/SlotInv.v (at head lib/B/Prog/SlotInv.v:118-245; written on a working branch 1d6892010bb)), same names and fields. *)
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

(* The 'not in the FakeStack' part of a live block byte, by name (lwb_byte's last conjunct). *)
Lemma lwb_byte_not_fs : forall H mem md p n, lw_blk H mem md p n ->
  forall a, p <= a < p + n -> ~ AC.a_in_fs AC.ASYMS mem a.
Proof.
  intros H mem md p n B a Ha. destruct B as [_ _ _ _ Hb].
  destruct (Hb a Ha) as (_ & _ & _ & _ & Hfs). exact Hfs.
Qed.

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
   record as lw_store). Image B's text (a working branch 23a791566db); A's law has the same shape. *)
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
   every sp of the function is above S - 4096 (A = (S - 416) & -32 >= S - 447, real-arm sp = fr >= S - 3487), so the
   sp-anchored window [sp - FN_STACK, sp) of fra_win lies inside [S - SLOT_STACK, S), and every callee's own stack
   need (largest 2224, the checked memcpy) is below FN_STACK. *)
Definition FN_STACK : Z := AF.SLOT_STACK - 4096.

(* The side-arm FakeStack frame record (push 5b, for frame_release_6 / asan_stack_free_6_contract): the frame is
   slot j of size class 6 of the FakeStack FS (the word at tp), its flag byte is 1 (in use) and the slot's last word
   holds the flag's address, as A1's asan_stack_malloc_6 call leaves them. The fs_* layout is the one the
   stack-allocation contracts read (lib/A/Prog/asan_stack_malloc_c.v; Contract.v's a_fs_* are the same formulas). *)
Definition FSREC (fr : Z) (mem : word -> option byte) : Prop :=
  exists FS j, word_mem rsegs mem (AC.as_tp AC.ASYMS) FS /\ 0 <= FS < 2 ^ 64 /\ 0 <= j < SMC.fs_M 6 /\
    fr = SMC.fs_frame FS 6 j /\ bytes_at rsegs mem (SMC.fs_flag FS 6 j) [Z_to_bv 8 1] /\
    bytes_at rsegs mem (fr + SMC.fs_B 6 - 8) (le8 (Z_to_bv 64 (SMC.fs_flag FS 6 j))).

(* FRA (plan 3.1): the frame-and-shadow invariant carried at every cut from A3 to Y2, on top of the ubsan twin.
   The frame base fr (fr mod 32 = 0) is carried by the spill q64 (A + 304) = fr (s1+304, set 0x80f88, never
   overwritten), NOT by a register: s6 and s5 hold fr / the request result only up to 0x813a8 and are reused as
   the input cursor and the frame-loop index j afterwards (so FRA no longer pins reg 22 / reg 21; the A-region cuts
   add rg regs 22 fr in their own body). s1 = A the spill base, s0 = S, s3 = S(fr), s10 = ASAN_K the shadow
   offset (reg 26, loaded at 0x80f1c, never rewritten before the epilogue reload 0x82b24, so it holds K at
   every FRA cut; every inline shadow check computes `add aX, aX, s10`). The frame bytes are a_store_ok
   (real arm, s5 = 0) or in FS (side arm, s5 = fr) by the frame-location disjunction. Plus
   the frame header, the 380 shadow bytes S(fr)..S(fr)+379 (FP.4, carried abstractly as a 380-byte list), the slot
   window writable, the saved caller registers, the asan runtime RT, the live heap H = hb ++ the entry heap with
   the single-buffer ROOM bound, and the runtime cells ro_agree / sink_none / errno. Also the spill-base bounds
   sp <= A (the frame / side-stack block sits at or below the spill base A = s1) and A + 416 <= S (the 416-byte
   prologue save area [A, A+416) fits below the entry sp S), both read off the prologue 0x80ebc-0x80f64.
   Push 5c adds what the callee preconditions of the segments need at every FRA cut: the slot window outside
   the frame addressable (the entry pre gives the whole window addressable and only the
   frame's shadow is poisoned, so fra_call_pre can hand a callee its own window), and the three ghost facts about
   the ENTRY state's stack top that a_call_pre asks for (S at or below stkhi, stkhi at or below APPMEM_END, the
   bytes of [S, stkhi) present at entry); ENT carries those three to the cut's own state. The fr reload spill
   q64 (A + 24) = fr (stored 0x8132c, reloaded 0x82abc) is in FRA only: FRAS / FRAR drop it, as they drop the
   selector spill, since the early edge 0x812c4 reaches the release join with neither written. *)
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
    A + 416 <= g_S g /\ g_S g - 4096 < sp /\ g_S g < APPMEM_END /\
    q64 mem (A + 304) fr /\ q64 mem (A + 24) s5 /\ q64 mem (A + 16) fr /\
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
    (* no mem_inv here (5d, a Theorem Labs lane): the entry pre gives ro_agree only, and a callee reaches its own
       mem_inv premise through MemNorm.evt_normalize from ro_agree (slot contract S1.7). *)
    (forall a, g_S g - AF.SLOT_STACK <= a < g_S g -> ~ (fr <= a < fr + FRAME_BYTES) -> addressable mem a 1) /\
    g_S g <= AC.aa_stkhi AC.ASYMS AsanRTInv.RT API (g_mem g) (g_md g) /\
    AC.aa_stkhi AC.ASYMS AsanRTInv.RT API (g_mem g) (g_md g) <= APPMEM_END /\
    (forall a, g_S g <= a < AC.aa_stkhi AC.ASYMS AsanRTInv.RT API (g_mem g) (g_md g) ->
       exists b, mbyte rsegs (g_mem g) a = Some b) /\
    (* frame batch 2 raised alib_pre's live-bytes bound from 3 to 5 * 2 ^ 30 (FrameAPI.v:65; FrameAPI gives it no
       name, so this is the literal of that line - re-check it at the next generated set). *)
    (length hb <= 1)%nat /\ AC.a_live_bytes (g_H g) <= 5 * 2 ^ 30.

(* ENT (push 5c): what a cut keeps of the ENTRY state. It is exactly the part of the slot post
   (AF.alib_post, lib/A/FrameAPI.v:76-103) that compares the return state with the entry state and that FRA does
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
  (* ghost tp (push 5c, needed by Y3's `getr regs 4 = getr (g_regs g) 4` reload at 0x82b2c): the entry tp word
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
  (* frame batch 2, item 9 (FrameAPI.v alib_post): the SHADOW of every entry block the target does not keep is
     the entry one too. Appended after the v1.8 conjuncts, so every positional destruct of ENT keeps its
     components; it is the twin of post 85 above. The runtime writes a chunk's shadow only when that chunk is
     allocated or freed, and a_laws_not_owned says a live block's byte AND its shadow byte are unowned, so the
     frame clause of every callee post carries it. *)
  (forall q k i, In (q, k) (g_H g) -> ~ In (q, k) (g_T g) -> 0 <= i < k ->
     mbyte rsegs mem (shadow_addr (q + i)) = mbyte rsegs (g_mem g) (shadow_addr (q + i))) /\
  (* Generation N.1's per-class bound, 14th and LAST (a Theorem Labs lane's design 16:0xZ, mirrored by image B): SOME per-class
     bound BE on the ENTRY heap, with room for the slot's own share under the shared budget 2 ^ 22
     (classbound/fuzz_ctrl.tsv (a working note, not in this delivery): Bc = 2 ^ 22, m = 1, SP = size_of_class c). It is existential, so no
     section variable is added and no lemma's arity moves. It names only the ghost, so every transport keeps the
     witness; Seg/Tac_cls.v's sl_malloc_cls / sl_free_cls turn it into the allocator's class premises with
     Bc c = BE c + BC_ctrl c. At entry it is the slot's named premise ENTRY_CLASS (Seg/Tac_slot.v), which the
     driver owes until a Theorem Labs lane puts it in alib_pre. *)
  (exists BE : Z -> Z,
     (forall c, 0 <= c < AsanCtrl.K_NUM_CLASSES -> ClassConsDef.a_class_bytes (g_H g) c <= BE c) /\
     (forall c, 0 <= c < AsanCtrl.K_NUM_CLASSES -> BE c + BC_ctrl c <= 2 ^ 22)).

(* A cut: the config at pc with FRA (the frame base fr is existential, passed to the register/memory predicate P)
   and ENT, the extra live buffer list hb, and P the cut's own register/memory content. *)
Definition CUTST (g : ghost) (pc : Z) (hb : list (Z * Z))
    (P : Z -> bvmap 5 word -> (word -> option byte) -> Prop) (c : config) : Prop :=
  exists regs mem md fr,
    c = mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom segs)) md /\
    FRA g fr hb regs mem md /\ ENT g hb mem md /\ P fr regs mem.

(* FRAH: FRA with the frame selector s5 a parameter instead of an existential, WITHOUT the spill
   q64 mem (A + 32) s5, and with the frame header word hdr a parameter. The selector is stored to [A + 32] only at
   0x812cc (`sd s5,32(s1)`), after the size test 0x812e8-0x81314, so the early edge 0x81314 (`j 0x82b80`) reaches
   the release join with the selector in register 21 alone and with neither [A + 32] nor [A + 24] written; the cuts
   on that edge carry FRAH and name the selector themselves. The header word is 0x41b58ab3 up to the release join
   and 0x45e0360e after the store at 0x82ac8. *)
Definition FRAH (g : ghost) (fr : Z) (hb : list (Z * Z)) (regs : bvmap 5 word) (mem : word -> option byte)
    (md : Model) (s5 hdr : Z) : Prop :=
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
    fr mod 32 = 0 /\ (s5 = 0 \/ s5 = fr) /\ A mod 32 = 0 /\ A <= g_S g /\ sp <= A /\ fr + FRAME_BYTES <= A /\
    A + 416 <= g_S g /\ g_S g - 4096 < sp /\ g_S g < APPMEM_END /\
    q64 mem (A + 304) fr /\
    ((s5 = 0 /\ sp = fr /\
        (forall a, fr <= a < fr + FRAME_BYTES -> AC.aa_stklo AC.ASYMS AsanRTInv.RT API mem md <= a < APPMEM_END)) \/
     (s5 = fr /\
        (forall FS, word_mem rsegs mem (AC.as_tp AC.ASYMS) FS -> 0 <= FS < 2 ^ 64 -> FS + 6328320 <= fr) /\
        (forall a, fr <= a < fr + FRAME_BYTES -> AC.a_in_fs AC.ASYMS mem a) /\ FSREC fr mem)) /\
    q64 mem fr hdr /\ q64 mem (fr + 16) AF.ENTRY /\
    (exists sh, bytes_at rsegs mem (Sfr fr) sh /\ length sh = Z.to_nat FRAME_SHADOW) /\
    stk rsegs mem (g_S g - AF.SLOT_STACK) (g_S g) /\
    bytes_at rsegs mem (g_S g - 104) (saved_bytes g) /\
    (forall a, AC.a_errno AC.ASYMS <= a < AC.a_errno AC.ASYMS + 4 -> writable_at rsegs mem a) /\
    (forall a, in_globals AF.frame_AG a -> addressable mem a 1) /\
    (* no mem_inv (5d): see FRA. *)
    (forall a, g_S g - AF.SLOT_STACK <= a < g_S g -> ~ (fr <= a < fr + FRAME_BYTES) -> addressable mem a 1) /\
    g_S g <= AC.aa_stkhi AC.ASYMS AsanRTInv.RT API (g_mem g) (g_md g) /\
    AC.aa_stkhi AC.ASYMS AsanRTInv.RT API (g_mem g) (g_md g) <= APPMEM_END /\
    (forall a, g_S g <= a < AC.aa_stkhi AC.ASYMS AsanRTInv.RT API (g_mem g) (g_md g) ->
       exists b, mbyte rsegs (g_mem g) a = Some b) /\
    (length hb <= 1)%nat /\ AC.a_live_bytes (g_H g) <= 5 * 2 ^ 30.

(* Before the release's header store: the header word is the one A3 wrote at 0x80f90. *)
Definition FRAS (g : ghost) (fr : Z) (hb : list (Z * Z)) (regs : bvmap 5 word) (mem : word -> option byte)
    (md : Model) (s5 : Z) : Prop := FRAH g fr hb regs mem md s5 0x41b58ab3.
(* After it (0x82b88 `sd a0,0(s6)` with a0 = 0x45e0360e, so Y1 at 0x82b9c and Y2 at 0x82bac). *)
Definition FRAR (g : ghost) (fr : Z) (hb : list (Z * Z)) (regs : bvmap 5 word) (mem : word -> option byte)
    (md : Model) (s5 : Z) : Prop := FRAH g fr hb regs mem md s5 0x45e0360e.

(* The FRAS cut: as CUTST, with the selector passed to the cut's own predicate as well as the frame base. *)
Definition CUTST0 (g : ghost) (pc : Z) (hb : list (Z * Z))
    (P : Z -> Z -> bvmap 5 word -> (word -> option byte) -> Prop) (c : config) : Prop :=
  exists regs mem md fr s5,
    c = mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom segs)) md /\
    FRAS g fr hb regs mem md s5 /\ ENT g hb mem md /\ P fr s5 regs mem.
(* The same cut after the release's header store. *)
Definition CUTSTR (g : ghost) (pc : Z) (hb : list (Z * Z))
    (P : Z -> Z -> bvmap 5 word -> (word -> option byte) -> Prop) (c : config) : Prop :=
  exists regs mem md fr s5,
    c = mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom segs)) md /\
    FRAR g fr hb regs mem md s5 /\ ENT g hb mem md /\ P fr s5 regs mem.

(* Two Z values held by the same register agree modulo 2^64. *)
Lemma rg_eq64 : forall (regs : bvmap 5 word) (r : bv 5) (a b : Z),
  rg regs r a -> rg regs r b -> a mod 2 ^ 64 = b mod 2 ^ 64.
Proof.
  intros regs r a b Ha Hb. unfold rg in Ha, Hb. rewrite Ha in Hb.
  apply (f_equal bv_unsigned) in Hb. rewrite !Z_to_bv_unsigned in Hb.
  unfold bv_wrap in Hb. change (bv_modulus 64) with (2 ^ 64) in Hb. exact Hb.
Qed.

(* and so agree outright when both lie in one 2^64-wide window. (v1.9: the upper bound on a is 2 ^ 64 - 32, what
   FRA_of_FRAS reads off the selector spill [A + 24]; v1.8 had [A + 32] and 2 ^ 64 - 40.) *)
Lemma rg_eq : forall (regs : bvmap 5 word) (r : bv 5) (a b : Z),
  rg regs r a -> rg regs r b -> -32 <= a -> a <= 2 ^ 64 - 32 -> 0 < b -> b <= 2 ^ 64 - 416 -> a = b.
Proof.
  intros regs r a b Ha Hb H1 H2 H3 H4.
  pose proof (rg_eq64 regs r a b Ha Hb) as Hm.
  revert Hm H1 H2 H3 H4. change (2 ^ 64) with 18446744073709551616.
  intros Hm H1 H2 H3 H4. Z.div_mod_to_equations. lia.
Qed.

(* FRA gives FRAS at the selector its existential names, plus the [A + 32] spill of that selector. *)
Lemma FRAS_of_FRA : forall g fr hb regs mem md,
  FRA g fr hb regs mem md ->
  exists s5 A, rg regs 9 A /\ FRAS g fr hb regs mem md s5 /\ q64 mem (A + 24) s5.
Proof.
  intros g fr hb regs mem md H. destruct H as (A & sp & s5 & H).
  exists s5, A. split; [unfold rg; tauto | split; [exists A, sp; tauto | tauto]].
Qed.

(* and conversely: FRAS plus the two spills at [A + 32] (the selector) and [A + 24] (the fr reload read at
   0x82abc) rebuilds FRA. The spill base A is pinned by register 9, so it is the A of FRAS's existential (rg_eq,
   with 0 < A from sp <= A and S - 4096 < sp). *)
Lemma FRA_of_FRAS : forall g fr hb regs mem md s5 A,
  FRAS g fr hb regs mem md s5 -> rg regs 9 A -> q64 mem (A + 24) s5 -> q64 mem (A + 16) fr ->
  FRA g fr hb regs mem md.
Proof.
  intros g fr hb regs mem md s5 A HS Hr9 Hsel Hfr24.
  destruct HS as (A' & sp & HS).
  assert (Hr9' : rg regs 9 A') by tauto.
  assert (Hsp : sp <= A') by tauto.
  assert (HS4 : g_S g - 4096 < sp) by tauto.
  assert (HA416 : A' + 416 <= g_S g) by tauto.
  assert (Hstk : stk rsegs mem (g_S g - AF.SLOT_STACK) (g_S g)) by tauto.
  assert (Hb : 0 <= g_S g - AF.SLOT_STACK /\ g_S g <= 2 ^ 64)
    by (unfold stk in Hstk; split; [apply (proj1 Hstk) | apply (proj1 (proj2 Hstk))]).
  assert (Hsa : 0 <= A + 24 /\ A + 24 + Z.of_nat (length (le8 (Z_to_bv 64 s5))) <= 2 ^ 64)
    by (unfold q64, bytes_at in Hsel; split; [apply (proj1 Hsel) | apply (proj1 (proj2 Hsel))]).
  rewrite length_le8 in Hsa.
  assert (HAeq : A = A').
  { apply (rg_eq regs 9 A A' Hr9 Hr9'); unfold AF.SLOT_STACK in Hb; lia. }
  subst A'. exists A, sp, s5. tauto.
Qed.

(* The sp-anchored window the callee contracts ask for, read off FRA's S-anchored stack facts: every sp of the
   function is above S - 4096 and at most A <= S, so [sp - FN_STACK, sp) is a sub-window of [S - SLOT_STACK, S). *)
Lemma fra_win : forall g fr hb regs mem md,
  FRA g fr hb regs mem md ->
  AC.aa_stklo AC.ASYMS AsanRTInv.RT API mem md <= AC.aspZ regs - FN_STACK /\
  stk rsegs mem (AC.aspZ regs - FN_STACK) (AC.aspZ regs).
Proof.
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

(* The frame's placement, for the callee premises of the call segments: the 3040-byte frame is either entirely 16
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
  pose proof FRAME_BYTES_val as HFBv.
  intros g fr hb regs mem md HFRA.
  destruct HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HFSsz : AC.FS_SIZE = 11571200) by reflexivity.
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  unfold stk in Hwin. destruct Hwin as (Hw0 & Hw1 & Hwv).
  assert (HA64 : 0 <= A < 2 ^ 64) by lia.
  assert (Hplace : forall FS, word_mem rsegs mem (AC.as_tp AC.ASYMS) FS -> 0 <= FS < 2 ^ 64 ->
            FS + AC.FS_SIZE <= AC.aa_stklo AC.ASYMS AsanRTInv.RT API mem md).
  { intros FS Hw HFSr.
    destruct (lw_fs_place API (hb ++ g_H g) mem md FS HAH Hw HFSr) as [_ Hend _ _]. exact Hend. }
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
      pose proof (lw_fs_ok API (hb ++ g_H g) mem md FSa HAH Hwa HFSar) as Hok.
      exact (proj1 (lw_fs_bytes mem FSa Hok a ltac:(lia))). }
Qed.
(* The frame body is byte-backed: on the real arm the frame is a sub-window of FRA's entry-anchored stack window,
   on the side arm every frame byte is a FakeStack byte, which a_fs_ok makes writable and present. (Push 13 group
   B, a Theorem Labs lane's cut-gap5-81bf8.md section 1 (a working note, not in this delivery): so `stk rsegs mem fr (fr + 3040)` need not be a cut conjunct; FLSH
   keeps it for the frame loop, and P12 gets it here.) *)
Lemma fra_stk : forall g fr hb regs mem md,
  FRA g fr hb regs mem md -> stk rsegs mem fr (fr + FRAME_BYTES).
Proof.
  pose proof FRAME_BYTES_val as HFBv.
  intros g fr hb regs mem md HFRA.
  destruct HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  unfold APPMEM_END in HAPP.
  destruct Hwin as (Hw0 & Hw1 & Hwv).
  destruct Hloc as [[H0 [Hspfr Hreal]]|[Hfr0 [HfsbS [Hfs _]]]].
  - split; [lia|]. split; [lia|]. intros a Ha. apply Hwv. lia.
  - destruct (Hfs fr ltac:(lia)) as (FS0 & HFS0r & Hw00 & Hlo0 & Hhi0).
    split; [lia|]. split; [lia|].
    intros a Ha.
    destruct (Hfs a Ha) as (FSa & HFSar & Hwa & Hloa & Hhia).
    pose proof (lw_fs_ok API (hb ++ g_H g) mem md FSa HAH Hwa HFSar) as Hok.
    exact (lw_fs_bytes mem FSa Hok a ltac:(lia)).
Qed.

(* Every frame byte is app memory: on the real arm the frame lies in [stklo, APPMEM_END) and the allocator laws
   put stklo at or above HIGHMEM_BEG; on the side arm it lies in the FakeStack, whose bytes a_laws_fs_place makes
   app memory. (A lemma, not an FRA conjunct: both arms already carry the fact a callee needs.) *)
Lemma fra_app : forall g fr hb regs mem md,
  FRA g fr hb regs mem md -> AC.GT <= fr /\ (forall a, fr <= a < fr + FRAME_BYTES -> app_mem a).
Proof.
  pose proof FRAME_BYTES_val as HFBv.
  intros g fr hb regs mem md HFRA.
  destruct HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
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

(* The fr reload spill at [A + 24] (stored 0x8132c, read at 0x82abc), which FRAS / FRAR drop; A in register 9 is
   in range (A <= S, S - 4096 < sp <= A, and stk puts S - SLOT_STACK at or above 0 and S at or below 2^64). *)
Lemma fra_fr_spill : forall g fr hb regs mem md,
  FRA g fr hb regs mem md -> exists A, rg regs 9 A /\ 0 <= A < 2 ^ 64 /\ q64 mem (A + 16) fr.
Proof.
  intros g fr hb regs mem md H. destruct H as (A & sp & s5 & H). exists A.
  assert (Hr9 : rg regs 9 A) by tauto.
  assert (Hsp : sp <= A) by tauto.
  assert (HAS : A <= g_S g) by tauto.
  assert (HS4 : g_S g - 4096 < sp) by tauto.
  assert (Hstk : stk rsegs mem (g_S g - AF.SLOT_STACK) (g_S g)) by tauto.
  assert (Hsp24 : q64 mem (A + 16) fr) by tauto.
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  unfold stk in Hstk. destruct Hstk as (Hb0 & Hb1 & _).
  split; [exact Hr9 | split; [lia | exact Hsp24]].
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
  intros g fr hb regs mem md K HFRA HENT Hret HK.
  pose proof (fra_win g fr hb regs mem md HFRA) as (Hlo & Hwk).
  pose proof (fra_frame g fr hb regs mem md HFRA) as (Hapart & _ & _ & _).
  pose proof HFRA as HF.
  destruct HF as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  destruct HENT as (Hasp & Htp & HTH & Hfs & Hfz & Hmdl & Hslo & Hshi & Hblk & Himg & Habv & Hshd).
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HFN : FN_STACK = 1044480) by reflexivity.
  pose proof Hwk as Hwk'. unfold stk in Hwk'. destruct Hwk' as (_ & _ & Hwkv).
  pose proof Hwin as Hwin'. unfold stk in Hwin'. destruct Hwin' as (_ & _ & Hwinv).
  assert (Hnb : forall a, AC.aa_stklo AC.ASYMS AsanRTInv.RT API mem md <= a ->
            ~ AC.in_blocks (hb ++ g_H g) a).
  { intros a Ha (p & n & Hin & Hr).
    destruct (lw_blocks API (hb ++ g_H g) mem md p n HAH Hin) as [_ _ Hend _ _]. lia. }
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

(* ENTRY (A1, 0x80ebc): the slot pre at pc ENTRY plus the slot obligation's side premises (plan 3.3). *)
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
(* The declaration slot in the frame (reg 18 at R19): A+192 = fr+2560 (set 0x81360 addi a0,s5,384 with s5=fr+2176;
   spilled sd a0,192(s1); loaded into s2 at 0x81800), the expected declaration bytes for the bcmp at 0x8188c. *)
Definition decl_slot (fr : Z) : Z := fr + 2560.

(* ==== Image-A port of the lib/U/Prog/SlotInv.v bundles (CUR, RT, RB, RS, RF, LK, LI, FC, FT, FV/FB, PORTS, ...)
   under plan-asan 3.2. Each frame variable moves from ubsan sp+N to fr + <FP.4 "fr +" offset>; each data spill to
   A + <offset> (s1-relative, A = reg 9), pinned from aslot/asan_entry_fn.s. Registers re-pinned to the asan
   allocation: input cursor s6 (reg 22), left s9 (reg 25); round trip b s7 (reg 23), n_b s2 (reg 18), Phi_r s8
   (reg 24); frame loop j s5 (reg 21), Phi s7 (reg 23), len s2 (reg 18), body ptr s4 (reg 20), kind k s8 (reg 24),
   blk s9 (reg 25). The ubsan check-false conjuncts M8/OVF/A2/S2/T2 (plan-asan 7) are dropped. Data spills:
   fr A+304 (in FRA); first-frag FS have A+104 / a0 A+112 / a1 A+96 / nb A+88 (opens_record 0x82320-0x82338);
   the record cursor left-h A+224 (0x81d00, read at the latch 0x828a4). The frame-loop flag registers is_8819 /
   sum_ok / [len>=50] / TF and the W00 row index are not re-pinned here (heavily reused asan registers; see report). *)
Definition spill (regs : bvmap 5 word) (m : word -> option byte) (off v : Z) : Prop :=
  exists A, rg regs 9 A /\ q64 m (A + off) v.
Definition CUR (g : ghost) (c : Z) (regs : bvmap 5 word) : Prop :=
  0 <= c <= g_n g /\ rg regs 22 (g_p g + c) /\ rg regs 25 (g_n g - c).
Definition OURb (g : ghost) (fr : Z) (m : word -> option byte) : Prop :=
  bytes_at rsegs m (fr + 2624) (OUR (g_in g)).
(* PRO (push 13 group B, a Theorem Labs lane's cut-gap5-81bf8.md (a working note, not in this delivery)): the frame facts A4's prologue sets and nothing rewrites
   before the frame loop, on every cut from Inv_A81400_at to Inv_A81c84 and inside FLSH. The eight spills are
   A4's 0x812d4 / 0x812ec / 0x812e4 / 0x81324 / 0x8139c / 0x812dc / 0x8131c / 0x812f4; our[]'s 6 bytes are
   addressable from 0x8138c `sb a2,328(s3)` (a2 = 6, and S(fr) + 328 = shadow_addr (fr + 2624)); the input facts
   are ENTRY's alib_pre ones, which A1-A4 thread (Inv_A80f54 .. Inv_A810e4) in the guarded form A4 can give
   (for n = 0 alib_pre gives no block). No instruction of 0x813a8 .. 0x81bf8 stores to [s1 + 40 / 120 / 136 /
   160 / 168 / 176 / 200 / 248], to S(fr) + 328 or to the input block, and no callee of the range writes them
   (a Theorem Labs lane's table of write sets in cut-gap5-81bf8.md section 2 (a working note, not in this delivery)). [A + 144] = fr + 2688 and the 17 bytes at fr + 2691 are official facts
   of their own (push 12A), not PRO members.
   Push 14 group D (FLC, below): PRO also carries A4's [A + 184] = fr + 336, [A + 256] = fr + 256,
   [A + 264] = fr + 304 and [A + 272] = fr + 272 (0x81314 / 0x812fc / 0x8130c / 0x81304), appended last. No
   instruction of 0x813a8 .. 0x828b0 stores to [s1 + 184 / 256 / 264 / 272], so P12 can hand them to FLC at the
   loop head. *)
Definition PRO (g : ghost) (fr : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  spill regs m 40 (fr + 32) /\ spill regs m 120 (fr + 160) /\ spill regs m 136 (fr + 128) /\
  spill regs m 160 (fr + 528) /\ spill regs m 168 (fr + 2624) /\ spill regs m 176 (fr + 64) /\
  spill regs m 208 (fr + 448) /\ spill regs m 248 (fr + 176) /\
  addressable m (fr + 2624) 6 /\
  bytes_at rsegs m (g_p g) (g_in g) /\
  (0 < g_n g -> In (g_p g, g_n g) (g_H g) /\ addressable m (g_p g) (g_n g)) /\
  spill regs m 184 (fr + 336) /\ spill regs m 256 (fr + 256) /\ spill regs m 264 (fr + 304) /\
  spill regs m 272 (fr + 272) /\
  (* v1.9, appended last so that every v1.8 conjunct keeps its position: [A + 32] = fr + 2880 = &first.sroa.7,
     A4's 0x813c8 / 0x813cc, the only store to [s1 + 32] in the function (loads 0x81b6c / 0x81d2c / 0x823cc). *)
  spill regs m 32 (fr + 2880).
(* OUTA: the out[] buffer (1492 bytes at fr + 544) stays addressable through the b loop: it is made addressable
   before the loop (0x814d0 / 0x814ec) and no loop instruction or callee writes its shadow bytes. *)
Definition OUTA (fr : Z) (m : word -> option byte) : Prop := addressable m (fr + 544) 1492.
Definition IDBr (g : ghost) (fr : Z) (idb : list byte) (m : word -> option byte) : Prop :=
  bytes_at rsegs m (fr + 2176) idb.
Definition FGBr (g : ghost) (fr : Z) (st : list byte) (m : word -> option byte) : Prop :=
  bytes_at rsegs m (fr + 2256) st.
Definition IDBe (g : ghost) (fr : Z) (idb : list byte) (m : word -> option byte) : Prop :=
  bytes_at rsegs m (fr + 2688) idb.
Definition FGBe (g : ghost) (fr : Z) (st : list byte) (m : word -> option byte) : Prop :=
  bytes_at rsegs m (fr + 2768) st.

(* Round trip (R6-R21), turn b: s7 = b, s8 = Phi_r, s2 = n_b; CUR g 7; our / id_rt / frag_rt. *)
Definition RB (g : ghost) (fr : Z) (b : nat) (idb fgb : list byte) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  (b <= 6)%nat /\ CUR g 7 regs /\ OURb g fr m /\ rg regs 23 (Z.of_nat b) /\ IDBr g fr idb m /\ FGBr g fr fgb m.
Definition RS (g : ghost) (fr : Z) (b : nat) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  RB g fr b (RID (g_in g) b) (RFG (g_in g) b) regs m.
Definition RFb (g : ghost) (fr : Z) (b : nat) (idb fgb : list byte) (phi : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  RB g fr b idb fgb regs m /\ rnb g b <> 0 /\ rg regs 24 phi /\ bytes_at rsegs m phi (rt_F (g_in g) (Z.of_nat b)).
Definition RFx (g : ghost) (fr : Z) (b : nat) (idb fgb : list byte) (phi : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  RFb g fr b idb fgb phi regs m /\ rg regs 18 (rnb g b).
Definition RF (g : ghost) (fr : Z) (b : nat) (phi : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  RFx g fr b (RID (g_in g) b) (RFG (g_in g) b) phi regs m.
(* Push 10 (a Theorem Labs lane, the R8-R12 lane's Seg/RNCuts.v (not in this delivery) at 837bd45000f): RXS, the round-trip spills and the fragment
   record's addressability that the calls of R9 (0x81678 `ld a2,56(s1)`), R10 (0x816b4 .. 0x816bc, 0x816ec .. 0x81700,
   0x81754 .. 0x81768), R12 (0x816bc .. 0x816cc) and, on the b = 0 CONFIG path, R17 / R18 (0x817f8, 0x81800 ..
   0x81844) read. Producers (image-A listing, s5 = fr + 2176 from 0x81338):
   [A + 48] = fr + 2256 (t3 = s5 + 80, 0x81390; stored 0x814e0, R1), [A + 56] = fr + 2368 (t4 = s5 + 192, 0x81394;
   stored 0x814dc, R1), [A + 88] = fr + 2448 (t5 = s5 + 272, 0x81398; stored 0x814d8, R1), [A + 80] = fr + 2464
   (t6 = s5 + 288, 0x8139c; stored 0x814d4, R1), [A + 72] = fr + 2496 (ra = s5 + 320, 0x813a0; stored 0x814d0, R1),
   [A + 16] = mrow + 16 (0x81534 / 0x81538, R5), [A + 8] = mrow + 20 (0x81540 / 0x81544, R5), [A + 192] = decl_slot fr
   (0x8135c / 0x81360, A4), [A + 216] = fr + 2528 (0x81354 / 0x81358, A4); the fragment record's 72 bytes at fr + 2256
   are addressable from R3's shadow stores S(fr) + 282 .. 290 (0x814dc .. 0x814e8, 0x81504 / 0x81508, 0x8150c ..
   0x81514). Every one is set before the loop head 0x81574, so the b = 0 chain carries each from its producer
   (A5 .. R5, see Inv_A81400_at .. Inv_A81588), and none is written in 0x81574 .. 0x81904 (no store to [s1 + ...];
   the loop's frame shadow stores are S(fr) + 296 .. 323): RXS is loop-carried, on every cut Inv_A815cc_at ..
   Inv_A81924_at, and R21's latch (0x818f4 .. 0x81900) and R7's n_b = 0 skip (0x81594 -> 0x818f4) carry it into
   Inv_A815cc_at (S b); no loop instruction re-establishes it. *)
Definition RXS (g : ghost) (fr : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  spill regs m 48 (fr + 2256) /\ spill regs m 56 (fr + 2368) /\ spill regs m 88 (fr + 2448) /\
  spill regs m 80 (fr + 2464) /\ spill regs m 72 (fr + 2496) /\
  spill regs m 8 (mrow (g_in g) + 16) /\ spill regs m 0 (mrow (g_in g) + 20) /\
  spill regs m 200 (decl_slot fr) /\ spill regs m 216 (fr + 2528) /\
  addressable m (fr + 2256) 72.

(* Frame loop (F1-F38), turn j: s5 = j, s7 = Phi, s2 = len, s4 = body ptr, s8 = k, s9 = blk; id/frag of the entry
   (fr+2688/2768); first-frag FS at the A+88/96/104/112 spills; p/B at fr+176; check_ports ports fr+128, first fr+160. *)
Definition IDb (g : ghost) (fr : Z) (idb : list byte) (m : word -> option byte) : Prop :=
  IDBe g fr idb m /\ RcIdentModel.id_ok idb.
Definition FGb (g : ghost) (fr : Z) (st : list byte) (m : word -> option byte) : Prop :=
  FGBe g fr st m /\ frag_ok st.
(* v1.9 first-fragment state (SlotModel.v fstate {have; n; body}, shared with image B), image A's layout,
   measured on the v1.9.0 listing: SROA keeps `have` and `n` in spills and only the body tail first.sroa.7 in the
   frame.
   - have: [A + 104], zeroed before the loop at 0x81cec `sd zero,104(s1)` (P12), set on the opens arm at 0x823d8 /
     0x823dc `li a0,1; sd a0,104(s1)`, read by F16 at 0x82210 `ld a0,104(s1)` / 0x82214 `beqz a0`.
   - n: [A + 112], zeroed at 0x81ce8 `sd zero,112(s1)` (P12), set at 0x823e0 `sd s9,112(s1)` with s9 = block[8]
     (0x823a4 `addi a0,s7,26`, 0x823b8 `lbu s9,0(a0)`), read by F16 at 0x821cc `ld t0,112(s1)`.
   - body: the bytes at fr + 2880 = first.sroa.7 (35 bytes; [A + 32] = fr + 2880 from 0x813c8 / 0x813cc
     `addi a0,s5,704; sd a0,32(s1)` with s5 = fr + 2176), zeroed by P3's 0x81b68 .. 0x81b74
     `__asan_memset([A + 32], 0, 35)`, written on the opens arm by 0x823c8 .. 0x82480
     `__asan_memcpy([A + 32], s7 + 27, s9)`, read by F16's inlined joined_byte through [A + 56] = fr + 2889 /
     [A + 48] = fr + 2890 (0x81d2c .. 0x81d3c) at 0x82218 / 0x82250.
   - addressable: S(fr) + 360 .. 363 = 0 and S(fr) + 364 = 3 (P3's 0x81b40 / 0x81b44 / 0x81b5c / 0x81b60 / 0x81b64),
     so the 35 bytes from fr + 2880 are addressable (the checked memcpy and joined_byte's shadow checks read
     them); the next store to S(fr) + 360 .. 364 is X1's re-poisoning 0x82b34 .. 0x82b44, after the loop.
   The body is exactly the n bytes the last FIRST copied (fs_body s), not padded: the memcpy writes s9 = n bytes
   and the memset runs once, before the loop, so after a shorter FIRST the bytes past n are the older FIRST's
   (the model leaves bytes past n unmodelled; joined_byte reads body[i] only for i < n).
   No other instruction of 0x81ce0 .. 0x82964 writes [s1 + 104 / 112], fr + 2880 .. 2914 or S(fr) + 360 .. 364
   (listing; callees get none of these addresses). *)
Definition FSb (g : ghost) (fr : Z) (s : fstate) (st : list byte) (regs : bvmap 5 word) (m : word -> option byte) :
    Prop :=
  spill regs m 104 (fs_have s) /\ spill regs m 112 (fs_n s) /\
  bytes_at rsegs m (fr + 2880) (fs_body s) /\ addressable m (fr + 2880) 35 /\ FI st s.
Definition IDj (g : ghost) (fr : Z) (j : nat) (m : word -> option byte) : Prop := IDb g fr (t_ID (g_in g) j) m.
Definition FGj (g : ghost) (fr : Z) (j : nat) (m : word -> option byte) : Prop := FGb g fr (t_FG (g_in g) j) m.
Definition FSj (g : ghost) (fr : Z) (j : nat) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  FSb g fr (fst_at (g_in g) j) (t_FG (g_in g) j) regs m.
Definition IFS (g : ghost) (fr : Z) (j : nat) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  IDj g fr j m /\ FGj g fr j m /\ FSj g fr j regs m.
Definition LK (g : ghost) (fr : Z) (j : nat) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  (j <= 255)%nat /\ rg regs 21 (Z.of_nat j) /\ OURb g fr m.
Definition LI (g : ghost) (fr : Z) (j : nat) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  LK g fr j regs m /\ CUR g (t_c (g_in g) j) regs /\ 1 <= t_left (g_in g) j /\ IFS g fr j regs m.
Definition FC (g : ghost) (fr : Z) (j : nat) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  spill regs m 224 (t_left (g_in g) j - t_h (g_in g) j) /\ rg regs 20 (g_p g + t_body (g_in g) j) /\
  rg regs 18 (t_len (g_in g) j).
Definition FT (g : ghost) (fr : Z) (j : nat) (phi : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  LK g fr j regs m /\ FC g fr j regs m /\ rg regs 23 phi /\ bytes_at rsegs m phi (t_phi (g_in g) j).
Definition V7 (g : ghost) (j : nat) (regs : bvmap 5 word) : Prop := rg regs 24 (t_k (g_in g) j).
Definition pBb (g : ghost) (fr : Z) (j : nat) (m : word -> option byte) : Prop :=
  bytes_at rsegs m (fr + 176) (t_B (g_in g) j).
Definition FB (g : ghost) (fr : Z) (j : nat) (phi : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  FT g fr j phi regs m /\ V7 g j regs /\ rg regs 25 (if t_big (g_in g) j then phi + 18 else 0) /\ pBb g fr j m.
Definition PORTS (g : ghost) (fr : Z) (j : nat) (m : word -> option byte) : Prop :=
  (t_rp (g_in g) j = 0 ->
     u32 m (fr + 128) (4 * RcLeaf.n_in (t_pbs (g_in g) j)) /\
     u32 m (fr + 132) (4 * RcLeaf.n_out (t_pbs (g_in g) j)) /\
     u32 m (fr + 136) (16 * RcLeaf.bt (t_pbs (g_in g) j) 7)) /\
  (t_rp (g_in g) j <> 0 -> u32 m (fr + 128) (-7) /\ u32 m (fr + 132) (-7) /\ u32 m (fr + 136) (-7)).
Definition FIRSTb (g : ghost) (fr : Z) (j : nat) (m : word -> option byte) : Prop :=
  b8 m (fr + 160) (t_first (g_in g) j).
(* Frame-loop variables read on the F15 / F16 close path (0x820e8-0x82134). The fragment scratch buffer sits at
   fragb fr = fr + 2768 (= [A+208], set 0x81374 addi a0,s5,592 with s5 = fr+2176, never rewritten in the loop); its
   three derived pointers are spilled once in the pre-loop block 0x81c6c-0x81c84 ([A+208]+8 -> [A+80], +19 -> [A+72],
   +15 -> [A+64], loop-invariant, not rewritten in the frame loop). The identity_fragment call 0x820b8 writes, into
   the output cells pp = [A+272] = fr+272 and pn = [A+264] = fr+304 (pointers set 0x81304/0x8130c), the pl pointer
   fragb fr + 19 and the pll f_pll (= fg_T - 13) when it opens a record (t_rf j = 1): the 0x8211c check [A+72] = [pp]
   and the 0x820f4-0x82118 bounds 0 <= [pp]-[A+80] <= 64 and 64 - ([pp]-[A+80]) >= [pn]+2 follow. *)
Definition fragb (fr : Z) : Z := fr + 2768.
Definition FLV (g : ghost) (fr : Z) (j : nat) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  spill regs m 80 (fragb fr + 15) /\ spill regs m 88 (fragb fr + 19) /\ spill regs m 96 (fragb fr + 8) /\
  spill regs m 272 (fr + 272) /\ spill regs m 264 (fr + 304) /\
  (t_rf (g_in g) j = 1 ->
     q64 m (fr + 272) (fragb fr + 19) /\
     q64 m (fr + 304) (f_pll (t_FG (g_in g) j) (t_g (g_in g) j))).

(* ---- A region (plan 3.3): the pre-frame cuts carry no FRA (the frame is not built yet); the FRA cuts start at
   A4 (0x810c4) after the 380 shadow bytes are written. A1's request cut and A2/A3 are the asan-only entry cuts. *)
(* Pre-frame subset of FRA (fr-independent; threaded through the A2 and A3 cuts so A3 assembles FRA with sl_fr_of,
   fix a1.4): the asan runtime at sp, the heap and runtime cells, the spill base A = s1 and entry sp S = s0, gp / tp /
   s10 = K, the slot window and errno writable, the 13 saved caller registers, the stack-low bound and alignments.
   Push 5c adds FRA's frame-independent additions: the whole slot window addressable (no frame shadow is
   written yet before A3's poisoning run, so the entry pre's addressability still holds of the whole window; the
   FRA form excludes the frame) and the three ENTRY stack-top facts. mem_inv is not carried (5d). *)
Definition PREF (g : ghost) (A sp : Z) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop :=
  AsanRTInv.RT sp mem md /\
  AC.aa_AH AC.ASYMS AsanRTInv.RT API (g_H g) mem md /\
  ro_agree rsegs mem /\ sink_none B mem md /\ m_halted md = None /\ G_img_c B AF.frame_RELRO mem /\
  getr regs 2 = Z_to_bv 64 sp /\ sp mod 16 = 0 /\ AC.aspZ regs = sp /\
  AC.aa_stklo AC.ASYMS AsanRTInv.RT API mem md <= g_S g - AF.SLOT_STACK /\
  getr regs 4 = Z_to_bv 64 (AC.as_tp AC.ASYMS) /\
  rg regs 8 (g_S g) /\ rg regs 9 A /\ getr regs 3 = getr (g_regs g) 3 /\ rg regs 26 ASAN_K /\
  A mod 32 = 0 /\ A <= g_S g /\ g_S g - 432 <= A /\ sp <= A /\ A + 416 <= g_S g /\
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
  AC.a_live_bytes (g_H g) <= 5 * 2 ^ 30.



(* A2 (0x80f54): the arm selection, at the `mv s5,a0` that takes the frame request's result r in a0 (0 = no side
   frame, else the side frame's base, 32-aligned and in FS above the FakeStack metadata); the pre-frame subset
   threaded (fix a1.4), with the input pointer s7 = p and size s8 = n of 0x80f20 / 0x80f04. ENT is threaded from
   A1 on (push 5c): the frame request is a callee run, so ent_call / ent_store carry the entry relation across it,
   and A3 hands it to the first FRA cut unchanged.
   Push 6c (a Theorem Labs lane, option 3 of group 3): the input facts of ENTRY's alib_pre (the input bytes at p; for
   n > 0 the block (p, n) is live and addressable), threaded A2 -> A3 -> A4 -> A5 to a Theorem Labs lane's R1 entry Inv_A81414;
   A1-A4 write only the frame, its shadow and the stack, never the input block. *)
Definition Inv_A80f54 (g : ghost) (c : config) : Prop :=
  exists regs mem md A r,
    c = mkCfg (mkst regs (Z_to_bv 64 0x80f54) mem (seg_rom segs)) md /\
    PREF g A A regs mem md /\ ENT g [] mem md /\ rg regs 10 r /\ 0 <= r < 2 ^ 64 /\
    rg regs 23 (g_p g) /\ rg regs 24 (g_n g) /\
    (r = 0 \/ (r mod 32 = 0 /\
       (forall FS, word_mem rsegs mem (AC.as_tp AC.ASYMS) FS -> 0 <= FS < 2 ^ 64 -> FS + 6328320 <= r) /\
       (forall a, r <= a < r + FRAME_BYTES -> AC.a_in_fs AC.ASYMS mem a) /\ FSREC r mem)) /\
    bytes_at rsegs mem (g_p g) (g_in g) /\
    (0 < g_n g -> In (g_p g, g_n g) (g_H g) /\ addressable mem (g_p g) (g_n g)).

(* A3 (0x80f68): the side-arm join (0x80f44 bnez s5,0x80f68); fr fixed, about to write the header and the 380 shadow
   bytes. The pre-frame subset threaded (fix a1.4) plus ENT, fr and the frame-location disjunction, told apart by s5
   (real arm s5 = 0, sp lowered to fr; side arm s5 = fr, sp = A). No s3 = S(fr) yet (set at 0x80f78 / 0x80fa0, fix
   a1.5). `fr + 3040 <= A` is at top level (5d): Inv_A810e4's FRAS needs it on both arms. Push 6c: the input
   facts (see A2). *)
Definition Inv_A80f88 (g : ghost) (c : config) : Prop :=
  exists regs mem md A fr sp s5,
    c = mkCfg (mkst regs (Z_to_bv 64 0x80f88) mem (seg_rom segs)) md /\
    PREF g A sp regs mem md /\ ENT g [] mem md /\
    rg regs 22 fr /\ fr mod 32 = 0 /\ rg regs 21 s5 /\ 0 <= fr < 2 ^ 64 /\ fr + FRAME_BYTES <= A /\
    (s5 = 0 \/ s5 = fr) /\ rg regs 23 (g_p g) /\ rg regs 24 (g_n g) /\
    ((s5 = 0 /\ sp = fr /\ (forall a, fr <= a < fr + FRAME_BYTES ->
        AC.aa_stklo AC.ASYMS AsanRTInv.RT API mem md <= a < APPMEM_END)) \/
     (s5 = fr /\ sp = A /\
        (forall FS, word_mem rsegs mem (AC.as_tp AC.ASYMS) FS -> 0 <= FS < 2 ^ 64 -> FS + 6328320 <= fr) /\
        (forall a, fr <= a < fr + FRAME_BYTES -> AC.a_in_fs AC.ASYMS mem a) /\ FSREC fr mem)) /\
    bytes_at rsegs mem (g_p g) (g_in g) /\
    (0 < g_n g -> In (g_p g, g_n g) (g_H g) /\ addressable mem (g_p g) (g_n g)).

(* A4 (0x810c4): first FRA cut, taken on FRAS because the selector is not spilled to [A + 32] until 0x812cc; the
   size test 0x812a8-0x812c4 is in this segment (fall-through n < 2^26 to A5, branch n >= 2^26 to Jrel by
   slot_early with the selector in register 21 only). Register pins: every callee-saved register seg_A4
   (0x810c4-0x813a4) reads, all set before the call at 0x810c0 -- s2 = -8 and s4 = -14 (0x80f80 / 0x80f7c, the
   64-bit two's complements), s5 = the selector (0x80f34 / 0x80f3c), s6 = fr (0x80f40 / 0x80f50), s7 = p
   (0x80f40), s8 = n (0x80f24), s9 = S(fr) + 68 (0x810d4 addi s9,s3,68). s3 = S(fr) is already in FRAS.
   Push 6c: the input facts (see A2). *)
Definition Inv_A810e4 (g : ghost) (c : config) : Prop :=
  CUTST0 g 0x810e4 [] (fun fr s5 regs m =>
    g_n g <= AC.ANMAX /\
    rg regs 18 (-8) /\ rg regs 20 (-14) /\ rg regs 21 s5 /\ rg regs 22 fr /\
    rg regs 23 (g_p g) /\ rg regs 24 (g_n g) /\ rg regs 25 (Sfr fr + 68) /\
    bytes_at rsegs m (g_p g) (g_in g) /\
    (0 < g_n g -> In (g_p g, g_n g) (g_H g) /\ addressable m (g_p g) (g_n g))) c.
(* A5 (0x813a8): FRA; the our[] loop head, turn t (0 <= t <= 6). a Theorem Labs lane's adopt1-for-A.md (a working note, not in this delivery) (07:03Z) adds the two
   record pointers image A keeps in registers instead of spills: s5 = fr + 2176 (the identity record, 0x81338)
   and t3 = fr + 2256 (the fragment record, 0x81340, spilled only at 0x81488 inside R1). a2 (05:51Z) carries the
   frame-shadow pointer spill [A + 152] = S(fr) + 68 (stored 0x812c8) from here to R2, since R2 reads it at
   0x814d0 and no cut between produces it. *)
(* two Theorem Labs lanes' image-A twins (p5c-plan-B.md items 1 and 21 (a working note, not in this delivery), owner-approved): the our[] spill [A + 168] = fr + 2624
   (stored 0x8139c, in the A4 segment before this head), the catalogue cell s2 = fr + 2656 (0x81368) that R2
   reads at 0x81500, and t2 = fr + 544 (0x81378) -- image A spills it to [A + 128] only at 0x814e4, inside R1,
   so the two cuts before that carry the register, not the spill. *)
(* Push 6c: the input cursor, not the frame base. Push 5's `rg regs 22 fr` held on turn 0 only (0x813a8 is
   `mv s6,s7`, so on the back edge 0x81430 s6 is the cursor); the cut now names what 0x813a8 / 0x813b8 copy:
   s7 = p + min t n and s8 = n - min t n (A4's p / n on turn 0; R1's 0x81478 `addi s7,s6,1` / 0x81474
   `addi s8,s9,-1` on the back edge). Also the facts A5 hands to Inv_A81414 (a Theorem Labs lane's R1 entry) that the A4
   segment sets and the loop keeps: ra = fr + 2496, t4 / t5 / t6 = fr + 2368 / 2448 / 2464 (0x81344 .. 0x81350),
   a1 = t (0 after the 0x81310 size test, 0x81408 on the back edge), a2 = 6 (0x81384), a3 = 7 (0x813ec),
   a4 = fr + 2624 (0x81364, reloaded from [A + 168] at 0x81428), our[]'s shadow byte S(fr) + 328 = 6 (0x8133c),
   and the 6 our[] bytes present (the first t are OUR). Last, the input facts (see A2). The turn range is
   0 <= t <= 5 (was <= 6): the back edge 0x81488 is taken only when 0x81484 `beq a1,a2` finds a1 = t + 1 <> 6, and
   R1's entry Inv_A81414_at, which A5 reaches with the same t, has 0 <= t <= 5. *)
(* Push 7 (a Theorem Labs lane 23:51Z and a Theorem Labs lane 23:48Z, via a Theorem Labs lane): from here to R21 (Inv_A81924_at) every cut
   carries the two record pointer spills [A + 144] = fr + 2688 (stored 0x81398) and [A + 208] = fr + 2768
   (stored 0x81374), both in the A4 segment and written by no later instruction of A5 .. R21, and the two frame
   records at fr + 2688 (38 bytes) and fr + 2768 (72 bytes) readable and writable with some content: R21's b = 6
   tail loads s11 = [A + 144] (0x8193c), and P1 / P2 hand all four on to Inv_A81b14. The exact [A + 144] spill
   replaces push 6c's `exists w, spill regs m 144 w`. *)
(* Push 9 (a Theorem Labs lane, P4 lane, via a Theorem Labs lane): the same cuts also carry the two code / scratch pointer spills
   [A + 280] = fr + 2960 (stored 0x81388) and [A + 240] = fr + 2976 (stored 0x81390), set in the A4 segment next to
   [A + 208] (0x81374) and written by no later instruction before P4, and the 1-byte code cell at fr + 2960 and the
   32-byte scratch at fr + 2976 readable and writable with some content: P5's entry Inv_A81b90 reads all four, and
   R21's b = 6 tail, P1 / P2 / P3 and P4 hand them on. *)
(* Push 10 (a Theorem Labs lane, for R17 / R18 and the loop cuts' RXS): from here on the b = 0 chain carries each RXS conjunct
   from its producer (see RXS): A4's [A + 192] = decl_slot fr (0x81360) and [A + 216] = fr + 2528 (0x81358) on
   Inv_A81400_at .. Inv_A81588; R1's [A + 56] / [A + 88] / [A + 80] / [A + 72] (0x81484 / 0x81480 / 0x8147c /
   0x81478, from t4 / t5 / t6 / ra, which this cut and Inv_A81414_at pin) on Inv_A814f8 .. Inv_A81588, next to R1's
   [A + 48] (0x81488) that Inv_A814f8 .. Inv_A81578 had; [A + 48] and R3's 72 fragment-record bytes addressable
   (Inv_A81578) on Inv_A81588; R5's [A + 16] / [A + 8] (0x81538 / 0x81544) first on Inv_A815cc_at (RXS). No
   instruction of 0x813a8 .. 0x81570 other than these producers stores to [s1 + 8 / 16 / 48 / 56 / 72 / 80 / 88 /
   192 / 216] or to the shadow bytes S(fr) + 282 .. 290 after R3. *)
Definition Inv_A81400_at (g : ghost) (t : Z) (c : config) : Prop :=
  CUTST g 0x81400 [] (fun fr regs m => g_n g < 2 ^ 26 /\ 0 <= t <= 5 /\
    rg regs 23 (g_p g + Z.min t (g_n g)) /\ rg regs 24 (g_n g - Z.min t (g_n g)) /\
    bytes_at rsegs m (fr + 2624) (firstn (Z.to_nat t) (OUR (g_in g))) /\
    rg regs 21 (fr + 2176) /\ rg regs 28 (fr + 2256) /\ spill regs m 152 (Sfr fr + 68) /\
    rg regs 18 (fr + 2656) /\ PRO g fr regs m /\ rg regs 7 (fr + 544) /\
    rg regs 1 (fr + 2496) /\ rg regs 11 t /\ rg regs 12 6 /\ rg regs 13 7 /\ rg regs 14 (fr + 2624) /\
    rg regs 29 (fr + 2368) /\ rg regs 30 (fr + 2448) /\ rg regs 31 (fr + 2464) /\
    b8 m (Sfr fr + 328) 6 /\ rg regs 27 (fr + 2688) /\
    spill regs m 144 (fr + 2688) /\ spill regs m 192 (fr + 2768) /\
    (exists idb, rw_cells rsegs m (fr + 2688) [CB 38 idb]) /\ (exists junk, rw_cells rsegs m (fr + 2768) [CB 72 junk]) /\
    spill regs m 280 (fr + 3040) /\ spill regs m 240 (fr + 3056) /\
    (exists jy, rw_cells rsegs m (fr + 3040) [CB 1 jy]) /\ (exists junk, rw_cells rsegs m (fr + 3056) [CB 32 junk]) /\
    spill regs m 200 (decl_slot fr) /\ spill regs m 216 (fr + 2528) /\
    (exists junk, length junk = Z.to_nat (6 - t) /\
       bytes_at rsegs m (fr + 2624) (firstn (Z.to_nat t) (OUR (g_in g)) ++ junk))) c.
Definition Inv_A81400 (g : ghost) (c : config) : Prop := exists t, Inv_A81400_at g t c.

(* ---- Round trip (R1-R21), turn b : nat. R1 is the catalogue setup; R7 malloc gains the buffer Phi_r, R20 free
   drops it. The register/model content of each cut is the ubsan twin (R01-R23, plan-ubsan 3.2) under renaming;
   stated here at the FRA + heap + a0-result + model-value level (plan 3.2/3.3). *)
(* R1 (0x813bc, turn t of the our[] loop): push 6c, a Theorem Labs lane's Seg/R1.v (a version not in this delivery) Inv_A813bc_loc_at (
   written on a working branch 4f3a7c0b23c, seg_R1 Qed), verbatim: the push-5 body (g_n g < 2 ^ 26) plus
   - the loop registers of turn t: a0 = a4 = our + t, a1 = t + 1, a2 = 6, a3 = 7 (0x81334 / 0x81394), the cursor
     s6 = p + min t n and left s9 = n - min t n (fuzz_u8);
   - the frame pointers the odd-mode tail spills at 0x81478-0x8148c: x1 = fr + 2496, t2 = fr + 544,
     t3 = fr + 2256, t4 = fr + 2368, t5 = fr + 2448, t6 = fr + 2464, s2 = fr + 2656 (the catalogue count cell)
     and s5 = fr + 2176 (R2 carries it on);
   - the our[] shadow byte S(fr) + 328 = 06 (OUR, 0x8133c) and the spills [A + 152], [A + 168] R2 carries on;
   - the input facts of IC.3 IN (from alib_pre): the bytes of the input block and, when n > 0, that it is a live
     block of H and addressable;
   - the our[] bytes written so far: the first t are OUR, the rest unread.
   R1's exits: Inv_A814f8 (its R1.v copy Inv_A814a0_loc is the push-5 Inv_A814f8; push 6c adds s7 = mode and
   our[] 6 there, which R1 re-states) and Inv_A81b14. *)
Definition Inv_A81414_at (g : ghost) (t : Z) (c : config) : Prop :=
  CUTST g 0x81414 [] (fun fr regs m =>
    g_n g < 2 ^ 26 /\ 0 <= t <= 5 /\
    rg regs 1 (fr + 2496) /\ rg regs 7 (fr + 544) /\
    rg regs 10 (fr + 2624 + t) /\ rg regs 11 (t + 1) /\ rg regs 12 6 /\ rg regs 13 7 /\
    rg regs 14 (fr + 2624 + t) /\ rg regs 18 (fr + 2656) /\ rg regs 21 (fr + 2176) /\
    rg regs 22 (g_p g + Z.min t (g_n g)) /\ rg regs 25 (g_n g - Z.min t (g_n g)) /\
    rg regs 28 (fr + 2256) /\ rg regs 29 (fr + 2368) /\ rg regs 30 (fr + 2448) /\ rg regs 31 (fr + 2464) /\
    spill regs m 152 (Sfr fr + 68) /\ PRO g fr regs m /\
    b8 m (Sfr fr + 328) 6 /\ rg regs 27 (fr + 2688) /\
    spill regs m 144 (fr + 2688) /\ spill regs m 192 (fr + 2768) /\
    (exists idb, rw_cells rsegs m (fr + 2688) [CB 38 idb]) /\ (exists junk, rw_cells rsegs m (fr + 2768) [CB 72 junk]) /\
    spill regs m 280 (fr + 3040) /\ spill regs m 240 (fr + 3056) /\
    (exists jy, rw_cells rsegs m (fr + 3040) [CB 1 jy]) /\ (exists junk, rw_cells rsegs m (fr + 3056) [CB 32 junk]) /\
    spill regs m 200 (decl_slot fr) /\ spill regs m 216 (fr + 2528) /\
    (exists junk, length junk = Z.to_nat (6 - t) /\
       bytes_at rsegs m (fr + 2624) (firstn (Z.to_nat t) (OUR (g_in g)) ++ junk))) c.
Definition Inv_A81414 (g : ghost) (c : config) : Prop := exists t, Inv_A81414_at g t c.
(* R2 (0x814a0): a Theorem Labs lane's Seg/R2.v (a version not in this delivery; written on a working branch c53018cf6ad) Inv_A814a0_loc. The catalogue result, the
   frame-shadow pointer spill the 0x814d0 fill reads, s2 = fr + 2656 with the catalogue count [s2] = CAT_N
   (0x81368 / 0x814a8), s5 = fr + 2176, CUR g 7, and the spills R3 / R6 / R8 read. mem_inv dropped (5d).
   Push 6c (a Theorem Labs lane's b = 0 chain text, via a Theorem Labs lane 23:19Z), carried on to the loop head Inv_A815cc_at:
   s7 = mode (R1's own 0x814bc `lbu s7,0(s7)` on the n >= 7 path), from which R2 forms s2 = mrow at
   0x8150c .. 0x8151c, and our[]'s 6 bytes addressable (shadow S(fr) + 328 = 6, set 0x8138c `sb a2,328(s3)`;
   nothing before 0x82aa8 writes S(fr) + 328). *)
Definition Inv_A814f8 (g : ghost) (c : config) : Prop :=
  CUTST g 0x814f8 [] (fun fr regs m => g_n g < 2 ^ 26 /\ a0v regs CAT /\ OURb g fr m /\
    spill regs m 152 (Sfr fr + 68) /\
    rg regs 18 (fr + 2656) /\ q64 m (fr + 2656) CAT_N /\ rg regs 21 (fr + 2176) /\ CUR g 7 regs /\
    spill regs m 48 (fr + 2256) /\ spill regs m 128 (fr + 544) /\
    PRO g fr regs m /\
    rg regs 23 (mode (g_in g)) /\
    spill regs m 144 (fr + 2688) /\ spill regs m 192 (fr + 2768) /\
    (exists idb, rw_cells rsegs m (fr + 2688) [CB 38 idb]) /\ (exists junk, rw_cells rsegs m (fr + 2768) [CB 72 junk]) /\
    spill regs m 280 (fr + 3040) /\ spill regs m 240 (fr + 3056) /\
    (exists jy, rw_cells rsegs m (fr + 3040) [CB 1 jy]) /\ (exists junk, rw_cells rsegs m (fr + 3056) [CB 32 junk]) /\
    spill regs m 56 (fr + 2368) /\ spill regs m 88 (fr + 2448) /\ spill regs m 80 (fr + 2464) /\
    spill regs m 72 (fr + 2496) /\ spill regs m 200 (decl_slot fr) /\ spill regs m 216 (fr + 2528)) c.
(* R3 (0x814d4): a Theorem Labs lane's Seg/R3.v (a version not in this delivery; written on a working branch 8fd8ba5b2bd) Inv_A814d4_loc, word for word R2.v's exit.
   out[]'s first 1488 bytes are addressable after the 0x814d0 fill. mem_inv dropped (5d).
   Push 6c carries on to the loop head Inv_A815cc_at: the frame-shadow pointer spill [A + 152] = S(fr) + 68
   (Inv_A814f8 has it; R2's meta_fill_00 call writes shadow bytes S(fr) + 68 .. 253, not the spill or S(fr) + 328),
   the spill [A + 144] (stored at 0x81398, read by R21's tail at 0x8193c; = fr + 2688 since push 7, see A5),
   s2 = mrow (formed by R2 at 0x814c4 from s7 = mode; meta_fill_00 keeps s2) and our[]'s 6
   bytes addressable. *)
Definition Inv_A8152c (g : ghost) (c : config) : Prop :=
  CUTST g 0x8152c [] (fun fr regs m => g_n g < 2 ^ 26 /\ OURb g fr m /\ rg regs 21 (fr + 2176) /\
    CUR g 7 regs /\ spill regs m 48 (fr + 2256) /\ addressable m (fr + 544) 1488 /\
    spill regs m 128 (fr + 544) /\ PRO g fr regs m /\
    spill regs m 152 (Sfr fr + 68) /\ spill regs m 144 (fr + 2688) /\ spill regs m 192 (fr + 2768) /\
    (exists idb, rw_cells rsegs m (fr + 2688) [CB 38 idb]) /\ (exists junk, rw_cells rsegs m (fr + 2768) [CB 72 junk]) /\
    spill regs m 280 (fr + 3040) /\ spill regs m 240 (fr + 3056) /\
    (exists jy, rw_cells rsegs m (fr + 3040) [CB 1 jy]) /\ (exists junk, rw_cells rsegs m (fr + 3056) [CB 32 junk]) /\
    spill regs m 56 (fr + 2368) /\ spill regs m 88 (fr + 2448) /\ spill regs m 80 (fr + 2464) /\
    spill regs m 72 (fr + 2496) /\ spill regs m 200 (decl_slot fr) /\ spill regs m 216 (fr + 2528) /\
    rg regs 18 (mrow (g_in g))) c.
(* R4 (0x81520): a Theorem Labs lane's Seg/R3.v Inv_A81520_loc (a version not in this delivery; = R4.v's entry cut). FGBr is NOT here (only R4's memset at
   0x8152c writes the 72 fragment bytes); the three buffers this segment made addressable are (out[] 1492 after
   the 0x814ec store, id 38, frag 72, the last being R4's memset premise). FGBr g fr (RFG (g_in g) 0) and
   `rnb g b <> 0` dropped per a Theorem Labs lane (06:27Z / 07:42Z); mem_inv dropped (5d).
   Push 6c carries s5 = fr + 2176, [A + 152], [A + 144], s2 = mrow (R3's reac_identity_init call keeps s5 and s2)
   and our[]'s 6 bytes addressable (R3's shadow stores are S(fr) + 254 .. 290) on to the loop head. *)
Definition Inv_A81578 (g : ghost) (c : config) : Prop :=
  CUTST g 0x81578 [] (fun fr regs m => g_n g < 2 ^ 26 /\ CUR g 7 regs /\ OURb g fr m /\
    IDBr g fr (RID (g_in g) 0) m /\ spill regs m 48 (fr + 2256) /\
    addressable m (fr + 544) 1492 /\ addressable m (fr + 2176) 38 /\ addressable m (fr + 2256) 72 /\
    spill regs m 128 (fr + 544) /\ PRO g fr regs m /\
    rg regs 21 (fr + 2176) /\ spill regs m 152 (Sfr fr + 68) /\ spill regs m 144 (fr + 2688) /\
    spill regs m 192 (fr + 2768) /\
    (exists idb, rw_cells rsegs m (fr + 2688) [CB 38 idb]) /\ (exists junk, rw_cells rsegs m (fr + 2768) [CB 72 junk]) /\
    spill regs m 280 (fr + 3040) /\ spill regs m 240 (fr + 3056) /\
    (exists jy, rw_cells rsegs m (fr + 3040) [CB 1 jy]) /\ (exists junk, rw_cells rsegs m (fr + 3056) [CB 32 junk]) /\
    spill regs m 56 (fr + 2368) /\ spill regs m 88 (fr + 2448) /\ spill regs m 80 (fr + 2464) /\
    spill regs m 72 (fr + 2496) /\ spill regs m 200 (decl_slot fr) /\ spill regs m 216 (fr + 2528) /\
    rg regs 18 (mrow (g_in g))) c.
(* R5 (0x81530): a Theorem Labs lane's Seg/R4.v / Seg/R5.v (versions not in this delivery; written on working branches 215203173df / 14beceffa5f) Inv_A81530_loc, the same text in both.
   OUTA (a Theorem Labs lane, 2026-10-27): loop invariant, see OUTA.
   Push 6c adds what R5 must hand to Inv_A815cc_at 0 and does not write itself: s5 = fr + 2176, [A + 152],
   [A + 144], the identity record's 38 bytes addressable (Inv_A81578 has it; R4's checked memset writes only the
   fragment record's bytes), s2 = mrow (R5's 0x81594 `sd s2,112(s1)` gives the loop head's [A + 112]) and our[]'s 6
   bytes addressable. R5 writes [A + 112], [A + 104] / [A + 96] / [A + 64], s8 = 36 and a0 = [A + 128] itself. *)
Definition Inv_A81588 (g : ghost) (c : config) : Prop :=
  CUTST g 0x81588 [] (fun fr regs m => g_n g < 2 ^ 26 /\ CUR g 7 regs /\ OURb g fr m /\ OUTA fr m /\
    IDBr g fr (RID (g_in g) 0) m /\ FGBr g fr (RFG (g_in g) 0) m /\
    spill regs m 128 (fr + 544) /\ PRO g fr regs m /\
    rg regs 21 (fr + 2176) /\ spill regs m 152 (Sfr fr + 68) /\ spill regs m 144 (fr + 2688) /\
    spill regs m 192 (fr + 2768) /\
    (exists idb, rw_cells rsegs m (fr + 2688) [CB 38 idb]) /\ (exists junk, rw_cells rsegs m (fr + 2768) [CB 72 junk]) /\
    spill regs m 280 (fr + 3040) /\ spill regs m 240 (fr + 3056) /\
    (exists jy, rw_cells rsegs m (fr + 3040) [CB 1 jy]) /\ (exists junk, rw_cells rsegs m (fr + 3056) [CB 32 junk]) /\
    spill regs m 48 (fr + 2256) /\ spill regs m 56 (fr + 2368) /\ spill regs m 88 (fr + 2448) /\
    spill regs m 80 (fr + 2464) /\ spill regs m 72 (fr + 2496) /\
    spill regs m 200 (decl_slot fr) /\ spill regs m 216 (fr + 2528) /\ addressable m (fr + 2256) 72 /\
    addressable m (fr + 2176) 38 /\
    rg regs 18 (mrow (g_in g))) c.
(* R6 (0x81574): the b-loop head. Push 6c: a Theorem Labs lane's Seg/R6.v (a version not in this delivery; written on a working branch 84a41972a7d) Inv_A81574_loc_at:
   the push-5 body with a0 = fr + 544, s8 = 36 and the magic word [A + 64] = 0xe38f0000, plus the
   row spill [A + 112] = mrow (build_as's a1; it replaces `exists cb, spill regs m 112 cb`), s5 = fr + 2176 and
   [A + 152] = S(fr) + 68 (R7's n_b = 0 arm) and our[]'s 6 bytes addressable (build_as's d premise). R6.v's
   `addressable m (fr + 544) 1492` is OUTA (push 6a), kept where push 6a put it. R6.v's last conjunct, the class-0 /
   class-1 side-stack package (fp [0; 1] + reac_ctrl_build_as_tls of the build_as call), is on NO cut (a Theorem Labs lane,
   23:19Z): FRA gives it at every cut, by fra_fp (Seg/Tac_fsfree.v) with cs = [0; 1].
   Last two conjuncts, not in R6.v: [A + 144] and the identity record's
   38 bytes addressable, which R6 hands to Inv_A815ec_at for the loop body (R21's tail reads them; nothing in
   0x81574 .. 0x818f0 writes them).
   Push 10 (a Theorem Labs lane): RXS, last (see RXS): at b = 0 R5 gives it (its own [A + 16] / [A + 8] at 0x81538 / 0x81544,
   the rest from Inv_A81588), at S b R21's latch and R7's n_b = 0 skip carry it from Inv_A81924_at / Inv_A815ec_at. *)
Definition Inv_A815cc_at (g : ghost) (b : nat) (c : config) : Prop :=
  CUTST g 0x815cc [] (fun fr regs m => g_n g < 2 ^ 26 /\ RS g fr b regs m /\ OUTA fr m /\
    spill regs m 128 (fr + 544) /\ PRO g fr regs m /\
    spill regs m 104 0x21140 /\ spill regs m 96 0x1234 /\
    a0v regs (fr + 544) /\ rg regs 24 36 /\ spill regs m 64 0xe38f0000 /\
    spill regs m 112 (mrow (g_in g)) /\
    rg regs 21 (fr + 2176) /\
    spill regs m 152 (Sfr fr + 68) /\
    spill regs m 144 (fr + 2688) /\ addressable m (fr + 2176) 38 /\ spill regs m 192 (fr + 2768) /\
    (* push 13B: our[]'s 6 bytes addressable is in PRO *)
    (exists idb, rw_cells rsegs m (fr + 2688) [CB 38 idb]) /\ (exists junk, rw_cells rsegs m (fr + 2768) [CB 72 junk]) /\
    spill regs m 280 (fr + 3040) /\ spill regs m 240 (fr + 3056) /\
    (exists jy, rw_cells rsegs m (fr + 3040) [CB 1 jy]) /\ (exists junk, rw_cells rsegs m (fr + 3056) [CB 32 junk]) /\
    RXS g fr regs m) c.
Definition Inv_A815cc (g : ghost) (c : config) : Prop := exists b, Inv_A815cc_at g b c.
(* R7 (0x81594): the allocation cut, a Theorem Labs lane's validated Inv_A81594_loc. Not a CUTST: it names the model md for
   the allocation pre a_call_pre at AK_MALLOC, whose ROOM side comes from FRA's live-bytes bound. The request
   a0 = rt_n(in, b) is bounded so that ContractPlace's a_place_room_of_alive applies to a_size of it (the frame's
   ALIVE_MAX premise stays FRA's a_live_bytes (g_H g) <= 5 * 2^30). The three inline checks at 0x8159c-0x815d8 read
   the reciprocal s8 = 36 (0x815ac) and the magic word at [A + 64] = 0xe38f0000 (0x815a8/0x815c0/0x815c4).
   a4 (pending-5b line 16, decided): `rnb g b <> 0` is DROPPED (build_as may return 0, so R7's n_b = 0 exit is
   live) and the build_as out pointer spill [A + 128] = fr + 544 (read 0x815f4) is ADDED; a Theorem Labs lane's R5 needs the same.
   a4 (05:46Z): on the n_b = 0 arm the cut also carries the turn-b identity and fragment records, which R21's
   b = 6 tail reads back. mem_inv dropped there (FRA no longer carries it, push 5d).
   OUTA (a Theorem Labs lane, 2026-10-27): loop invariant, see OUTA.
   Push 6c (a Theorem Labs lane, 23:00Z / 23:19Z): the catalogue-row / our[] / round_trip.box / [A + 144] / frame-shadow
   pointer spills, s5 = fr + 2176 and the identity record's and our[]'s bytes addressable are at the top level
   (the loop body R8-R21 carries them to the latch, see R8); the n_b = 0 arm keeps the turn-b records. R6 gives
   all of them from its entry.
   Push 10 (a Theorem Labs lane, for X81640 at R7's exit 0x815e8, the R8-R12 lane's Seg/RNCuts.v (not in this delivery) at 837bd45000f): RXS, last
   (R6 carries it from Inv_A815cc_at; build_as writes no frame spill); the turn-b identity and fragment records on
   both arms (push 5b's `rnb g b = 0 ->` guard dropped: RS of Inv_A815cc_at gives them for every b and build_as
   writes only out[] = [fr + 544, fr + 2036), apart from fr + 2176 / fr + 2256); and, when n_b <> 0, out[]'s n_b
   bytes = rt_F of turn b (build_as's post at 0x81590), which wrapper_malloc keeps, so R7 gives X81640's
   out[] = rt_F (0x815e8 is reached only with rnb g b <> 0). R6 (0x81574 -> 0x81594) produces all three.
   Push 11 group F (the R6 refit, a Theorem Labs lane): the rt_F conjunct is guarded by `rnb g b <> 0`. When
   rnb g b = 0 (rt_E false: istar in {0, 2, 3} at b = 5, 6) build_as returns 0 and writes no out[] byte, but rt_F
   still has 52 bytes (em_fr's trailer at bytes 50 .. 51), so the push-10 unconditional form was false there. *)
Definition Inv_A815ec_at (g : ghost) (b : nat) (c : config) : Prop :=
  exists regs mem md fr A,
    c = mkCfg (mkst regs (Z_to_bv 64 0x815ec) mem (seg_rom segs)) md /\
    FRA g fr [] regs mem md /\ ENT g [] mem md /\
    g_n g < 2 ^ 26 /\ (b <= 6)%nat /\ 0 <= rnb g b <= AC.ANMAX /\
    0 <= AC.a_size (rnb g b) <= 616472576 /\
    0 <= A < 2 ^ 64 /\ rg regs 9 A /\ rg regs 24 36 /\ a0v regs (rnb g b) /\ q64 mem (A + 64) 0xe38f0000 /\
    spill regs mem 128 (fr + 544) /\
    IDBr g fr (RID (g_in g) b) mem /\ FGBr g fr (RFG (g_in g) b) mem /\
    (rnb g b <> 0 -> bytes_at rsegs mem (fr + 544) (rt_F (g_in g) (Z.of_nat b))) /\
    rg regs 23 (Z.of_nat b) /\ OURb g fr mem /\ OUTA fr mem /\ CUR g 7 regs /\
    spill regs mem 112 (mrow (g_in g)) /\ PRO g fr regs mem /\
    spill regs mem 104 0x21140 /\ spill regs mem 96 0x1234 /\ spill regs mem 144 (fr + 2688) /\
    spill regs mem 192 (fr + 2768) /\
    (exists idb, rw_cells rsegs mem (fr + 2688) [CB 38 idb]) /\ (exists junk, rw_cells rsegs mem (fr + 2768) [CB 72 junk]) /\
    spill regs mem 280 (fr + 3040) /\ spill regs mem 240 (fr + 3056) /\
    (exists jy, rw_cells rsegs mem (fr + 3040) [CB 1 jy]) /\ (exists junk, rw_cells rsegs mem (fr + 3056) [CB 32 junk]) /\
    spill regs mem 152 (Sfr fr + 68) /\ rg regs 21 (fr + 2176) /\ addressable mem (fr + 2176) 38 /\
    RXS g fr regs mem.
(* The loop body R8-R21 (push 6c, a Theorem Labs lane 23:00Z / 23:19Z): every cut from R8 to R21 carries the facts that the
   B3 cuts (a Theorem Labs lane's B3Cuts v4), R21's b = 6 tail and the loop head Inv_A815cc_at (S b) at R21's latch read, so R10
   (0x81628 -> 0x81710 / 0x81770 / 0x81794) and R13 (0x816dc -> 0x818cc) can give them: the spills
   [A + 112] = mrow (0x8153c), [A + 128] = fr + 544 (0x8148c), [A + 168] = fr + 2624 (0x8139c),
   [A + 104] = 0x21140, [A + 96] = 0x1234, [A + 64] = 0xe38f0000 (0x815b4 / 0x815bc / 0x815c4), [A + 144] (0x81398)
   and [A + 152] = S(fr) + 68 (0x812c8), s5 = fr + 2176 (0x81338), the identity record's 38 bytes (shadow
   S(fr) + 272 .. 276, set 0x814f0 .. 0x81500) and our[]'s 6 bytes (shadow S(fr) + 328, set 0x8133c) addressable.
   No instruction of 0x81594 .. 0x81904 writes s5, stores to [s1 + ...] or stores those shadow bytes (its frame
   shadow stores are S(fr) + 296 .. 323), and the callees keep s5 and the frame spills.
   Push 10 (a Theorem Labs lane): the same holds for RXS (see RXS), which every cut from R6 to R21 carries. *)
(* Push 10 (a Theorem Labs lane, the R8-R12 lane's Seg/RNCuts.v (not in this delivery) at 837bd45000f, adopted verbatim): each of the five cuts
   Inv_A81640_at .. Inv_A81708_at is its push-9 body, parenthesized, conjoined with one block X<addr>: the turn-b
   facts that the calls of the segment it enters read. X81640 (R7 gives it, R8 reads it): the turn-b identity and
   fragment records (Inv_A815ec_at's, kept by wrapper_malloc), out[]'s n_b bytes = rt_F (build_as's post at
   0x81590, on Inv_A815ec_at) and RXS. *)
Definition X81640 (g : ghost) (b : nat) (phi fr : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  IDBr g fr (RID (g_in g) b) m /\ FGBr g fr (RFG (g_in g) b) m /\
  bytes_at rsegs m (fr + 544) (rt_F (g_in g) (Z.of_nat b)) /\
  RXS g fr regs m.
(* R8 (0x815e8): the copy into the fresh buffer Phi. The count is in s2 (0x81598 mv s2,a0, read 0x815f8) and the
   source pointer is the spill [A + 128] = fr + 544 (0x815f4), whose rnb bytes the copy reads.
   OUTA (a Theorem Labs lane, 2026-10-27): loop invariant, see OUTA. *)
Definition Inv_A81640_at (g : ghost) (b : nat) (c : config) : Prop :=
  exists phi, CUTST g 0x81640 (hb1 phi (rnb g b)) (fun fr regs m => (g_n g < 2 ^ 26 /\ (b <= 6)%nat /\ rnb g b <> 0 /\
    a0v regs phi /\ HB m phi (rnb g b) /\ rg regs 18 (rnb g b) /\ spill regs m 128 (fr + 544) /\
    addressable m (fr + 544) (rnb g b) /\
    (exists src, bytes_at rsegs m (fr + 544) src /\ Z.of_nat (length src) = rnb g b) /\
    rg regs 23 (Z.of_nat b) /\ OURb g fr m /\ OUTA fr m /\ CUR g 7 regs /\
    spill regs m 112 (mrow (g_in g)) /\ PRO g fr regs m /\
    spill regs m 104 0x21140 /\ spill regs m 96 0x1234 /\ spill regs m 64 0xe38f0000 /\
    spill regs m 144 (fr + 2688) /\ spill regs m 192 (fr + 2768) /\
    (exists idb, rw_cells rsegs m (fr + 2688) [CB 38 idb]) /\ (exists junk, rw_cells rsegs m (fr + 2768) [CB 72 junk]) /\
    spill regs m 280 (fr + 3040) /\ spill regs m 240 (fr + 3056) /\
    (exists jy, rw_cells rsegs m (fr + 3040) [CB 1 jy]) /\ (exists junk, rw_cells rsegs m (fr + 3056) [CB 32 junk]) /\
    spill regs m 152 (Sfr fr + 68) /\ rg regs 21 (fr + 2176) /\
    addressable m (fr + 2176) 38) /\
    X81640 g b phi fr regs m) c.
(* OUTA (a Theorem Labs lane, 2026-10-27): loop invariant, see OUTA. The loop-body facts: see R8.
   Push 10: X81658 (R8 gives it, R9 reads it): RF (s8 = Phi from 0x815f0, Phi's bytes = rt_F copied from out[] by
   checked_memcpy 0x815fc, s2 = n_b from 0x81598, the turn-b records) and RXS. *)
Definition X81658 (g : ghost) (b : nat) (phi fr : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  RF g fr b phi regs m /\ RXS g fr regs m.
Definition Inv_A81658_at (g : ghost) (b : nat) (c : config) : Prop :=
  exists phi, CUTST g 0x81658 (hb1 phi (rnb g b)) (fun fr regs m => (g_n g < 2 ^ 26 /\ (b <= 6)%nat /\ HB m phi (rnb g b) /\ rg regs 23 (Z.of_nat b) /\ OURb g fr m /\ OUTA fr m /\ CUR g 7 regs /\
    spill regs m 112 (mrow (g_in g)) /\ spill regs m 128 (fr + 544) /\ PRO g fr regs m /\
    spill regs m 104 0x21140 /\ spill regs m 96 0x1234 /\ spill regs m 64 0xe38f0000 /\
    spill regs m 144 (fr + 2688) /\ spill regs m 192 (fr + 2768) /\
    (exists idb, rw_cells rsegs m (fr + 2688) [CB 38 idb]) /\ (exists junk, rw_cells rsegs m (fr + 2768) [CB 72 junk]) /\
    spill regs m 280 (fr + 3040) /\ spill regs m 240 (fr + 3056) /\
    (exists jy, rw_cells rsegs m (fr + 3040) [CB 1 jy]) /\ (exists junk, rw_cells rsegs m (fr + 3056) [CB 32 junk]) /\
    spill regs m 152 (Sfr fr + 68) /\ rg regs 21 (fr + 2176) /\
    addressable m (fr + 2176) 38) /\
    X81658 g b phi fr regs m) c.
Definition Inv_A81658 (g : ghost) (c : config) : Prop := exists b, Inv_A81658_at g b c.
(* OUTA (a Theorem Labs lane, 2026-10-27): loop invariant, see OUTA. The loop-body facts: see R8.
   Push 10: X81680 (R9 gives it, R10 reads it): RF, RXS, a0 = the parse kind rt_k of turn b (reac_ctrl_parse's post
   at 0x8167c) and s11 = 4 (0x81668). *)
Definition X81680 (g : ghost) (b : nat) (phi fr : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  RF g fr b phi regs m /\ RXS g fr regs m /\
  a0v regs (rt_k (g_in g) (Z.of_nat b)) /\ rg regs 27 4.
Definition Inv_A81680_at (g : ghost) (b : nat) (c : config) : Prop :=
  exists phi, CUTST g 0x81680 (hb1 phi (rnb g b)) (fun fr regs m => (g_n g < 2 ^ 26 /\ (b <= 6)%nat /\ HB m phi (rnb g b) /\ rg regs 23 (Z.of_nat b) /\ OURb g fr m /\ OUTA fr m /\ CUR g 7 regs /\
    spill regs m 112 (mrow (g_in g)) /\ spill regs m 128 (fr + 544) /\ PRO g fr regs m /\
    spill regs m 104 0x21140 /\ spill regs m 96 0x1234 /\ spill regs m 64 0xe38f0000 /\
    spill regs m 144 (fr + 2688) /\ spill regs m 192 (fr + 2768) /\
    (exists idb, rw_cells rsegs m (fr + 2688) [CB 38 idb]) /\ (exists junk, rw_cells rsegs m (fr + 2768) [CB 72 junk]) /\
    spill regs m 280 (fr + 3040) /\ spill regs m 240 (fr + 3056) /\
    (exists jy, rw_cells rsegs m (fr + 3040) [CB 1 jy]) /\ (exists junk, rw_cells rsegs m (fr + 3056) [CB 32 junk]) /\
    spill regs m 152 (Sfr fr + 68) /\ rg regs 21 (fr + 2176) /\
    addressable m (fr + 2176) 38) /\
    X81680 g b phi fr regs m) c.
Definition Inv_A81680 (g : ghost) (c : config) : Prop := exists b, Inv_A81680_at g b c.
(* OUTA (a Theorem Labs lane, 2026-10-27): loop invariant, see OUTA. The loop-body facts: see R8.
   Push 10: X816c4 (R10 gives it for b = 3, 4 (0x8163c / 0x81644), R11 reads it): b in {3, 4}, a0 = 1, RF, RXS and
   the three reply cells at fr + 2448 / 2464 / 2496 (reac_ctrl_identity_reply's post under reply_ok, call 0x81668
   with a2 / a3 / a4 = [A + 88] / [A + 80] / [A + 72]). *)
Definition X816c4 (g : ghost) (b : nat) (phi fr : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  (b = 3 \/ b = 4)%nat /\ a0v regs 1 /\ RF g fr b phi regs m /\ RXS g fr regs m /\
  rw_cells rsegs m (fr + 2448) [CB 2 (RcReply.reply_addr (rt_g (g_in g) (Z.of_nat b)))] /\
  rw_cells rsegs m (fr + 2464) [CB 8 (le8 (Z_to_bv 64 (phi + 38)))] /\
  rw_cells rsegs m (fr + 2496) [CB 8 (le8 (Z_to_bv 64 (RcReply.ir_s (rt_g (g_in g) (Z.of_nat b)) - 13)))].
Definition Inv_A816c4_at (g : ghost) (b : nat) (c : config) : Prop :=
  exists phi, CUTST g 0x816c4 (hb1 phi (rnb g b)) (fun fr regs m => (g_n g < 2 ^ 26 /\ (b <= 6)%nat /\ HB m phi (rnb g b) /\ rg regs 23 (Z.of_nat b) /\ OURb g fr m /\ OUTA fr m /\ CUR g 7 regs /\
    spill regs m 112 (mrow (g_in g)) /\ spill regs m 128 (fr + 544) /\ PRO g fr regs m /\
    spill regs m 104 0x21140 /\ spill regs m 96 0x1234 /\ spill regs m 64 0xe38f0000 /\
    spill regs m 144 (fr + 2688) /\ spill regs m 192 (fr + 2768) /\
    (exists idb, rw_cells rsegs m (fr + 2688) [CB 38 idb]) /\ (exists junk, rw_cells rsegs m (fr + 2768) [CB 72 junk]) /\
    spill regs m 280 (fr + 3040) /\ spill regs m 240 (fr + 3056) /\
    (exists jy, rw_cells rsegs m (fr + 3040) [CB 1 jy]) /\ (exists junk, rw_cells rsegs m (fr + 3056) [CB 32 junk]) /\
    spill regs m 152 (Sfr fr + 68) /\ rg regs 21 (fr + 2176) /\
    addressable m (fr + 2176) 38) /\
    X816c4 g b phi fr regs m) c.
Definition Inv_A816c4 (g : ghost) (c : config) : Prop := exists b, Inv_A816c4_at g b c.
(* OUTA (a Theorem Labs lane, 2026-10-27): loop invariant, see OUTA. The loop-body facts: see R8.
   Push 10: X81708 (R10 gives it for b = 6 (0x8163c / 0x81684), R12 reads it): b = 6, a0 = 1, RFb with the fragment
   record of turn 7 (CLOSE, written by reac_ctrl_identity_fragment, call 0x816ac with a0 = [A + 48] = fr + 2256), RXS
   and the three reply cells of fg_mem FgClose at fr + 2448 / 2464 / 2496. *)
Definition X81708 (g : ghost) (b : nat) (phi fr : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  b = 6%nat /\ a0v regs 1 /\
  RFb g fr b (RID (g_in g) b) (RFG (g_in g) (S b)) phi regs m /\ RXS g fr regs m /\
  bytes_at rsegs m (fr + 2448)
    (le2 (Z_to_bv 64 (RcFrag.fg_addr (RFG (g_in g) b) (rt_g (g_in g) (Z.of_nat b))))) /\
  bytes_at rsegs m (fr + 2464) (le8 (Z_to_bv 64 (fr + 2256 + 19))) /\
  bytes_at rsegs m (fr + 2496)
    (le8 (Z_to_bv 64 (RcFrag.fg_T (RFG (g_in g) b) (rt_g (g_in g) (Z.of_nat b)) - 13))).
Definition Inv_A81708_at (g : ghost) (b : nat) (c : config) : Prop :=
  exists phi, CUTST g 0x81708 (hb1 phi (rnb g b)) (fun fr regs m => (g_n g < 2 ^ 26 /\ (b <= 6)%nat /\ HB m phi (rnb g b) /\ rg regs 23 (Z.of_nat b) /\ OURb g fr m /\ OUTA fr m /\ CUR g 7 regs /\
    spill regs m 112 (mrow (g_in g)) /\ spill regs m 128 (fr + 544) /\ PRO g fr regs m /\
    spill regs m 104 0x21140 /\ spill regs m 96 0x1234 /\ spill regs m 64 0xe38f0000 /\
    spill regs m 144 (fr + 2688) /\ spill regs m 192 (fr + 2768) /\
    (exists idb, rw_cells rsegs m (fr + 2688) [CB 38 idb]) /\ (exists junk, rw_cells rsegs m (fr + 2768) [CB 72 junk]) /\
    spill regs m 280 (fr + 3040) /\ spill regs m 240 (fr + 3056) /\
    (exists jy, rw_cells rsegs m (fr + 3040) [CB 1 jy]) /\ (exists junk, rw_cells rsegs m (fr + 3056) [CB 32 junk]) /\
    spill regs m 152 (Sfr fr + 68) /\ rg regs 21 (fr + 2176) /\
    addressable m (fr + 2176) 38) /\
    X81708 g b phi fr regs m) c.
Definition Inv_A81708 (g : ghost) (c : config) : Prop := exists b, Inv_A81708_at g b c.
(* OUTA (a Theorem Labs lane, 2026-10-27): loop invariant, see OUTA. The loop-body facts: see R8.
   Push 10: RXS, last (R11 / R12 carry it from X816c4 / X81708; R13 carries it to Inv_A81924_at).
   Push 11 group D (the R11-R13 lane's Seg/RN2Cuts.v (not in this delivery) X816dc (X81734 here), a working branch faaa389f397), after RXS:
   a0 = 1, the ingest result (R13's 0x81734 `li a1,1` / 0x81738 `beq a0,a1,8191c`, else 0x8173c `j 82bf4`);
   s8 = phi (set 0x815f0 `mv s8,a0`, callee-saved through the reply / fragment / ingest calls; R13's 0x818c4
   `mv a0,s8` frees it); RB at the turn-(S b) records (identity record = the one ingest wrote, fragment record =
   RFG (S b): kept for b = 3, 4, CLOSE for b = 6), which Inv_A81924_at's RB reads. Producers: R11 / R12
   (RNIng.rn_ing_cont at 0x816dc); consumer: R13. *)
Definition X81734 (g : ghost) (b : nat) (phi fr : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  a0v regs 1 /\ rg regs 24 phi /\ RB g fr b (RID (g_in g) (S b)) (RFG (g_in g) (S b)) regs m.
Definition Inv_A81734_at (g : ghost) (b : nat) (c : config) : Prop :=
  exists phi, CUTST g 0x81734 (hb1 phi (rnb g b)) (fun fr regs m => g_n g < 2 ^ 26 /\ (b <= 6)%nat /\ HB m phi (rnb g b) /\ rg regs 23 (Z.of_nat b) /\ OURb g fr m /\ OUTA fr m /\ CUR g 7 regs /\
    spill regs m 112 (mrow (g_in g)) /\ spill regs m 128 (fr + 544) /\ PRO g fr regs m /\
    spill regs m 104 0x21140 /\ spill regs m 96 0x1234 /\ spill regs m 64 0xe38f0000 /\
    spill regs m 144 (fr + 2688) /\ spill regs m 192 (fr + 2768) /\
    (exists idb, rw_cells rsegs m (fr + 2688) [CB 38 idb]) /\ (exists junk, rw_cells rsegs m (fr + 2768) [CB 72 junk]) /\
    spill regs m 280 (fr + 3040) /\ spill regs m 240 (fr + 3056) /\
    (exists jy, rw_cells rsegs m (fr + 3040) [CB 1 jy]) /\ (exists junk, rw_cells rsegs m (fr + 3056) [CB 32 junk]) /\
    spill regs m 152 (Sfr fr + 68) /\ rg regs 21 (fr + 2176) /\
    addressable m (fr + 2176) 38 /\
    RXS g fr regs m /\
    X81734 g b phi fr regs m) c.
Definition Inv_A81734 (g : ghost) (c : config) : Prop := exists b, Inv_A81734_at g b c.
(* ---- B3 (R14-R21, 0x81710 .. 0x81a64): a Theorem Labs lane's Seg/B3Cuts.v (not in this delivery) v4 bodies (a working branch 554c83ce6f5,
   Inv_A81710s_at .. Inv_A818ccs_at), adopted as the official cuts. Each is the push-3 frozen body
   (parenthesized, with push 6a's OUTA after OURb, after RFb at 0x81878) plus the facts the B3 segments read and
   the "R21 extras": what R21's latch load, its b = 6 tail and the loop head Inv_A815cc_at (S b) read, carried on
   every cut of the chains into 0x818cc. a Theorem Labs lane's `AGr m` (the registered globals addressable) is DROPPED, because FRA
   carries exactly that conjunct. Push 6c changes to a Theorem Labs lane's text (a Theorem Labs lane, 23:00Z; a Theorem Labs lane agrees): the spill [A + 152]
   is exact (`spill regs m 152 (Sfr fr + 68)`, nothing in 0x81594 .. 0x818cc writes it; spill152_bounds gives
   a Theorem Labs lane's `exists Q` form back), and our[]'s 6 bytes addressable is added, so R21's latch gives Inv_A815cc_at (S b)
   (the loop body, see R8).
   Push 10 (a Theorem Labs lane): every B3 cut ends with RXS (see RXS), loop-carried from R10's exits (X81680) and R13's
   (Inv_A81734_at) to R21's latch into Inv_A815cc_at (S b). R14 / R17 / R18 keep their own copies of RXS's spills
   16 / 8 / 192 / 216, which a Theorem Labs lane's segments read by name.
   rsum: the unsigned sum of the first i of the 32 block bytes Phi_r[18..] of turn b. *)
Definition rsum (g : ghost) (b i : nat) : Z := RcModel.psum (skipn 18 (rt_g (g_in g) (Z.of_nat b))) i.
(* a Theorem Labs lane's bound form of the frame-shadow pointer spill (B3Cuts v3 / v4) follows from the exact one. *)
(* Push 14 group A (a Theorem Labs lane): the bound is Sfr fr + 328, so that P1's set_shadow_f8 (Q, 187) at 0x81ab4 misses
   our[]'s shadow byte S(fr) + 328 (68 + 187 = 255 <= 328). *)
Lemma spill152_bounds : forall fr regs m, spill regs m 152 (Sfr fr + 68) ->
  exists Q, spill regs m 152 Q /\ Sfr fr <= Q /\ Q + 187 <= Sfr fr + 328.
Proof. intros fr regs m H. exists (Sfr fr + 68). split; [exact H | lia]. Qed.
(* R14 (0x81710): the b = 0 CONFIG-path block-sum loop head (a Theorem Labs lane: R14 keeps spill 112 for R17 / R18 / R21, spills
   16 / 8 for R18, spill 192 for R17 -> R18, spill 216 and addressable (fr + 2528) 12 for R17's ports_parse). *)
Definition Inv_A81768_at (g : ghost) (b : nat) (c : config) : Prop :=
  exists phi i, CUTST g 0x81768 (hb1 phi (rnb g b)) (fun fr regs m =>
    (g_n g < 2 ^ 26 /\ (b <= 6)%nat /\ HB m phi (rnb g b) /\ rg regs 23 (Z.of_nat b) /\ OURb g fr m /\ OUTA fr m /\
     CUR g 7 regs /\
     (i <= 32)%nat /\ rg regs 10 (phi + 18 + Z.of_nat i) /\ rg regs 12 (phi + 18 + Z.of_nat i) /\
     rg regs 13 (32 - Z.of_nat i)) /\
    b = 0%nat /\ (i < 32)%nat /\ rg regs 11 (rsum g b i) /\ RF g fr b phi regs m /\
    spill regs m 112 (mrow (g_in g)) /\ spill regs m 8 (mrow (g_in g) + 16) /\
    spill regs m 0 (mrow (g_in g) + 20) /\ spill regs m 200 (decl_slot fr) /\ spill regs m 216 (fr + 2528) /\
    addressable m (fr + 2528) 12 /\
    spill regs m 128 (fr + 544) /\ (* R21 latch 0x81950 ld a0,128(s1); Inv_A815cc_at *)
    PRO g fr regs m /\ spill regs m 104 0x21140 /\ spill regs m 96 0x1234 /\ (* Inv_A815cc_at; PRO: push 13B *)
    spill regs m 64 0xe38f0000 /\ (* Inv_A815cc_at (push 5b): the magic word, no B3 store to [s1+64] *)
    rg regs 21 (fr + 2176) /\ (* R21 tail: s5 = the id record, 0x81990 lbu a0,2(s5) .. 0x81aac addi a0,s5,3 *)
    spill regs m 144 (fr + 2688) /\ (* R21 tail 0x81994 ld s11,144(s1) *)
    spill regs m 192 (fr + 2768) /\ (* R21 b = 6 tail -> Inv_A81ac0 / Inv_A81ac8: [A + 208] (push 7) *)
    (exists idb, rw_cells rsegs m (fr + 2688) [CB 38 idb]) /\ (exists junk, rw_cells rsegs m (fr + 2768) [CB 72 junk]) /\
    spill regs m 280 (fr + 3040) /\ spill regs m 240 (fr + 3056) /\ (* P5 entry Inv_A81b90 via R21's b = 6 tail (push 9) *)
    (exists jy, rw_cells rsegs m (fr + 3040) [CB 1 jy]) /\ (exists junk, rw_cells rsegs m (fr + 3056) [CB 32 junk]) /\
    spill regs m 152 (Sfr fr + 68) /\ (* R21 exit: 0x81b08 ld a0,152(s1); Inv_A815cc_at *)
    addressable m (fr + 2176) 38 /\ (* R21 tail: the strcmp wrapper's range at a0 = s5 + 3 (0x81a64) *)
    (* push 13B: our[]'s 6 bytes addressable is in PRO *)
    RXS g fr regs m (* push 10: loop-carried to Inv_A815cc_at (S b) *)) c.
Definition Inv_A81768 (g : ghost) (c : config) : Prop := exists b, Inv_A81768_at g b c.
(* R15 (0x81770): after reac_ctrl_identity_fragment; the turn-(S b) records, s8 = phi, a0 = 0. *)
Definition Inv_A817c8_at (g : ghost) (b : nat) (c : config) : Prop :=
  exists phi, CUTST g 0x817c8 (hb1 phi (rnb g b)) (fun fr regs m =>
    (g_n g < 2 ^ 26 /\ (b <= 6)%nat /\ HB m phi (rnb g b) /\ rg regs 23 (Z.of_nat b) /\ OURb g fr m /\ OUTA fr m /\
     CUR g 7 regs) /\
    RB g fr b (RID (g_in g) (S b)) (RFG (g_in g) (S b)) regs m /\ rg regs 24 phi /\ a0v regs 0 /\
    spill regs m 128 (fr + 544) /\ (* R21 latch 0x81950 ld a0,128(s1); Inv_A815cc_at *)
    PRO g fr regs m /\ spill regs m 104 0x21140 /\ spill regs m 96 0x1234 /\ (* Inv_A815cc_at; PRO: push 13B *)
    spill regs m 64 0xe38f0000 /\ (* Inv_A815cc_at (push 5b): the magic word, no B3 store to [s1+64] *)
    rg regs 21 (fr + 2176) /\ (* R21 tail: s5 = the id record, 0x81990 lbu a0,2(s5) .. 0x81aac addi a0,s5,3 *)
    spill regs m 112 (mrow (g_in g)) /\ (* R21 tail: row m, 0x819a0 .. 0x81a8c ld a0,112(s1) *)
    spill regs m 144 (fr + 2688) /\ (* R21 tail 0x81994 ld s11,144(s1) *)
    spill regs m 192 (fr + 2768) /\ (* R21 b = 6 tail -> Inv_A81ac0 / Inv_A81ac8: [A + 208] (push 7) *)
    (exists idb, rw_cells rsegs m (fr + 2688) [CB 38 idb]) /\ (exists junk, rw_cells rsegs m (fr + 2768) [CB 72 junk]) /\
    spill regs m 280 (fr + 3040) /\ spill regs m 240 (fr + 3056) /\ (* P5 entry Inv_A81b90 via R21's b = 6 tail (push 9) *)
    (exists jy, rw_cells rsegs m (fr + 3040) [CB 1 jy]) /\ (exists junk, rw_cells rsegs m (fr + 3056) [CB 32 junk]) /\
    spill regs m 152 (Sfr fr + 68) /\ (* R21 exit: 0x81b08 ld a0,152(s1); Inv_A815cc_at *)
    addressable m (fr + 2176) 38 /\ (* R21 tail: the strcmp wrapper's range at a0 = s5 + 3 (0x81a64) *)
    (* push 13B: our[]'s 6 bytes addressable is in PRO *)
    RXS g fr regs m (* push 10: loop-carried to Inv_A815cc_at (S b) *)) c.
Definition Inv_A817c8 (g : ghost) (c : config) : Prop := exists b, Inv_A817c8_at g b c.
(* R16 (0x81794): the b = 1 / b = 2 block-sum loop head. *)
Definition Inv_A817ec_at (g : ghost) (b : nat) (c : config) : Prop :=
  exists phi i, CUTST g 0x817ec (hb1 phi (rnb g b)) (fun fr regs m =>
    (g_n g < 2 ^ 26 /\ (b <= 6)%nat /\ HB m phi (rnb g b) /\ rg regs 23 (Z.of_nat b) /\ OURb g fr m /\ OUTA fr m /\
     CUR g 7 regs /\
     (i <= 32)%nat /\ rg regs 10 (phi + 18 + Z.of_nat i) /\ rg regs 12 (phi + 18 + Z.of_nat i) /\
     rg regs 13 (32 - Z.of_nat i)) /\
    (b = 1 \/ b = 2)%nat /\ (i < 32)%nat /\ rg regs 11 (rsum g b i) /\
    RFb g fr b (RID (g_in g) b) (RFG (g_in g) b) phi regs m /\
    spill regs m 128 (fr + 544) /\ (* R21 latch 0x81950 ld a0,128(s1); Inv_A815cc_at *)
    PRO g fr regs m /\ spill regs m 104 0x21140 /\ spill regs m 96 0x1234 /\ (* Inv_A815cc_at; PRO: push 13B *)
    spill regs m 64 0xe38f0000 /\ (* Inv_A815cc_at (push 5b): the magic word, no B3 store to [s1+64] *)
    rg regs 21 (fr + 2176) /\ (* R21 tail: s5 = the id record, 0x81990 lbu a0,2(s5) .. 0x81aac addi a0,s5,3 *)
    spill regs m 112 (mrow (g_in g)) /\ (* R21 tail: row m, 0x819a0 .. 0x81a8c ld a0,112(s1) *)
    spill regs m 144 (fr + 2688) /\ (* R21 tail 0x81994 ld s11,144(s1) *)
    spill regs m 192 (fr + 2768) /\ (* R21 b = 6 tail -> Inv_A81ac0 / Inv_A81ac8: [A + 208] (push 7) *)
    (exists idb, rw_cells rsegs m (fr + 2688) [CB 38 idb]) /\ (exists junk, rw_cells rsegs m (fr + 2768) [CB 72 junk]) /\
    spill regs m 280 (fr + 3040) /\ spill regs m 240 (fr + 3056) /\ (* P5 entry Inv_A81b90 via R21's b = 6 tail (push 9) *)
    (exists jy, rw_cells rsegs m (fr + 3040) [CB 1 jy]) /\ (exists junk, rw_cells rsegs m (fr + 3056) [CB 32 junk]) /\
    spill regs m 152 (Sfr fr + 68) /\ (* R21 exit: 0x81b08 ld a0,152(s1); Inv_A815cc_at *)
    addressable m (fr + 2176) 38 /\ (* R21 tail: the strcmp wrapper's range at a0 = s5 + 3 (0x81a64) *)
    (* push 13B: our[]'s 6 bytes addressable is in PRO *)
    RXS g fr regs m (* push 10: loop-carried to Inv_A815cc_at (S b) *)) c.
Definition Inv_A817ec (g : ghost) (c : config) : Prop := exists b, Inv_A817ec_at g b c.
(* R17 (0x817e4): after reac_box_catalogue_match; a0 = the matched row. *)
Definition Inv_A8183c_at (g : ghost) (b : nat) (c : config) : Prop :=
  exists phi, CUTST g 0x8183c (hb1 phi (rnb g b)) (fun fr regs m =>
    (g_n g < 2 ^ 26 /\ (b <= 6)%nat /\ HB m phi (rnb g b) /\ rg regs 23 (Z.of_nat b) /\ OURb g fr m /\ OUTA fr m /\
     CUR g 7 regs /\ spill regs m 216 (fr + 2528)) /\
    b = 0%nat /\ RFb g fr b (RID (g_in g) b) (RFG (g_in g) b) phi regs m /\ a0v regs (mrow (g_in g)) /\
    spill regs m 112 (mrow (g_in g)) /\ spill regs m 8 (mrow (g_in g) + 16) /\
    spill regs m 0 (mrow (g_in g) + 20) /\ spill regs m 200 (decl_slot fr) /\
    addressable m (fr + 2528) 12 /\
    spill regs m 128 (fr + 544) /\ (* R21 latch 0x81950 ld a0,128(s1); Inv_A815cc_at *)
    PRO g fr regs m /\ spill regs m 104 0x21140 /\ spill regs m 96 0x1234 /\ (* Inv_A815cc_at; PRO: push 13B *)
    spill regs m 64 0xe38f0000 /\ (* Inv_A815cc_at (push 5b): the magic word, no B3 store to [s1+64] *)
    rg regs 21 (fr + 2176) /\ (* R21 tail: s5 = the id record, 0x81990 lbu a0,2(s5) .. 0x81aac addi a0,s5,3 *)
    spill regs m 144 (fr + 2688) /\ (* R21 tail 0x81994 ld s11,144(s1) *)
    spill regs m 192 (fr + 2768) /\ (* R21 b = 6 tail -> Inv_A81ac0 / Inv_A81ac8: [A + 208] (push 7) *)
    (exists idb, rw_cells rsegs m (fr + 2688) [CB 38 idb]) /\ (exists junk, rw_cells rsegs m (fr + 2768) [CB 72 junk]) /\
    spill regs m 280 (fr + 3040) /\ spill regs m 240 (fr + 3056) /\ (* P5 entry Inv_A81b90 via R21's b = 6 tail (push 9) *)
    (exists jy, rw_cells rsegs m (fr + 3040) [CB 1 jy]) /\ (exists junk, rw_cells rsegs m (fr + 3056) [CB 32 junk]) /\
    spill regs m 152 (Sfr fr + 68) /\ (* R21 exit: 0x81b08 ld a0,152(s1); Inv_A815cc_at *)
    addressable m (fr + 2176) 38 /\ (* R21 tail: the strcmp wrapper's range at a0 = s5 + 3 (0x81a64) *)
    (* push 13B: our[]'s 6 bytes addressable is in PRO *)
    RXS g fr regs m (* push 10: loop-carried to Inv_A815cc_at (S b) *)) c.
Definition Inv_A8183c (g : ghost) (c : config) : Prop := exists b, Inv_A8183c_at g b c.
(* R18 (0x81800): after reac_ports_parse; the two port words at fr + 2528 / fr + 2532, s11 = phi + 18, a0 = 0. *)
Definition Inv_A81858_at (g : ghost) (b : nat) (c : config) : Prop :=
  exists phi, CUTST g 0x81858 (hb1 phi (rnb g b)) (fun fr regs m =>
    (g_n g < 2 ^ 26 /\ (b <= 6)%nat /\ HB m phi (rnb g b) /\ rg regs 23 (Z.of_nat b) /\ OURb g fr m /\ OUTA fr m /\
     CUR g 7 regs /\ spill regs m 200 (decl_slot fr)) /\
    b = 0%nat /\ RFb g fr b (RID (g_in g) b) (RFG (g_in g) b) phi regs m /\ rg regs 27 (phi + 18) /\
    a0v regs 0 /\
    u32 m (fr + 2528) (4 * RcLeaf.n_in (rt_pbs (g_in g))) /\
    u32 m (fr + 2532) (4 * RcLeaf.n_out (rt_pbs (g_in g))) /\
    spill regs m 216 (fr + 2528) /\ spill regs m 8 (mrow (g_in g) + 16) /\
    spill regs m 0 (mrow (g_in g) + 20) /\ spill regs m 112 (mrow (g_in g)) /\
    spill regs m 128 (fr + 544) /\ (* R21 latch 0x81950 ld a0,128(s1); Inv_A815cc_at *)
    PRO g fr regs m /\ spill regs m 104 0x21140 /\ spill regs m 96 0x1234 /\ (* Inv_A815cc_at; PRO: push 13B *)
    spill regs m 64 0xe38f0000 /\ (* Inv_A815cc_at (push 5b): the magic word, no B3 store to [s1+64] *)
    rg regs 21 (fr + 2176) /\ (* R21 tail: s5 = the id record, 0x81990 lbu a0,2(s5) .. 0x81aac addi a0,s5,3 *)
    spill regs m 144 (fr + 2688) /\ (* R21 tail 0x81994 ld s11,144(s1) *)
    spill regs m 192 (fr + 2768) /\ (* R21 b = 6 tail -> Inv_A81ac0 / Inv_A81ac8: [A + 208] (push 7) *)
    (exists idb, rw_cells rsegs m (fr + 2688) [CB 38 idb]) /\ (exists junk, rw_cells rsegs m (fr + 2768) [CB 72 junk]) /\
    spill regs m 280 (fr + 3040) /\ spill regs m 240 (fr + 3056) /\ (* P5 entry Inv_A81b90 via R21's b = 6 tail (push 9) *)
    (exists jy, rw_cells rsegs m (fr + 3040) [CB 1 jy]) /\ (exists junk, rw_cells rsegs m (fr + 3056) [CB 32 junk]) /\
    spill regs m 152 (Sfr fr + 68) /\ (* R21 exit: 0x81b08 ld a0,152(s1); Inv_A815cc_at *)
    addressable m (fr + 2176) 38 /\ (* R21 tail: the strcmp wrapper's range at a0 = s5 + 3 (0x81a64) *)
    (* push 13B: our[]'s 6 bytes addressable is in PRO *)
    RXS g fr regs m (* push 10: loop-carried to Inv_A815cc_at (S b) *)) c.
Definition Inv_A81858 (g : ghost) (c : config) : Prop := exists b, Inv_A81858_at g b c.
(* R19 (0x81878): after declaration_of; a0 = vd <> 0 as a 64-bit word, the 32 declaration bytes addressable.
   (This cut has no OURb of its own, it is inside RFb, so OUTA follows RFb.) *)
Definition Inv_A818d0_at (g : ghost) (b : nat) (c : config) : Prop :=
  exists phi vd, CUTST g 0x818d0 (hb1 phi (rnb g b)) (fun fr regs m =>
    (g_n g < 2 ^ 26 /\ RFb g fr b (RID (g_in g) b) (RFG (g_in g) b) phi regs m /\ OUTA fr m /\ rg regs 10 vd /\
     vd <> 0 /\ rg regs 27 (phi + 18) /\ rg regs 18 (decl_slot fr) /\
     bytes_at rsegs m (decl_slot fr) (RcDecl.decl (rt_mb (g_in g)))) /\
    b = 0%nat /\ HB m phi (rnb g b) /\ 0 <= vd < 2 ^ 64 /\ length (RcDecl.decl (rt_mb (g_in g))) = 32%nat /\
    addressable m (decl_slot fr) 32 /\
    spill regs m 128 (fr + 544) /\ (* R21 latch 0x81950 ld a0,128(s1); Inv_A815cc_at *)
    PRO g fr regs m /\ spill regs m 104 0x21140 /\ spill regs m 96 0x1234 /\ (* Inv_A815cc_at; PRO: push 13B *)
    spill regs m 64 0xe38f0000 /\ (* Inv_A815cc_at (push 5b): the magic word, no B3 store to [s1+64] *)
    rg regs 21 (fr + 2176) /\ (* R21 tail: s5 = the id record, 0x81990 lbu a0,2(s5) .. 0x81aac addi a0,s5,3 *)
    spill regs m 112 (mrow (g_in g)) /\ (* R21 tail: row m, 0x819a0 .. 0x81a8c ld a0,112(s1) *)
    spill regs m 144 (fr + 2688) /\ (* R21 tail 0x81994 ld s11,144(s1) *)
    spill regs m 192 (fr + 2768) /\ (* R21 b = 6 tail -> Inv_A81ac0 / Inv_A81ac8: [A + 208] (push 7) *)
    (exists idb, rw_cells rsegs m (fr + 2688) [CB 38 idb]) /\ (exists junk, rw_cells rsegs m (fr + 2768) [CB 72 junk]) /\
    spill regs m 280 (fr + 3040) /\ spill regs m 240 (fr + 3056) /\ (* P5 entry Inv_A81b90 via R21's b = 6 tail (push 9) *)
    (exists jy, rw_cells rsegs m (fr + 3040) [CB 1 jy]) /\ (exists junk, rw_cells rsegs m (fr + 3056) [CB 32 junk]) /\
    spill regs m 152 (Sfr fr + 68) /\ (* R21 exit: 0x81b08 ld a0,152(s1); Inv_A815cc_at *)
    addressable m (fr + 2176) 38 /\ (* R21 tail: the strcmp wrapper's range at a0 = s5 + 3 (0x81a64) *)
    (* push 13B: our[]'s 6 bytes addressable is in PRO *)
    RXS g fr regs m (* push 10: loop-carried to Inv_A815cc_at (S b) *)) c.
Definition Inv_A818d0 (g : ghost) (c : config) : Prop := exists b, Inv_A818d0_at g b c.
(* R20 (0x81890): after the bcmp wrapper; a0 = 0, s8 = Phi_r is wrapper_free's argument. *)
Definition Inv_A818e8_at (g : ghost) (b : nat) (c : config) : Prop :=
  exists phi, CUTST g 0x818e8 (hb1 phi (rnb g b)) (fun fr regs m =>
    (g_n g < 2 ^ 26 /\ (b <= 6)%nat /\ HB m phi (rnb g b) /\ rg regs 23 (Z.of_nat b) /\ OURb g fr m /\ OUTA fr m /\
     CUR g 7 regs) /\
    b = 0%nat /\ RFb g fr b (RID (g_in g) b) (RFG (g_in g) b) phi regs m /\ a0v regs 0 /\
    spill regs m 128 (fr + 544) /\ (* R21 latch 0x81950 ld a0,128(s1); Inv_A815cc_at *)
    PRO g fr regs m /\ spill regs m 104 0x21140 /\ spill regs m 96 0x1234 /\ (* Inv_A815cc_at; PRO: push 13B *)
    spill regs m 64 0xe38f0000 /\ (* Inv_A815cc_at (push 5b): the magic word, no B3 store to [s1+64] *)
    rg regs 21 (fr + 2176) /\ (* R21 tail: s5 = the id record, 0x81990 lbu a0,2(s5) .. 0x81aac addi a0,s5,3 *)
    spill regs m 112 (mrow (g_in g)) /\ (* R21 tail: row m, 0x819a0 .. 0x81a8c ld a0,112(s1) *)
    spill regs m 144 (fr + 2688) /\ (* R21 tail 0x81994 ld s11,144(s1) *)
    spill regs m 192 (fr + 2768) /\ (* R21 b = 6 tail -> Inv_A81ac0 / Inv_A81ac8: [A + 208] (push 7) *)
    (exists idb, rw_cells rsegs m (fr + 2688) [CB 38 idb]) /\ (exists junk, rw_cells rsegs m (fr + 2768) [CB 72 junk]) /\
    spill regs m 280 (fr + 3040) /\ spill regs m 240 (fr + 3056) /\ (* P5 entry Inv_A81b90 via R21's b = 6 tail (push 9) *)
    (exists jy, rw_cells rsegs m (fr + 3040) [CB 1 jy]) /\ (exists junk, rw_cells rsegs m (fr + 3056) [CB 32 junk]) /\
    spill regs m 152 (Sfr fr + 68) /\ (* R21 exit: 0x81b08 ld a0,152(s1); Inv_A815cc_at *)
    addressable m (fr + 2176) 38 /\ (* R21 tail: the strcmp wrapper's range at a0 = s5 + 3 (0x81a64) *)
    (* push 13B: our[]'s 6 bytes addressable is in PRO *)
    RXS g fr regs m (* push 10: loop-carried to Inv_A815cc_at (S b) *)) c.
Definition Inv_A818e8 (g : ghost) (c : config) : Prop := exists b, Inv_A818e8_at g b c.
(* R21 (0x818cc): after wrapper_free; the turn-(S b) records feed the latch into Inv_A815cc at turn S b (b + 1 <= 6
   on the latch, CUR, OURb, s7 = b and the id / frag bytes of turn S b give its RS; IDBr feeds the 0x81938 ..
   0x81a64 tail compares). *)
Definition Inv_A81924_at (g : ghost) (b : nat) (c : config) : Prop :=
  CUTST g 0x81924 [] (fun fr regs m =>
    g_n g < 2 ^ 26 /\ (b <= 6)%nat /\ rg regs 23 (Z.of_nat b) /\ OURb g fr m /\ OUTA fr m /\
    RB g fr b (RID (g_in g) (S b)) (RFG (g_in g) (S b)) regs m /\
    spill regs m 128 (fr + 544) /\ (* R21 latch 0x81950 ld a0,128(s1); Inv_A815cc_at *)
    PRO g fr regs m /\ spill regs m 104 0x21140 /\ spill regs m 96 0x1234 /\ (* Inv_A815cc_at; PRO: push 13B *)
    spill regs m 64 0xe38f0000 /\ (* Inv_A815cc_at (push 5b): the magic word, no B3 store to [s1+64] *)
    rg regs 21 (fr + 2176) /\ (* R21 tail: s5 = the id record, 0x81990 lbu a0,2(s5) .. 0x81aac addi a0,s5,3 *)
    spill regs m 112 (mrow (g_in g)) /\ (* R21 tail: row m, 0x819a0 .. 0x81a8c ld a0,112(s1) *)
    spill regs m 144 (fr + 2688) /\ (* R21 tail 0x81994 ld s11,144(s1) *)
    spill regs m 192 (fr + 2768) /\ (* R21 b = 6 tail -> Inv_A81ac0 / Inv_A81ac8: [A + 208] (push 7) *)
    (exists idb, rw_cells rsegs m (fr + 2688) [CB 38 idb]) /\ (exists junk, rw_cells rsegs m (fr + 2768) [CB 72 junk]) /\
    spill regs m 280 (fr + 3040) /\ spill regs m 240 (fr + 3056) /\ (* P5 entry Inv_A81b90 via R21's b = 6 tail (push 9) *)
    (exists jy, rw_cells rsegs m (fr + 3040) [CB 1 jy]) /\ (exists junk, rw_cells rsegs m (fr + 3056) [CB 32 junk]) /\
    spill regs m 152 (Sfr fr + 68) /\ (* R21 exit: 0x81b08 ld a0,152(s1); Inv_A815cc_at *)
    addressable m (fr + 2176) 38 /\ (* R21 tail: the strcmp wrapper's range at a0 = s5 + 3 (0x81a64) *)
    (* push 13B: our[]'s 6 bytes addressable is in PRO *)
    RXS g fr regs m (* push 10: loop-carried to Inv_A815cc_at (S b) *)) c.
Definition Inv_A81924 (g : ghost) (c : config) : Prop := exists b, Inv_A81924_at g b c.

(* ---- Init and P8 (P1-P12). P1 (0x81a68) re-poisons out[]; P2 (0x81ab8) is the init join. P3-P12 ~ P01-P09.
   Bodies from a Theorem Labs lane's cut-*.v (seg_P1..seg_P6 Qed on five working branches) and
   from a Theorem Labs lane's cutreq/p7-p10.md (a working note, not in this delivery) (seg_P7..seg_P10 Qed, a working branch 1aed2cac83). Every body drops
   mem_inv (push 5d) and the facts FRA / fra_frame / fra_win / fra_app / fra_call_pre carry: `aspZ <= APPMEM_END`
   (FRA's sp <= A <= S < APPMEM_END), the frame-vs-callee-window disjunction, `fr + 3040 <= A`, the FakeStack
   metadata bound and the callee window's addressability. The a3 bodies are stated as CUTST (they were raw
   existentials over FRA before push 5c, which has no ENT): their own conjuncts are unchanged. *)
(* P1 entry (0x81a68) and a Theorem Labs lane's NEW cut 0x81a70 (R21's `beqz a0,81a70` at 0x81a24 skips 0x81a68), a Theorem Labs lane's cut-P1.v (not in this delivery)
   text at both pcs. Push 7 (a Theorem Labs lane 23:48Z): these two cuts and P2's Inv_A81b10 also carry what Inv_A81b14
   reads and P1 / P2 do not write: s11 = fr + 2688 (R21's 0x81994 `ld s11,144(s1)`), the spill [A + 208] =
   fr + 2768 as a readable and writable cell, and the two frame records at fr + 2688 (38 bytes) and fr + 2768
   (72 bytes) readable and writable, in Inv_A81b14's own form; R21's b = 6 tail produces them from the B3 cuts'
   spills 144 / 208 and record cells.
   Push 9 (a Theorem Labs lane, P4 lane): these three cuts, Inv_A81b14 and Inv_A81b80 also carry what P5's entry Inv_A81b90
   reads and P1 .. P4 do not write: [A + 280] = fr + 2960, [A + 240] = fr + 2976 (A4's 0x81388 / 0x81390) and the
   1-byte code cell at fr + 2960 and the 32-byte scratch at fr + 2976 readable and writable; Inv_A81b80 also pins
   P4's memset target D = fr + 2768, so the memset's [D, D + 72) misses both. R21's b = 6 tail produces them from
   the B3 cuts' spills 280 / 240 and cells.
   Push 11 group A (a Theorem Labs lane's gap 4, cut-gap4-81bf8.md (a working note, not in this delivery), for P12's entry Inv_A81c84): right after `OURb g fr m`,
   - `CUR g (c0 (g_in g)) regs` (s6 = p + c0, s9 = n - c0) on Inv_A81ac0 .. Inv_A81c84. Producers: R21's b = 6 tail
     into 0x81a68 / 0x81a70 (the round trip carries CUR g 7, whose range 7 <= g_n g gives c0 (g_in g) = 7); R1's
     three exits into 0x81abc: 0x813e8 (n < 6, input used up: s6 = p + n from 0x813a8, s9 = 0 from 0x813d0, c0 = n),
     0x8198c (n = 6: 0x814a4 `beqz s8` -> 0x81984 `li s9,0` / 0x81988 `mv s6,s7`, c0 = 6) and 0x814cc (n >= 7, mode
     even: s6 = p + 7 from 0x81470, s9 = n - 7 from 0x81468, c0 = 7). P1 .. P11 write neither s6 nor s9.
   - `IDBe g fr RcIdentModel.ID0 m` on Inv_A81b80 .. Inv_A81c84: made by P3 (reac_identity_init at 0x81afc writes 38
     zero bytes at s11 = fr + 2688).
   - `FGBe g fr z72 m` on Inv_A81b90 .. Inv_A81c84: made by P4 (checked_memset at 0x81b0c writes 72 zero bytes at
     [A + 208] = fr + 2768).
   - Inv_A81c84 is P11.v's Inv_A81bf8_loc (a0 = QMARK, the kind-name strings, QMARK's two bytes addressable, XC)
     plus the three. Vacuity: CUR's range 0 <= c0 (g_in g) <= g_n g holds for every ghost (g_n_len), its register
     parts are equalities; IDBe / FGBe are bytes_at of closed lists; no new conjunct is under a quantifier. *)
(* Push 12 group A (a Theorem Labs lane's cutreq-826a4-and-flsh.md item 1 (a working note, not in this delivery), for X1's entry Inv_A82b04 and the frame loop):
   `spill regs m 144 (fr + 2688)` on Inv_A81ac0 .. Inv_A81c84 and `addressable m (fr + 2691) 17` on Inv_A81b80 ..
   Inv_A81c84, both also in FLSH (so every frame-loop cut from the head 0x81ca8 on has them). Producers: the spill
   is A4's 0x813f0 `sd s11,144(s1)`, the only store to [s1 + 144] in the function (push 7A made it exact on A5 ..
   R21), so R21's b = 6 tail gives it at 0x81a68 / 0x81a70 and R1's exits at 0x81abc from the chain; the 17 bytes
   are addressable from P3's own shadow stores 0x81b14 .. 0x81b20 (`sb zero,336(s3)` .. `sb zero,339(s3)` cover
   fr + 2688 .. fr + 2719), re-poisoned only at 0x82aac, after the frame loop, so P4 onward and every frame-loop
   cut keep them. Consumers: X1 (Inv_A82b04's `ld a1,144(s1)` and the memchr over [fr + 2691, fr + 2708)), the
   pre-loop exit 0x81c54 `beqz s9,82a58`, and F38's two exits into 0x82a58. *)
Definition Inv_A81ac0 (g : ghost) (c : config) : Prop :=
  CUTST g 0x81ac0 [] (fun fr regs m => g_n g < 2 ^ 26 /\ OURb g fr m /\ CUR g (c0 (g_in g)) regs /\
    PRO g fr regs m /\ spill regs m 144 (fr + 2688) /\ a0v regs 0 /\
    (exists Q, spill regs m 152 Q /\ Sfr fr <= Q /\ Q + 187 <= Sfr fr + 328) /\
    (exists (A : Z) (idb junk : list byte),
       getr regs 9 = Z_to_bv 64 A /\ rg regs 27 (fr + 2688) /\ 0 <= A < 2 ^ 64 /\
       rw_cells rsegs m (A + 192) [C8 (Z_to_bv 64 (fr + 2768))] /\
       rw_cells rsegs m (fr + 2688) [CB 38 idb] /\
       rw_cells rsegs m (fr + 2768) [CB 72 junk] /\
       q64 m (A + 280) (fr + 3040) /\ q64 m (A + 240) (fr + 3056) /\
       (exists jy junk2 : list byte, rw_cells rsegs m (fr + 3040) [CB 1 jy] /\ rw_cells rsegs m (fr + 3056) [CB 32 junk2]))) c.
Definition Inv_A81ac8 (g : ghost) (c : config) : Prop :=
  CUTST g 0x81ac8 [] (fun fr regs m => g_n g < 2 ^ 26 /\ OURb g fr m /\ CUR g (c0 (g_in g)) regs /\
    PRO g fr regs m /\ spill regs m 144 (fr + 2688) /\ a0v regs 0 /\
    (exists Q, spill regs m 152 Q /\ Sfr fr <= Q /\ Q + 187 <= Sfr fr + 328) /\
    (exists (A : Z) (idb junk : list byte),
       getr regs 9 = Z_to_bv 64 A /\ rg regs 27 (fr + 2688) /\ 0 <= A < 2 ^ 64 /\
       rw_cells rsegs m (A + 192) [C8 (Z_to_bv 64 (fr + 2768))] /\
       rw_cells rsegs m (fr + 2688) [CB 38 idb] /\
       rw_cells rsegs m (fr + 2768) [CB 72 junk] /\
       q64 m (A + 280) (fr + 3040) /\ q64 m (A + 240) (fr + 3056) /\
       (exists jy junk2 : list byte, rw_cells rsegs m (fr + 3040) [CB 1 jy] /\ rw_cells rsegs m (fr + 3056) [CB 32 junk2]))) c.
Definition Inv_A81b10 (g : ghost) (c : config) : Prop :=
  CUTST g 0x81b10 [] (fun fr regs m => g_n g < 2 ^ 26 /\ OURb g fr m /\ CUR g (c0 (g_in g)) regs /\
    PRO g fr regs m /\ spill regs m 144 (fr + 2688) /\
    (exists (A : Z) (idb junk : list byte),
       getr regs 9 = Z_to_bv 64 A /\ rg regs 27 (fr + 2688) /\ 0 <= A < 2 ^ 64 /\
       rw_cells rsegs m (A + 192) [C8 (Z_to_bv 64 (fr + 2768))] /\
       rw_cells rsegs m (fr + 2688) [CB 38 idb] /\
       rw_cells rsegs m (fr + 2768) [CB 72 junk] /\
       q64 m (A + 280) (fr + 3040) /\ q64 m (A + 240) (fr + 3056) /\
       (exists jy junk2 : list byte, rw_cells rsegs m (fr + 3040) [CB 1 jy] /\ rw_cells rsegs m (fr + 3056) [CB 32 junk2]))) c.
(* P3 entry (0x81abc), a Theorem Labs lane's cut-P3_entry.v (not in this delivery): the identity-record init call's cells and its munch/wmono frame rule. *)
Definition Inv_A81b14 (g : ghost) (c : config) : Prop :=
  CUTST g 0x81b14 [] (fun fr regs m => g_n g < 2 ^ 26 /\ OURb g fr m /\ CUR g (c0 (g_in g)) regs /\
    PRO g fr regs m /\ spill regs m 144 (fr + 2688) /\
    exists (spv A : Z) (idb junk : list byte),
      getr regs 2 = Z_to_bv 64 spv /\ getr regs 9 = Z_to_bv 64 A /\ rg regs 27 (fr + 2688) /\
      0 <= A < 2 ^ 64 /\ 0 <= spv < 2 ^ 64 /\
      rw_cells rsegs m (A + 192) [C8 (Z_to_bv 64 (fr + 2768))] /\
      rw_cells rsegs m (fr + 2688) [CB 38 idb] /\
      rw_cells rsegs m (fr + 2768) [CB 72 junk] /\
      q64 m (A + 280) (fr + 3040) /\ q64 m (A + 240) (fr + 3056) /\
      (exists jy junk2 : list byte, rw_cells rsegs m (fr + 3040) [CB 1 jy] /\ rw_cells rsegs m (fr + 3056) [CB 32 junk2])) c.
(* P4 entry (0x81b00), a Theorem Labs lane's cut-P4_entry.v (not in this delivery): the __asan_memset call on the 72-byte fragment scratch D. Push 6c
   (a Theorem Labs lane's p5b-plan-B.md section 5 item 3 (a working note, not in this delivery)): the spill-base exclusion covers [A0 + 24, A0 + 40) (the fr reload
   spill [A + 24] and the selector spill [A + 32]; it had only [A0 + 32, A0 + 40)), because sl_fr_run /
   sl_fr_meta need `A + 24 <= x < A + 40` outside W; and both spill-base premises take `0 <= A0 < 2 ^ 64` first
   (vacuity gate). *)
(* v1.9 (P3's exit, P4's entry; P3 gains the NEW-only shadow stores 0x81b38 / 0x81b3c / 0x81b40 / 0x81b44 / 0x81b64:
   S(fr) + 353 / 354 / 360 / 361 = 0, S(fr) + 364 = 3, and 0x81b68 .. 0x81b74 `__asan_memset([A + 32] = fr + 2880, 0, 35)`):
   - `addressable m (fragb fr) 72` is kept (round 2, cut owner): frag is at fr + 2768 and 72 bytes long in both
     images (frame description, section 7a's variable table), so its shadow is S(fr) + 346 .. 354 in both; only the
     instructions that clear 353 / 354 moved, to P3's NEW-only 0x81b38 / 0x81b3c (v1.8 0x81af0 / 0x81af4 now write
     362 / 363, inside first.sroa.7). P3's re-walk proves the conjunct from the new stores.
   - The spill-base exclusion is renumbered to the two FRA spills [A0 + 16] (fr reload) and [A0 + 24] (selector);
     v1.9's [A0 + 32] = fr + 2880 (first.sroa.7's pointer, 0x813cc) is not in it and no conjunct names it.
   - `Sfr fr <= x < Sfr fr + FRAME_SHADOW` covers the new shadow bytes by range only (the memset window W misses
     the whole frame shadow); renumbered, not restated.
   - Round 4 (a Theorem Labs lane's gap, cut owner): this cut and the eight after it (Inv_A81b90 .. Inv_A81c84) carry, LAST,
     `addressable m (fr + 2880) 35`, which P12's exit Inv_A81d40_at g 0 needs through FSj g fr 0 = FSb (fs0), its
     position 4. P3's 0x81b40 / 0x81b44 / 0x81b5c / 0x81b60 / 0x81b64 make it (S(fr) + 360 .. 363 = 0,
     S(fr) + 364 = 3). No instruction of 0x81b80 .. 0x81d3c stores to S(fr) + 360 .. 364 (its shadow stores are
     S(fr) + 370 / 372 / 376 / 380 / 382 .. 385 at 0x81b98 .. 0x81bc0 and 0x81cc0 .. 0x81cdc; 0x81bb0 writes the app
     byte fr + 3040), and no callee of the range writes them: the two __asan_memset calls write only their data range
     and window (the W of this cut misses [Sfr fr, Sfr fr + FRAME_SHADOW)), the six program callees write their own
     window below sp, their side-stack slots and the shadow of those (apart from the frame's shadow by FRA's
     placement and fra_fp's fp_dj), and app output cells. *)
Definition Inv_A81b80 (g : ghost) (c : config) : Prop :=
  CUTST g 0x81b80 [] (fun fr regs m => g_n g < 2 ^ 26 /\ OURb g fr m /\ CUR g (c0 (g_in g)) regs /\
    PRO g fr regs m /\ spill regs m 144 (fr + 2688) /\ addressable m (fr + 2691) 17 /\
    addressable m (fragb fr) 72 /\ addressable m (fr + 2688) 38 /\
    IDBe g fr RcIdentModel.ID0 m /\
    exists (D spv A : Z) (junk : list byte),
      let W : list ivl := [(D, D + 72); (spv - asan_memset_c.ASAN_MEMSET_K, spv)] in
      getr regs 2 = Z_to_bv 64 spv /\ getr regs 9 = Z_to_bv 64 A /\
      0 <= A < 2 ^ 64 /\ 0 <= D < 2 ^ 64 /\ 0 <= spv < 2 ^ 64 /\
      rw_cells rsegs m (A + 192) [C8 (Z_to_bv 64 D)] /\
      rw_cells rsegs m D [CB 72 junk] /\ addressable m D 72 /\ end_in_app D 72 /\ app_mem (D + 7) /\
      (D + 72 <= RT_LO \/ RT_HI <= D) /\
      (D + 72 <= spv - asan_memset_c.ASAN_MEMSET_K \/ spv <= D) /\
      (forall x, 0 <= x < 6283264 -> Frame.outside W x) /\
      (forall x, fr <= x < fr + 24 -> Frame.outside W x) /\
      (forall A0, getr regs 9 = Z_to_bv 64 A0 -> 0 <= A0 < 2 ^ 64 ->
         forall x, A0 + 304 <= x < A0 + 312 -> Frame.outside W x) /\
      (forall A0, getr regs 9 = Z_to_bv 64 A0 -> 0 <= A0 < 2 ^ 64 ->
         forall x, A0 + 16 <= x < A0 + 32 -> Frame.outside W x) /\
      (forall x, g_S g - 104 <= x < g_S g -> Frame.outside W x) /\
      (forall x, Sfr fr <= x < Sfr fr + FRAME_SHADOW -> Frame.outside W x) /\
      (forall x, fr + 2624 <= x < fr + 2624 + Z.of_nat (length (OUR (g_in g))) -> Frame.outside W x) /\
      all_app W /\ rt_disjoint W /\
      D = fr + 2768 /\ q64 m (A + 280) (fr + 3040) /\ q64 m (A + 240) (fr + 3056) /\
      (exists jy junk2 : list byte, rw_cells rsegs m (fr + 3040) [CB 1 jy] /\ rw_cells rsegs m (fr + 3056) [CB 32 junk2]) /\
      addressable m (fr + 2880) 35) c.
(* P5 entry (0x81b10), a Theorem Labs lane's cut-P5_entry.v (not in this delivery): the second memset, on the 1-byte code cell and the 32-byte scratch. *)
Definition Inv_A81b90 (g : ghost) (c : config) : Prop :=
  CUTST g 0x81b90 [] (fun fr regs m => g_n g < 2 ^ 26 /\ OURb g fr m /\ CUR g (c0 (g_in g)) regs /\
    PRO g fr regs m /\ spill regs m 144 (fr + 2688) /\ addressable m (fr + 2691) 17 /\
    spill regs m 192 (fragb fr) /\ addressable m (fragb fr) 72 /\ addressable m (fr + 2688) 38 /\
    IDBe g fr RcIdentModel.ID0 m /\ FGBe g fr z72 m /\
    exists (A : Z) (jy junk : list byte),
      rg regs 9 A /\ 0 <= A /\ q64 m (A + 280) (fr + 3040) /\ q64 m (A + 240) (fr + 3056) /\
      rw_cells rsegs m (fr + 3040) [CB 1 jy] /\ rw_cells rsegs m (fr + 3056) [CB 32 junk] /\
      addressable m (fr + 2880) 35) c.
(* XC (a Theorem Labs lane's p7-p10.md (a working note, not in this delivery)): the [A + 280] = fr + 2960 code-byte pointer and that byte addressable, read by P10's
   reac_ports_unknown. a Theorem Labs lane's own mem_inv conjunct is dropped (push 5d). *)
Definition XC (fr : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  (forall A, rg regs 9 A -> 0 <= A < 2 ^ 64 -> q64 m (A + 280) (fr + 3040)) /\
  addressable m (fr + 3040) 1.
(* P6 entry (0x81b58), a Theorem Labs lane's cut-P6_entry.v (not in this delivery): the identity-reply call. The callee's side-stack package (fp [1] and
   reac_ctrl_identity_reply_tls) is on NO cut: FRA gives it at every cut (inv_a81bd8_pkg, from fra_fp of
   Seg/Tac_fsfree.v). The window / placement parts are dropped. Push 11 group E (a Theorem Labs lane's fsfree-A-diff.md (a working note, not in this delivery))
   drops the FS binder and the three package conjuncts; the group A conjuncts stay. *)
Definition Inv_A81bd8 (g : ghost) (c : config) : Prop :=
  CUTST g 0x81bd8 [] (fun fr regs m => g_n g < 2 ^ 26 /\ OURb g fr m /\ CUR g (c0 (g_in g)) regs /\
    PRO g fr regs m /\ spill regs m 144 (fr + 2688) /\ addressable m (fr + 2691) 17 /\
    spill regs m 192 (fragb fr) /\ addressable m (fragb fr) 72 /\ addressable m (fr + 2688) 38 /\
    IDBe g fr RcIdentModel.ID0 m /\ FGBe g fr z72 m /\ XC fr regs m /\
    exists (A pa pp f : Z),
      rg regs 9 A /\ 0 <= A < 2 ^ 64 /\ 0 <= pa < 2 ^ 64 /\ 0 <= pp < 2 ^ 64 /\
      q64 m (A + 232) pa /\ q64 m (A + 224) pp /\ q64 m (A + 192) f /\
      addressable m (AC.aspZ regs - reac_ctrl_identity_reply_c.REAC_CTRL_IDENTITY_REPLY_K) reac_ctrl_identity_reply_c.REAC_CTRL_IDENTITY_REPLY_K /\
      addressable m reac_ctrl_parse_c.REAC_CTRL_PARSE_BC 6 /\
      addressable m (fr + 2880) 35) c.
(* P7-P10 (0x81b78 .. 0x81bdc), a Theorem Labs lane's p7-p10.md (a working note, not in this delivery): each callee gets a null argument and returns -1. *)
Definition Inv_A81bf8 (g : ghost) (c : config) : Prop :=
  CUTST g 0x81bf8 [] (fun fr regs m => g_n g < 2 ^ 26 /\ OURb g fr m /\ CUR g (c0 (g_in g)) regs /\
    PRO g fr regs m /\ spill regs m 144 (fr + 2688) /\ addressable m (fr + 2691) 17 /\
    spill regs m 192 (fragb fr) /\ addressable m (fragb fr) 72 /\ addressable m (fr + 2688) 38 /\
    IDBe g fr RcIdentModel.ID0 m /\ FGBe g fr z72 m /\ a0v regs (-1) /\
    (exists f, spill regs m 192 f) /\ XC fr regs m /\ addressable m (fr + 2880) 35) c.
Definition Inv_A81c20 (g : ghost) (c : config) : Prop :=
  CUTST g 0x81c20 [] (fun fr regs m => g_n g < 2 ^ 26 /\ OURb g fr m /\ CUR g (c0 (g_in g)) regs /\
    PRO g fr regs m /\ spill regs m 144 (fr + 2688) /\ addressable m (fr + 2691) 17 /\
    spill regs m 192 (fragb fr) /\ addressable m (fragb fr) 72 /\ addressable m (fr + 2688) 38 /\
    IDBe g fr RcIdentModel.ID0 m /\ FGBe g fr z72 m /\ a0v regs (-1) /\
    rg regs 18 (-1) /\ XC fr regs m /\ addressable m (fr + 2880) 35) c.
Definition Inv_A81c34 (g : ghost) (c : config) : Prop :=
  CUTST g 0x81c34 [] (fun fr regs m => g_n g < 2 ^ 26 /\ OURb g fr m /\ CUR g (c0 (g_in g)) regs /\
    PRO g fr regs m /\ spill regs m 144 (fr + 2688) /\ addressable m (fr + 2691) 17 /\
    spill regs m 192 (fragb fr) /\ addressable m (fragb fr) 72 /\ addressable m (fr + 2688) 38 /\
    IDBe g fr RcIdentModel.ID0 m /\ FGBe g fr z72 m /\ a0v regs (-1) /\ XC fr regs m /\
    addressable m (fr + 2880) 35) c.
(* RE-ANCHORED (v1.9): v1.8's cut Inv_A81bcc stood on 0x81bcc `bne a0,s2,82b34`, which v1.9 replaces by the pair
   0x81c4c `beq a0,s2,81c54` / 0x81c50 `j 82bf4` (branch relaxation; 0x82bf4 is the image of the v1.8 error block
   0x82b34). The cut stands on 0x81c4c, the first instruction of the replacement. It is reached only by the
   fall-through of 0x81c48 `jal reac_ports_parse` (= v1.8 0x81bc8, EQUAL); no branch targets it in either image.
   So the state at 0x81c4c is v1.8's state at 0x81bcc under the renumbering, and every conjunct below holds there
   with its v1.8 meaning (none reads the replaced branch). S_P10's walk changes: a0 = s2 now branches to 0x81c54
   (= v1.8 0x81bd0) and a0 <> s2 falls to the `j`. *)
Definition Inv_A81c4c (g : ghost) (c : config) : Prop :=
  CUTST g 0x81c4c [] (fun fr regs m => g_n g < 2 ^ 26 /\ OURb g fr m /\ CUR g (c0 (g_in g)) regs /\
    PRO g fr regs m /\ spill regs m 144 (fr + 2688) /\ addressable m (fr + 2691) 17 /\
    spill regs m 192 (fragb fr) /\ addressable m (fragb fr) 72 /\ addressable m (fr + 2688) 38 /\
    IDBe g fr RcIdentModel.ID0 m /\ FGBe g fr z72 m /\ a0v regs (-1) /\
    rg regs 18 (-1) /\ XC fr regs m /\ addressable m (fr + 2880) 35) c.
Definition Inv_A81c60 (g : ghost) (c : config) : Prop :=
  CUTST g 0x81c60 [] (fun fr regs m => g_n g < 2 ^ 26 /\ OURb g fr m /\ CUR g (c0 (g_in g)) regs /\
    PRO g fr regs m /\ spill regs m 144 (fr + 2688) /\ addressable m (fr + 2691) 17 /\
    spill regs m 192 (fragb fr) /\ addressable m (fragb fr) 72 /\ addressable m (fr + 2688) 38 /\
    IDBe g fr RcIdentModel.ID0 m /\ FGBe g fr z72 m /\ a0v regs (-1) /\
    b8 m (fr + 3040) 0 /\ XC fr regs m /\ addressable m (fr + 2880) 35) c.
(* P12 entry (0x81bf8): P11.v's Inv_A81bf8_loc (a0 = QMARK = kind_name_addr 14, the kind-name strings, QMARK's two
   bytes addressable, XC) and the three gap-4 facts (push 11 group A, see P1). *)
Definition Inv_A81c84 (g : ghost) (c : config) : Prop :=
  CUTST g 0x81c84 [] (fun fr regs m => g_n g < 2 ^ 26 /\ OURb g fr m /\ a0v regs KNA.QMARK /\
    KNA.kind_name_strings m /\ addressable m KNA.QMARK 2 /\ XC fr regs m /\ CUR g (c0 (g_in g)) regs /\
    PRO g fr regs m /\ spill regs m 144 (fr + 2688) /\ addressable m (fr + 2691) 17 /\
    spill regs m 192 (fragb fr) /\ addressable m (fragb fr) 72 /\ addressable m (fr + 2688) 38 /\
    IDBe g fr RcIdentModel.ID0 m /\ FGBe g fr z72 m /\ addressable m (fr + 2880) 35) c.

(* ---- Frame loop (F1-F38), turn j : nat. F1 malloc gains Phi, F37 free drops it. Each cut carries the turn
   index j (j <= 255) and, on the malloc span, HB(Phi, len) (plan 3.4, FP.4, IC HB(Phi) rows).
   The live-block list is `hb1 phi (AC.a_size (flen g j))`, NOT `hb1 phi (flen g j)` (a Theorem Labs lane, seg_F1 Qed):
   malloc(0) returns the block (q, a_size 0) = (q, 1), so AH over a list holding (q, 0) fails on the len = 0
   path. HB already has a_size inside, so only the heap list changes. *)
Definition flen (g : ghost) (j : nat) : Z := t_len (g_in g) j.
(* F1 (a Theorem Labs lane's Seg/F1.v, a working branch b5a32896e10). The input block the allocation call keeps live, and the
   [A + 248] = fr + 176 prologue spill F2 / F3 read. a Theorem Labs lane's f1_WIN and f1_HI are DROPPED: fra_call_pre gives the
   callee window addressable and off the live blocks (AK_MALLOC = 4096 <= FN_STACK), and the three ENTRY
   stack-top facts are FRA's, moved to the cut's state by ENT. Push 6c (a Theorem Labs lane's p5b-plan-B.md section 5 item 1 (a working note, not in this delivery)):
   the live-block fact is guarded by 0 < n, as alib_pre gives it (for n = 0, p = empty is no block). *)
Definition f1_IN (g : ghost) (m : word -> option byte) : Prop :=
  (0 < g_n g -> In (g_p g, g_n g) (g_H g)) /\ addressable m (g_p g) (g_n g) /\ bytes_at rsegs m (g_p g) (g_in g).
(* f1_IN from PRO on the arm where the input block exists (push 13 group B): P12's loop-head exit has 0 < g_n g
   (0x81c54 `beqz s9,82a58` not taken, with CUR's s9 = n - c0 and 0 <= c0 <= n). *)
Lemma f1_IN_of_PRO : forall g fr regs m, 0 < g_n g -> PRO g fr regs m -> f1_IN g m.
Proof.
  intros g fr regs m Hn HP. unfold PRO in HP.
  destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hin & Hg & _).
  destruct (Hg Hn) as (HH & Had). unfold f1_IN. split; [intros _; exact HH|].
  split; [exact Had | exact Hin].
Qed.
(* ---- The frame-loop bundles (push 5b, a Theorem Labs lane decision, Option B; push 6c, a Theorem Labs lane's cutreq-flsi.md (a working note, not in this delivery)).

   FLSH is the loop-INVARIANT part every frame-loop cut carries, from the loop head 0x81ca8 on: the frame-pointer
   spills set once in the A4 / P prologue (0x812dc-0x812ec, 0x81304-0x8139c, 0x81c6c-0x81ca4) and never rewritten
   inside the frame loop, plus out[]'s six bytes addressable and the frame body byte-backed (`stk fr (fr + 3040)`,
   a Theorem Labs lane: loop-invariant because the frame body is written only through stores that keep stk).

   FLSI is FLSH plus four facts a Theorem Labs lane asks for (the latch F38 reads [A+216] at 0x8289c and [A+224] at 0x828a4, and
   hands [A+248] and f1_IN to the loop head of turn j + 1): [A+216] = p + body_j, [A+224] = left_j - h_j, the
   prologue spill [A+248] = fr + 176 (0x812f4, never rewritten) and the harness block f1_IN (never written in the
   loop). FLSI is the bundle of the FCUT skeleton (every frame-loop cut from F2, 0x81d38, on). It is NOT on the loop
   head 0x81d40 or on F1's 0x81da4: [A+224] is written each turn at 0x81d98 and [A+216] at 0x81db4 (`sd s9,224(s1)`
   / `sd s4,216(s1)`; the only other stores to them are the prologue's 0x813a4 / 0x81358), so at the loop head
   they hold the previous turn's values; those two cuts carry FLSH and name [A+248] / f1_IN themselves (0x81d0c
   has [A+224] in FC). a Theorem Labs lane's fifth fact, IFS g fr (S j) (the next turn's frame records), is NOT in FLSI: it holds
   only once turn j has written those records (F15-F17), so the early cuts' producers cannot give it; it is the
   bundle LT of the F29-F38 bodies below.

   FLS is FLSI plus the TURN-dependent part (a Theorem Labs lane 06:52Z and a Theorem Labs lane 06:50Z / 07:11Z): registers 18/22/23/24/25, the
   record bytes at phi, and the two per-turn spills [A+152] = tfill and [A+280] = sum_ok. Those hold only from
   0x826a4 (F28's exit, which loads s9 = [A+176] = fr + 64) through F38: at the F2-F28 cuts s9 and s8 hold other
   values (a Theorem Labs lane's B7Cuts.v (a version not in this delivery) sets s9 = fr + 64 only at 0x826a4, and its 0x82548 / 0x82558 bodies have s9 = t_rp),
   the two per-turn spills still hold turn j - 1 (F5 writes them at 0x81df8-0x81eb4), and the short-frame arm has
   flen j < 50 (a Theorem Labs lane's F5ST). FLS's `rg regs 24 (t_k (g_in g) j)` is false from 0x8285c on (0x8284c `ld s8,40(s1)`,
   then 0x827b4 / 0x82804; a Theorem Labs lane): FLS holds up to 0x8281c, FLSX (FLS without it) from 0x827b0 on, FLSF (FLSX
   without the freed block's bytes) at 0x82894 after the free.

   Dropped from all of them, because FRA and its lemmas already carry them: mem_inv (push 5d), the
   frame-vs-callee-window placement (fra_frame), `AC.GT <= fr` and the frame in app memory (fra_app), the FakeStack
   metadata bound (fra_frame), and `addressable REAC_CTRL_PARSE_BC 6` (FRA's frame_AG conjunct:
   REAC_CTRL_PARSE_BC = 0x211e0 is the frame_AG entry (0x211e0, 7)).
   Push 12 group A (a Theorem Labs lane): FLSH also carries [A + 144] = fr + 2688 (A4's 0x81398, the only store to that
   spill) and the 17 bytes at fr + 2691 addressable (P3's shadow stores 0x81abc .. 0x81ac8, re-poisoned only at
   0x82aac): X1's entry Inv_A82b04 reads both, and the P chain hands them to the loop head (see P1). *)
Definition FLSH (g : ghost) (j : nat) (fr : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  (* push 13 group B: FLSH is PRO (the A4 prologue facts, which the P chain hands to the loop head) plus the loop
     part. The regrouping keeps every former conjunct (PRO has all eight spills and our[]'s 6 bytes) and adds
     [A + 248] = fr + 176 and the input pair, which FLSI / Inv_A81d40_at / Inv_A81da4_at carry next to FLSH
     anyway. `stk rsegs m fr (fr + 3040)` stays in the loop part (fra_stk gives it from FRA at any cut). *)
  PRO g fr regs m /\
  spill regs m 128 (fr + 452) /\ stk rsegs m fr (fr + FRAME_BYTES) /\
  spill regs m 144 (fr + 2688) /\ addressable m (fr + 2691) 17.
(* FLC (push 14 group D, the F1-F3 lane's C5 result, Seg/F1.v / F2.v on a working branch fc681b5ab1d): the
   frame-loop pointer spills and the two record ranges, set before the loop and written by no instruction of the
   loop body 0x81ca8 .. 0x828b0 and by no callee there (the loop's inline stores to [s1 + ...] are offsets
   224 / 216 / 232 / 192 / 240 / 280 / 152 / 112 / 96 / 104 / 88 only; no store to S(fr) + 336 .. 354; s1 and s3
   are never written; callee write sets are windows below sp, frame data cells, heap blocks and their shadow, and
   the side stack). Setters: [A + 256] / [A + 184] / [A + 272] / [A + 264] A4's 0x812fc / 0x81314 / 0x81304 /
   0x8130c (carried by PRO), [A + 208] A4's 0x81374, [A + 80] / [A + 72] / [A + 64] P12's 0x81c74 / 0x81c7c /
   0x81c84 (from [A + 208]), the 72 bytes at fragb fr P3's 0x81ad0 .. 0x81af4 (S(fr) + 346 .. 354 cleared), the
   38 bytes at fr + 2688 P3's 0x81abc .. 0x81ac8 and 0x81ae0 (S(fr) + 336 .. 339 = 0, S(fr) + 340 = 6). FLC is in
   FLSI (so every frame-loop cut from 0x81d38 on carries it and F38's latch gives it at Inv_A81d40_at (S j)) and
   on Inv_A81d40_at / Inv_A81da4_at, which carry FLSH but not FLSI.
   Push 14 group E (the F1-F3 lane): FLC also carries the two compare-operand spills [A + 56] = fr + 186 and
   [A + 48] = fr + 180, P12's 0x81c88 .. 0x81c90 / 0x81c94 .. 0x81c98 (from [A + 248] = fr + 176). They are made
   inside P12, so the first cut that has them is the loop head (P12 produces them at Inv_A81d40_at g 0; before P12
   [A + 48] / [A + 56] hold the round trip's fr + 2256 / fr + 2368, so no P cut carries them), and no instruction of
   0x81ca8 .. 0x828b0 stores to [s1 + 48 / 56].
   v1.9: the slots are renumbered per the table's section 7a ([A+208/80/72/64/56/48] -> [A+192/96/88/80/72/64];
   v1.9 P12's NEW-only 0x81d2c .. 0x81d3c put first.sroa.7 + 9 / + 10 into [A+56] / [A+48], which FLC now names:
   they are made in P12 like fr + 186 / fr + 180 (before P12, [A+48] / [A+56] hold the round trip's fr + 2256 /
   fr + 2368, stored 0x814e0 / 0x814dc), and no instruction of 0x81d40 .. 0x82b00 stores to [s1 + 48 / 56], so the
   loop head is again the first cut that has them. They are NOT in PRO for that reason; [A+32] = fr + 2880 is, its
   only store being A4's 0x813cc. `addressable m (fragb fr) 72` is kept, see Inv_A81b80. *)
Definition FLC (fr : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  spill regs m 256 (fr + 256) /\ spill regs m 184 (fr + 336) /\ spill regs m 192 (fragb fr) /\
  spill regs m 80 (fragb fr + 15) /\ spill regs m 88 (fragb fr + 19) /\ spill regs m 96 (fragb fr + 8) /\
  spill regs m 272 (fr + 272) /\ spill regs m 264 (fr + 304) /\
  addressable m (fragb fr) 72 /\ addressable m (fr + 2688) 38 /\
  spill regs m 72 (fr + 186) /\ spill regs m 64 (fr + 180) /\
  spill regs m 56 (fr + 2889) /\ spill regs m 48 (fr + 2890).
Definition FLSI (g : ghost) (j : nat) (fr : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  FLSH g j fr regs m /\
  spill regs m 216 (g_p g + t_body (g_in g) j) /\ spill regs m 224 (t_left (g_in g) j - t_h (g_in g) j) /\
  spill regs m 248 (fr + 176) /\ f1_IN g m /\ FLC fr regs m.
(* Short-arm guard (push 6c5b, a Theorem Labs lane via a Theorem Labs lane 00:24Z): the record part of FLS / FLSX / FLSF (phi in
   range, the record bytes at phi, 50 <= len_j) holds only on the long arm. The short arm (len_j <= 49, and
   len_j = 0) reaches the F29-F38 cuts too: 0x81e08 `bgeu a0,s2` (a0 = 49) jumps to 0x81e88, which stores
   [A+240] = 0 at 0x81e94; nothing rewrites [A+240], so 0x823e8 `ld a0,240(s1); beqz a0,8275c` jumps to 0x8275c.
   (So does the long arm whose record is not 0x88 0x19: 0x81e0c stores [A+240] = 0.) So that part is under
   `50 <= flen g j ->`; s6 is already `if t_big then phi + 18 else 0` (0x81df4 `li s6,0` on the short arm). *)
Definition FLS (g : ghost) (j : nat) (phi fr : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  FLSI g j fr regs m /\
  rg regs 18 (flen g j) /\ rg regs 22 (if t_big (g_in g) j then phi + 18 else 0) /\ rg regs 23 phi /\
  rg regs 24 (t_k (g_in g) j) /\ rg regs 25 (fr + 64) /\
  (50 <= flen g j ->
     0 < phi /\ phi + 50 <= 2 ^ 64 /\
     bytes_at rsegs m phi (t_g (g_in g) j) /\
     bytes_at rsegs m phi (t_phi (g_in g) j) /\
     Z.of_nat (length (t_phi (g_in g) j)) <= flen g j) /\
  spill regs m 152 (b2z (t_tfill (g_in g) j)) /\
  spill regs m 280 (b2z (t_sum_ok (g_in g) j)).
(* FLSX (a Theorem Labs lane's Seg/B8Cuts.v (not in this delivery), a working branch 4eed0e3747c): FLS without `rg regs 24 (t_k (g_in g) j)`.
   Every other conjunct of FLS holds at every pc of F29-F38: register 18 (s2 = len_j) is written next at 0x828a0,
   register 22 (s6 = Phi + 18) at 0x828a0, registers 23 (s7 = Phi) and 25 (s9 = fr + 64) are not written before
   0x828a8, the bytes at Phi are written by no store of the batch (every store is `sb s11,N(s3)` into the frame's
   shadow, `sw a0,0(a4)` into fr + 528 or `sd zero,0(s8)` into fr + 32) and by no callee (each writes its own frame
   and its out parameter), and the two per-turn spills [A+152] / [A+280] are written only at 0x81df8-0x81eb4 of
   turn j. The record part is guarded as in FLS. *)
Definition FLSX (g : ghost) (j : nat) (phi fr : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  FLSI g j fr regs m /\
  rg regs 18 (flen g j) /\ rg regs 22 (if t_big (g_in g) j then phi + 18 else 0) /\ rg regs 23 phi /\
  rg regs 25 (fr + 64) /\
  (50 <= flen g j ->
     0 < phi /\ phi + 50 <= 2 ^ 64 /\
     bytes_at rsegs m phi (t_g (g_in g) j) /\
     bytes_at rsegs m phi (t_phi (g_in g) j) /\
     Z.of_nat (length (t_phi (g_in g) j)) <= flen g j) /\
  spill regs m 152 (b2z (t_tfill (g_in g) j)) /\
  spill regs m 280 (b2z (t_sum_ok (g_in g) j)).
Lemma flsx_of_fls : forall g j phi fr regs m, FLS g j phi fr regs m -> FLSX g j phi fr regs m.
Proof.
  intros g j phi fr regs m (HI & H18 & H22 & H23 & H24 & H25 & Hrec & H152 & H280).
  unfold FLSX. tauto.
Qed.
(* FLSF (a Theorem Labs lane): what the free at 0x82890 keeps of FLSX: the block's bytes and HB are gone (the block was
   released), the registers and the spills stay (the wrapper saves and restores the callee-saved registers and
   writes only its own frame and the released block's shadow). The phi range is guarded as in FLS. *)
Definition FLSF (g : ghost) (j : nat) (phi fr : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  FLSI g j fr regs m /\
  rg regs 18 (flen g j) /\ rg regs 22 (if t_big (g_in g) j then phi + 18 else 0) /\ rg regs 23 phi /\
  rg regs 25 (fr + 64) /\
  (50 <= flen g j -> 0 < phi /\ phi + 50 <= 2 ^ 64) /\
  spill regs m 152 (b2z (t_tfill (g_in g) j)) /\
  spill regs m 280 (b2z (t_sum_ok (g_in g) j)).
(* RL (a Theorem Labs lane): the state of one turn of the row loop W00 (head 0x827c0, back branch 0x8280c), row i of the
   catalogue: s4 = the row pointer (0x8287c `mv a0,s4`, 0x828b4 `addi s4,s4,296`), s8 = the rows left (0x828b8
   `bnez s8`, 0x828b0 `addi s8,s8,-1`), and the rows before i did not match the block (the loop's result is read as
   t_want_m at 0x828b8 / 0x82810). `t_rowsel = true` is the path fact of the whole row arm: 0x82758 took
   `bne s8,a0` not taken (kind 9) and 0x82778 / 0x82798 found the bytes cd / ea. *)
Definition RL (g : ghost) (j i : nat) (phi fr : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  (i <= 10)%nat /\ rg regs 20 (CAT + CAT_ROW * Z.of_nat i) /\ rg regs 24 (CAT_N - Z.of_nat i) /\
  (forall i', (i' < i)%nat -> t_blk (g_in g) j <> decl_i (Z.of_nat i')) /\
  t_rowsel (g_in g) j = true /\ FLSX g j phi fr regs m.
(* LT (a Theorem Labs lane): the facts of turn j's tail that every F29-F38 body hands on unchanged and that F38 gives to the
   loop-head cut of turn j + 1. a Theorem Labs lane's LT also had [A+216], [A+224], f1_IN and [A+248]; push 6c moved those four
   into FLSI (see above), so LT is the one fact FLSI cannot carry: IFS g fr (S j), the frame records at fr + 2688 /
   fr + 2768 and the first-fragment spills [A+88] .. [A+112] of turn j + 1, which Inv_A81d40_at (S j) asks for.
   The stores of the batch write the frame's shadow, fr + 32 and fr + 528, and its callees write their own stack
   and their outputs at fr + 32, fr + 64 .. fr + 95, fr + 448 .. fr + 483; none of these meets IFS's bytes. *)
Definition LT (g : ghost) (fr : Z) (j : nat) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  IFS g fr (S j) regs m.
(* ---- Push 12 group B (a Theorem Labs lane's ifs-design.md (a working note, not in this delivery), for LT at 0x826a4 / 0x826b0 and the latch into the loop head
   of turn S j). LT = IFS g fr (S j) was on no cut before 0x826a4 and no cut carried what a producer needs. The
   model (SlotModel.v turn / fst_at): t_FG (S j) = t_FGf j, t_ID (S j) = fg_id (ID1 g j) len (t_FG j) (t_g j) with
   ID1 g j = rp_id (t_ID j) len (t_g j), and the four first-fragment spills change exactly when f_opens len (t_g j).
   Each model function is the identity when its guard is false, so one text per pc covers the short arm, the
   8819-false arm and the long arm. The stages (see the doc for the producer table):
     stage 1, 0x81ca8 .. 0x82014: identity t_ID j, fragment t_FG j, spills of turn j      = IFS g fr j
     stage 2, 0x82060 / 0x82064 / 0x820a0: identity ID1 (the reply ingest at 0x8205c ran, or ir = false)  = IFS1
     stage 3, 0x820bc .. 0x82134: fragment t_FG (S j) (F13's call at 0x820b8 wrote it)                    = IFS2
     stage 4, 0x821c0 / 0x821c4: identity t_ID (S j) (F16's ingest at 0x821bc ran, or t_rf j <> 1)        = IFS3
     stage 5, 0x8233c on: the spills of turn S j (F17's 0x82320 .. 0x82338 on the f_opens arm)            = LT
   No other instruction of 0x81ca8 .. 0x826a4 writes fr + 2688, fr + 2768 or [s1 + 88 / 96 / 104 / 112]. *)
Definition ID1 (g : ghost) (j : nat) : list byte := rp_id (t_ID (g_in g) j) (flen g j) (t_g (g_in g) j).
Definition IDb1 (g : ghost) (fr : Z) (j : nat) (m : word -> option byte) : Prop :=
  IDBe g fr (ID1 g j) m /\ RcIdentModel.id_ok (ID1 g j).
Definition IFS1 (g : ghost) (fr : Z) (j : nat) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  IDb1 g fr j m /\ FGj g fr j m /\ FSj g fr j regs m.
Definition IFS2 (g : ghost) (fr : Z) (j : nat) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  IDb1 g fr j m /\ FGj g fr (S j) m /\ FSj g fr j regs m.
Definition IFS3 (g : ghost) (fr : Z) (j : nat) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  IDj g fr (S j) m /\ FGj g fr (S j) m /\ FSj g fr j regs m.
Definition Inv_A81d40_at (g : ghost) (j : nat) (c : config) : Prop :=
  CUTST g 0x81d40 [] (fun fr regs m => g_n g < 2 ^ 26 /\ LI g fr j regs m /\ FLSH g j fr regs m /\
    f1_IN g m /\ spill regs m 248 (fr + 176) /\ FLC fr regs m) c.
Definition Inv_A81d40 (g : ghost) (c : config) : Prop := exists j, Inv_A81d40_at g j c.
Definition Inv_A81da4_at (g : ghost) (j : nat) (c : config) : Prop :=
  exists phi, CUTST g 0x81da4 (hb1 phi (AC.a_size (flen g j)))
    (fun fr regs m => g_n g < 2 ^ 26 /\ (j <= 255)%nat /\ a0v regs phi /\ HB m phi (flen g j) /\
       LK g fr j regs m /\ FC g fr j regs m /\ FLSH g j fr regs m /\
       f1_IN g m /\ spill regs m 248 (fr + 176) /\ IFS g fr j regs m /\ FLC fr regs m) c.
Definition Inv_A81da4 (g : ghost) (c : config) : Prop := exists j, Inv_A81da4_at g j c.
(* ---- F4-F12 (0x81d64 .. 0x82064), push 6c: a Theorem Labs lane's Seg/B5Cuts.v (not in this delivery) (a working branch 97c6173c646), one
   text per address at which the nine lanes F4..F12 meet, each the union of what the exiting segment gives and
   what the entering one needs, on one shell b5_CUT (the FCUT skeleton with phi passed to the body, LK and the
   span's carry b5_C). What the base gives is not repeated (FRA / ENT, FLSI, fra_app, fra_frame, fra_win,
   fra_call_pre, HB's phi <> 0 and range, mem_inv never; see a Theorem Labs lane's file header). a Theorem Labs lane's helper lemmas (b5_byte1,
   b5_rt_cells, b5_wr, b5_frame_stk, b5_spill_stk) stay in Seg/B5Cuts.v (not in this delivery): they are segment-side drops, not cut text.
   Names qualified here: RcReply.reply_* / ir / ir_s, RcKind.kind_name / cstr_bytes, KNA (lib/A/Prog
   reac_ctrl_kind_name_c), FGA.REAC_CTRL_IDENTITY_FRAGMENT_K (lib/A/Prog reac_ctrl_identity_fragment_c).
   Conflicts a Theorem Labs lane reports (kept visible, push 6c report): C1 F13's own entry Inv_A820a0_loc needs `50 <= flen` but
   the short arm reaches 0x82064 / 0x820a0 (the official Inv_A82138_at does not carry it); C2 F11 / F12's local
   `fr + 3040 <= FS + FS_SIZE` is false on the real arm, b5_FS has the FS-conditional form; C3 s9 at 0x81ebc is
   `b2z (t_tfill j)`; C4 F9's gap closes from the base and b5_C; C5 b5_C is set before the loop, so F1..F3 must
   produce it at 0x81d64 (and the loop head / 0x81d0c / 0x81d38 do not carry it); C7 (a Theorem Labs lane 22:57Z) 0x81d64
   needs `u32 m (fr + 176) (t_k j)`, which F3's parse call at 0x81d60 writes through [A+248] = fr + 176. *)
(* A spill word of the 416-byte save area, with its base bound once. *)
Definition b5_sp (regs : bvmap 5 word) (m : word -> option byte) (off v : Z) : Prop :=
  exists A, rg regs 9 A /\ 0 <= A < 2 ^ 64 /\ q64 m (A + off) v.
(* The ten frame pointers the A4 / P / F1 prologue spills (0x812f0, 0x812fc, 0x81398, 0x81314, 0x81374,
   0x81c74-0x81c84, 0x81304, 0x8130c) and that no instruction of F4..F12 rewrites. *)
Definition b5_SPILL (A fr : Z) (m : word -> option byte) : Prop :=
  q64 m (A + 248) (fr + 176) /\ q64 m (A + 256) (fr + 256) /\ q64 m (A + 144) (fr + 2688) /\
  q64 m (A + 184) (fr + 336) /\ q64 m (A + 192) (fragb fr) /\
  q64 m (A + 80) (fragb fr + 15) /\ q64 m (A + 88) (fragb fr + 19) /\ q64 m (A + 96) (fragb fr + 8) /\
  q64 m (A + 272) (fr + 272) /\ q64 m (A + 264) (fr + 304).
(* The 72-byte fragment scratch fragb fr = fr + 2768 holding the turn's fragment state, and the 38-byte identity
   record at fr + 2688; no shadow byte of theirs is written in F4..F12. *)
Definition b5_FR (g : ghost) (j : nat) (fr : Z) (m : word -> option byte) : Prop :=
  addressable m (fragb fr) 72 /\ addressable m (fr + 2688) 38 /\
  bytes_at rsegs m (fragb fr) (t_FG (g_in g) j) /\ length (t_FG (g_in g) j) = 72%nat.
(* The three identity_reply cells, usable only after F9's shadow stores at S(fr)+32 / +34 / +38
   (0x81f28-0x81f4c): carried from 0x81f5c on. *)
Definition b5_RC (fr : Z) (m : word -> option byte) : Prop :=
  addressable m (fr + 256) 2 /\ addressable m (fr + 272) 8 /\ addressable m (fr + 304) 8.
(* The FakeStack facts a caller of this span needs that FRA does not give: the frame's containment in it on the
   side arm only (FS-conditional, so true on the real arm too), and the thread's DTLS word. *)
Definition b5_FS (fr : Z) (m : word -> option byte) : Prop :=
  (forall FS, word_mem rsegs m (AC.as_tp AC.ASYMS) FS -> 0 <= FS < 2 ^ 64 -> FS <= fr < FS + AC.FS_SIZE ->
     fr + FRAME_BYTES <= FS + AC.FS_SIZE) /\
  (exists DB, word_mem rsegs m (AC.as_tp AC.ASYMS + 8) DB /\ 0 <= DB /\ DB + 32 <= 2 ^ 64).
(* The kind-name table (0x9e6a0) the two reac_ctrl_kind_name calls of F7 / F8 read. *)
Definition b5_KN (m : word -> option byte) : Prop :=
  bytes_at rsegs m KNA.KIND_NAME KNA.kind_name_bytes /\ addressable m KNA.KIND_NAME 112.
(* The record block of the turn: its 50 model bytes and placement for a long frame; for an empty frame, the
   block is not in the FakeStack. *)
Definition b5_PH (g : ghost) (j : nat) (phi fr : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  (50 <= flen g j -> bytes_at rsegs m phi (t_g (g_in g) j)) /\
  (50 <= flen g j ->
     (phi + 50 <= fr \/ fr + FRAME_BYTES <= phi) /\
     (phi + 50 <= AC.aspZ regs - FGA.REAC_CTRL_IDENTITY_FRAGMENT_K \/ AC.aspZ regs <= phi)) /\
  (flen g j = 0 -> ~ AC.a_in_fs AC.ASYMS m phi).
(* The record invariant at phi (= s7), spills at A (= s1), a Theorem Labs lane's Seg/F18.v rec_inv (a version not in this delivery): carried through F18 / F19 (the
   record part of a Theorem Labs lane's Inv_A8236c_loc), re-assembled at each exit. The parsed-struct pointer spilled at [s1+248]
   is the frame address fr + 176 (0x81340 addi a0,s6,176; 0x81344 sd a0,248(s1), s6 = fr). *)
Definition rec_inv (g : ghost) (j : nat) (fr phi A : Z) (m : word -> option byte) : Prop :=
  0 < phi /\ phi + 50 <= 2 ^ 64 /\ (50 <= flen g j)%Z /\ 0 <= t_k (g_in g) j < 2 ^ 64 /\
  (forall a, phi <= a < phi + 50 -> app_mem a) /\
  q64 m (A + 200) (phi + 18) /\
  bytes_at rsegs m (phi + 18) (t_blk (g_in g) j) /\
  bytes_at rsegs m (phi + 34) (RcFrag.bsl (t_g (g_in g) j) 34 6) /\
  (exists (field16 v14 v15 v16 v17 : Z),
     q64 m (A + 248) (fr + 176) /\ q64 m (A + 280) (b2z (t_sum_ok (g_in g) j)) /\
     u16 m (fr + 176 + 20) field16 /\
     b8 m (phi + 14) v14 /\ b8 m (phi + 15) v15 /\ b8 m (phi + 16) v16 /\ b8 m (phi + 17) v17 /\
     0 <= v14 < 256 /\ 0 <= v15 < 256 /\ 0 <= v16 < 256 /\ 0 <= v17 < 256 /\
     b8 m (Z.shiftr (phi + 14) 3 + ASAN_K) 0 /\ b8 m (Z.shiftr (phi + 15) 3 + ASAN_K) 0 /\
     b8 m (Z.shiftr (phi + 16) 3 + ASAN_K) 0 /\ b8 m (Z.shiftr (phi + 17) 3 + ASAN_K) 0 /\
     field16 = v14 + 256 * v15 /\
     (if v16 =? 0 then (if v17 =? 0 then 1 else 0) else 0) = (if t_k (g_in g) j =? 1 then 1 else 0)).
(* Push 15 (the rec_inv split, a Theorem Labs lane): rec_inv's parse-made group is false on a long frame whose header is not
   0x88 0x19 (ctrlparse then writes 36 zero bytes, so the u16 at fr + 196 is 0 and t_k j is 0, while phi's bytes
   14 .. 17 are raw), so the cuts that reach that arm carry rec_inv as its two halves: rec_inv0 (the
   header-independent part, under 50 <= flen g j) and rec_parse (under t_8819 (g_in g) j = true). rec_inv itself is
   unchanged and stays the form F19 .. F21 / B7 use on the 8819 arm (Inv_A82400_at keeps it whole);
   rec_inv_of_split / rec_inv_split convert. The phi bounds in rec_inv0 are also derivable from HB on every
   frame-loop cut: HB m phi (flen g j) is phi <> 0 /\ addressable m phi (AC.a_size (flen g j)), and addressable
   gives 0 <= phi and phi + a_size flen <= APPMEM_END < 2 ^ 64 with a_size flen = flen >= 50. *)
Definition rec_inv0 (g : ghost) (j : nat) (fr phi A : Z) (m : word -> option byte) : Prop :=
  0 < phi /\ phi + 50 <= 2 ^ 64 /\ (50 <= flen g j)%Z /\ 0 <= t_k (g_in g) j < 2 ^ 64 /\
  (forall a, phi <= a < phi + 50 -> app_mem a) /\
  q64 m (A + 200) (phi + 18) /\
  bytes_at rsegs m (phi + 18) (t_blk (g_in g) j) /\
  bytes_at rsegs m (phi + 34) (RcFrag.bsl (t_g (g_in g) j) 34 6) /\
  q64 m (A + 248) (fr + 176) /\ q64 m (A + 280) (b2z (t_sum_ok (g_in g) j)).
Definition rec_parse (g : ghost) (j : nat) (fr phi : Z) (m : word -> option byte) : Prop :=
  exists (field16 v14 v15 v16 v17 : Z),
    u16 m (fr + 176 + 20) field16 /\
    b8 m (phi + 14) v14 /\ b8 m (phi + 15) v15 /\ b8 m (phi + 16) v16 /\ b8 m (phi + 17) v17 /\
    0 <= v14 < 256 /\ 0 <= v15 < 256 /\ 0 <= v16 < 256 /\ 0 <= v17 < 256 /\
    b8 m (Z.shiftr (phi + 14) 3 + ASAN_K) 0 /\ b8 m (Z.shiftr (phi + 15) 3 + ASAN_K) 0 /\
    b8 m (Z.shiftr (phi + 16) 3 + ASAN_K) 0 /\ b8 m (Z.shiftr (phi + 17) 3 + ASAN_K) 0 /\
    field16 = v14 + 256 * v15 /\
    (if v16 =? 0 then (if v17 =? 0 then 1 else 0) else 0) = (if t_k (g_in g) j =? 1 then 1 else 0).
Lemma rec_inv_of_split : forall g j fr phi A m,
  rec_inv0 g j fr phi A m -> rec_parse g j fr phi m -> rec_inv g j fr phi A m.
Proof.
  intros g j fr phi A m (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10)
    (f & v14 & v15 & v16 & v17 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15).
  unfold rec_inv. repeat (split; [assumption|]).
  exists f, v14, v15, v16, v17. repeat (split; [assumption|]). exact P15.
Qed.
Lemma rec_inv_split : forall g j fr phi A m,
  rec_inv g j fr phi A m -> rec_inv0 g j fr phi A m /\ rec_parse g j fr phi m.
Proof.
  intros g j fr phi A m (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 &
    f & v14 & v15 & v16 & v17 & H9 & H10 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 &
    P15).
  split.
  - unfold rec_inv0. repeat (split; [assumption|]). exact H10.
  - exists f, v14, v15, v16, v17. repeat (split; [assumption|]). exact P15.
Qed.
(* The carry of the whole span: set before 0x81d64, written by no instruction of F4..F12. *)
Definition b5_C (g : ghost) (j : nat) (phi fr : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  rg regs 23 phi /\ rg regs 18 (flen g j) /\
  (exists A, rg regs 9 A /\ 0 <= A < 2 ^ 64 /\ b5_SPILL A fr m /\
     (* push 13 group C (a Theorem Labs lane): [A + 232] = the length flag, stored once at 0x81d18 / 0x81d20, before
        0x81d64; F17CARRY reads it at 0x820a0. The prologue spills [A + 136] / [A + 120] / [A + 176] that a Theorem Labs lane
        also asked for are NOT repeated here: PRO (push 13B) carries them in FLSH, which b5_CUT has through
        FLSI, and b5_C's own `0 <= A < 2 ^ 64` identifies that A with this one. *)
     q64 m (A + 232) (if t_big (g_in g) j then 0 else 1)) /\
  b5_PH g j phi fr regs m /\ b5_FR g j fr m /\ b5_FS fr m /\ b5_KN m /\
  (* push 12 group B: the fragment record and the first-fragment spills of turn j, which no instruction of
     F4 .. F12 writes (the identity record is the stage value, per cut). *)
  FGj g fr j m /\ FSj g fr j regs m.
(* The cut shape of the span: the FCUT skeleton plus LK and the carry, with phi handed to the body. *)
Definition b5_CUT (g : ghost) (pc : Z) (j : nat)
    (P : Z -> Z -> bvmap 5 word -> (word -> option byte) -> Prop) (c : config) : Prop :=
  exists phi, CUTST g pc (hb1 phi (AC.a_size (flen g j)))
    (fun fr regs m =>
       g_n g < 2 ^ 26 /\ (j <= 255)%nat /\ HB m phi (flen g j) /\ FLSI g j fr regs m /\
       LK g fr j regs m /\ b5_C g j phi fr regs m /\ P phi fr regs m) c.
(* The model registers and spills of the turn, from the join 0x81ebc to the end of the span: both arms set them
   before 0x81ebc (short arm 0x81df8-0x81e04, long arm 0x81e60-0x81eb8); fr + 176 holds the kind the parse wrote
   (F3's call at 0x81d60 or F4's at 0x81de8, o = [A+248] = fr + 176; F6's call has o = 0). *)
Definition b5_K (g : ghost) (j : nat) (phi fr : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  rg regs 20 (1 - b2z (t_sum_ok (g_in g) j)) /\
  rg regs 22 (if t_big (g_in g) j then phi + 18 else 0) /\
  rg regs 24 (t_k (g_in g) j) /\
  rg regs 25 (b2z (t_tfill (g_in g) j)) /\
  b5_sp regs m 280 (b2z (t_sum_ok (g_in g) j)) /\
  u32 m (fr + 176) (t_k (g_in g) j) /\
  RcReply.reply_args phi (fr + 256) (fr + 272) (fr + 304) = true.
(* The three reply cells of the identity_reply post under reply_ok (reac_ctrl_identity_reply_c.v:90-93). *)
Definition b5_RPost (phi fr : Z) (G : list byte) (m : word -> option byte) : Prop :=
  rw_cells rsegs m (fr + 256) [CB 2 (RcReply.reply_addr G)] /\
  rw_cells rsegs m (fr + 272) [CB 8 (le8 (Z_to_bv 64 (phi + 38)))] /\
  rw_cells rsegs m (fr + 304) [CB 8 (le8 (Z_to_bv 64 (RcReply.ir_s G - 13)))].
(* ---- Push 13 group C (a Theorem Labs lane): the F17CARRY fields that F4 .. F12 set and no later
   instruction of the span writes, so that F13's entry Inv_A82138_at (F16CARRY / F17CARRY) has a producer. Each
   bundle starts where the listing makes it true, which is later than a Theorem Labs lane's request in three places (see the push
   13 report): [A + 240] from 0x81e10 (the stores are 0x81db4 / 0x81dfc / 0x81e0c, so at 0x81dec / 0x81df0 /
   0x81e0c the spill still holds turn j - 1's value), and `spill regs m 152 (b2z (t_tfill j))` on NO b5 cut at all
   (0x820fc `sd s9,152(s1)` is the store, i.e. the last b5 cut is at it; F12 gives it at 0x82138 from b5_K's s9).
   Push 14 group C (a Theorem Labs lane, F6 lane): 13C's b5_F17b (0x81ebc on, with rec_inv) is replaced by b5_PF on all
   sixteen b5 cuts from 0x81d64: the facts F2's memcpy (0x81d34) and F3's parse (0x81d60, o = [A+248] = fr + 176)
   make, plus the two compare spills P12 sets before the loop. rec_inv itself is on no b5 cut: F12 assembles it at
   0x820a0 (F17CARRY) from b5_PF, b5_F17 ([A + 192]), PRO ([A + 248]), b5_K's [A + 280] and b5_PH. *)
(* [A + 192] = phi + 18: F4's 0x81d6c (s9 = phi + 18) on the long arm and 0x81dc0 (a0 = s7 + 18) on the empty one;
   no later store to [s1 + 192] in F4 .. F12. *)
Definition b5_F17 (g : ghost) (j : nat) (phi fr : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  exists A, rg regs 9 A /\ 0 <= A < 2 ^ 64 /\ q64 m (A + 200) (phi + 18).
(* [A + 240]: F4 stores b2z (t_8819 j) at 0x81db4 on the 8819-tested arm and 0 at 0x81dfc (short) / 0x81e0c
   (byte 12 <> 0x88); nothing else writes it in the span. a Theorem Labs lane's guarded form, as in F17CARRY. *)
Definition b5_W240 (g : ghost) (j : nat) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  exists A, rg regs 9 A /\ 0 <= A < 2 ^ 64 /\
    exists w240, q64 m (A + 240) w240 /\ 0 <= w240 < 2 ^ 64 /\
      (t_8819 (g_in g) j = true -> w240 <> 0) /\ (t_8819 (g_in g) j = false -> w240 = 0).
(* b5_PF: the record / parse facts of F17CARRY, true from 0x81d64 on (F1-F3 promise) and written by no instruction
   or callee of F4 .. F12 (the second parse at 0x81de8 runs only on the flen = 0 arm, where every part is guarded
   off; F6's parse at 0x81ec8 has o = 0):
   - under 50 <= flen: the record's first 38 bytes and the frame body at phi (F2's memcpy 0x81d34);
   - under t_8819 j = true: the part of rec_inv that F3's parse makes (the u16 at fr + 196 from the parse output at
     fr + 176, phi's bytes 14 .. 17 and their shadow bytes, field16 = v14 + 256 * v15 and the (v16, v17) =
     (t_k j =? 1) equation), and the two 6-byte compares of F18 / F19. Their spills [A + 56] = fr + 186 and
     [A + 48] = fr + 180 are P12's 0x81d0c .. 0x81c98 (before the loop head; no store to [s1 + 48 / 56] in
     0x81ca8 .. 0x828b0; FLC carries them since push 14E); the compared bytes at fr + 186 / fr + 180 are F3's parse
     output; their shadow S(fr) + 22 .. 26 is cleared at 0x81d3c .. 0x81d50 (and again at 0x81dc4 .. 0x81dd8) and
     re-poisoned by no instruction of 0x81d38 .. 0x820a0.
   Push 14 group E (soundness fix, found by the F1-F3 lane): the parse-made group was under 50 <= flen in 14C, which
   is false when flen >= 50 but bytes 12 / 13 of t_g j are not 0x88 / 0x19: then ctrlparse's header check fails,
   the parse output is 36 zero bytes (u16 at fr + 196 = 0, t_k j = 0) while v14 .. v17 are the raw frame bytes, so
   e.g. byte 12 = 0, byte 14 = 1 gives field16 = 0 <> 1. Under t_8819 j = true the header check passes.
   rec_inv's [A + 192] / [A + 248] / [A + 280] conjuncts and its phi bounds are NOT here (b5_F17, PRO, b5_K's
   [A + 280] spill and b5_PH have them). *)
Definition b5_PF (g : ghost) (j : nat) (phi fr : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  exists A, rg regs 9 A /\ 0 <= A < 2 ^ 64 /\
    (50 <= flen g j ->
       (exists rb, bytes_at rsegs m phi rb /\ (38 <= length rb)%nat) /\
       bytes_at rsegs m phi (t_phi (g_in g) j)) /\
    (t_8819 (g_in g) j = true ->
       (exists (field16 v14 v15 v16 v17 : Z),
          u16 m (fr + 176 + 20) field16 /\
          b8 m (phi + 14) v14 /\ b8 m (phi + 15) v15 /\ b8 m (phi + 16) v16 /\ b8 m (phi + 17) v17 /\
          0 <= v14 < 256 /\ 0 <= v15 < 256 /\ 0 <= v16 < 256 /\ 0 <= v17 < 256 /\
          b8 m (Z.shiftr (phi + 14) 3 + ASAN_K) 0 /\ b8 m (Z.shiftr (phi + 15) 3 + ASAN_K) 0 /\
          b8 m (Z.shiftr (phi + 16) 3 + ASAN_K) 0 /\ b8 m (Z.shiftr (phi + 17) 3 + ASAN_K) 0 /\
          field16 = v14 + 256 * v15 /\
          (if v16 =? 0 then (if v17 =? 0 then 1 else 0) else 0) = (if t_k (g_in g) j =? 1 then 1 else 0)) /\
       (exists (ls rs : list byte),
          q64 m (A + 72) (fr + 186) /\ bytes_at rsegs m (fr + 186) ls /\ (6 <= length ls)%nat /\
          bytes_at rsegs m phi rs /\ (6 <= length rs)%nat /\ SFA.memcmp_model ls rs 6 = Some 0 /\
          addressable m (fr + 186) 6) /\
       (exists (ls2 rs2 : list byte),
          q64 m (A + 64) (fr + 180) /\ bytes_at rsegs m (fr + 180) ls2 /\ (6 <= length ls2)%nat /\
          bytes_at rsegs m (phi + 6) rs2 /\ (6 <= length rs2)%nat /\ SFA.memcmp_model ls2 rs2 6 = Some 0 /\
          addressable m (fr + 180) 6)).
(* 0x81d38 - F2 exit / F3 entry (after F2's checked_memcpy at 0x81d34), push 14 group D: the F1-F3 lane's
   Inv_A81d38_c5_at (Seg/F2.v (a version not in this delivery; written on a working branch fc681b5ab1d)), on the b5_CUT shell (so b5_C's
   `rg regs 23 phi` is its phi pin: s7 = phi from 0x81d0c `mv s7,a0`, a Theorem Labs lane's cut_hb item 1 (a working note, not in this delivery)). It implies the
   old FCUT text (LK, FC, IFS = IDj with b5_C's FGj / FSj); FCUT, which had no other user, is gone. s6 is
   0x81db0 `sltiu s6,s2,50`, so 0 on a long frame; the frame body is at phi after the memcpy. *)
Definition Inv_A81dd0_at (g : ghost) (j : nat) (c : config) : Prop :=
  b5_CUT g 0x81dd0 j (fun phi fr regs m =>
    FC g fr j regs m /\ (50 <= flen g j -> rg regs 22 0) /\
    (50 <= flen g j -> bytes_at rsegs m phi (t_phi (g_in g) j)) /\ IDj g fr j m) c.
Definition Inv_A81dd0 (g : ghost) (c : config) : Prop := exists j, Inv_A81dd0_at g j c.
(* 0x81d64 - F3 exit / F4 entry 1 (the return of `jal reac_ctrl_parse` at 0x81d60): a0 = the parse result, also
   at the output slot fr + 176 (C7), s9 = phi + 18, and on the long arm s6 = 0 (0x81d18). FC is the skeleton's
   own conjunct at this address; F4 does not read it. *)
Definition Inv_A81dfc_at (g : ghost) (j : nat) (c : config) : Prop :=
  b5_CUT g 0x81dfc j (fun phi fr regs m =>
    FC g fr j regs m /\
    rg regs 10 (t_k (g_in g) j) /\ rg regs 25 (phi + 18) /\
    (50 <= flen g j -> rg regs 22 0) /\ u32 m (fr + 176) (t_k (g_in g) j) /\ IDj g fr j m /\
    b5_PF g j phi fr regs m) c.
Definition Inv_A81dfc (g : ghost) (c : config) : Prop := exists j, Inv_A81dfc_at g j c.
(* 0x81dbc - F4 entry 2 (`beqz s2,81dbc` at 0x81d24): the record is empty, the block one byte wide. New cut. *)
Definition Inv_A81e54_at (g : ghost) (j : nat) (c : config) : Prop :=
  b5_CUT g 0x81e54 j (fun phi fr regs m =>
    flen g j = 0 /\ (phi + 1 <= fr \/ fr + FRAME_BYTES <= phi) /\ IDj g fr j m /\ b5_PF g j phi fr regs m) c.
Definition Inv_A81e54 (g : ghost) (c : config) : Prop := exists j, Inv_A81e54_at g j c.
(* 0x81dec - F4 exit (the second parse call's return) / F5 entry: a0 = the parse result, also at fr + 176. *)
Definition Inv_A81e84_at (g : ghost) (j : nat) (c : config) : Prop :=
  b5_CUT g 0x81e84 j (fun phi fr regs m =>
    flen g j < 50 /\ rg regs 10 (t_k (g_in g) j) /\ u32 m (fr + 176) (t_k (g_in g) j) /\ IDj g fr j m /\
    b5_F17 g j phi fr regs m /\ b5_PF g j phi fr regs m) c.
Definition Inv_A81e84 (g : ghost) (c : config) : Prop := exists j, Inv_A81e84_at g j c.
(* 0x81df0 - F4 exit (the `bgeu a0,s2` arm at 0x81d70, len <= 49) / F5 internal join: s8 = the parse result.
   New cut. *)
Definition Inv_A81e88_at (g : ghost) (j : nat) (c : config) : Prop :=
  b5_CUT g 0x81e88 j (fun phi fr regs m =>
    flen g j < 50 /\ rg regs 24 (t_k (g_in g) j) /\ u32 m (fr + 176) (t_k (g_in g) j) /\ IDj g fr j m /\
    b5_F17 g j phi fr regs m /\ b5_PF g j phi fr regs m) c.
Definition Inv_A81e88 (g : ghost) (c : config) : Prop := exists j, Inv_A81e88_at g j c.
(* 0x81e0c - F4 exit (long arm, record byte 12 is not 0x88, so t_8819 j is false) / F5 entry. New cut. *)
Definition Inv_A81ea4_at (g : ghost) (j : nat) (c : config) : Prop :=
  b5_CUT g 0x81ea4 j (fun phi fr regs m =>
    50 <= flen g j /\ rg regs 22 0 /\ rg regs 24 (t_k (g_in g) j) /\ rg regs 25 (phi + 18) /\
    t_8819 (g_in g) j = false /\ u32 m (fr + 176) (t_k (g_in g) j) /\ IDj g fr j m /\
    b5_F17 g j phi fr regs m /\ b5_PF g j phi fr regs m) c.
Definition Inv_A81ea4 (g : ghost) (c : config) : Prop := exists j, Inv_A81ea4_at g j c.
(* 0x81e10 - F4 exit (long arm past the byte-13 test, [A+240] written at 0x81db4) / F5 entry. New cut. *)
Definition Inv_A81ea8_at (g : ghost) (j : nat) (c : config) : Prop :=
  b5_CUT g 0x81ea8 j (fun phi fr regs m =>
    50 <= flen g j /\ rg regs 22 0 /\ rg regs 24 (t_k (g_in g) j) /\ rg regs 25 (phi + 18) /\
    b5_sp regs m 240 (b2z (t_8819 (g_in g) j)) /\ u32 m (fr + 176) (t_k (g_in g) j) /\ IDj g fr j m /\
    b5_F17 g j phi fr regs m /\ b5_W240 g j regs m /\ b5_PF g j phi fr regs m) c.
Definition Inv_A81ea8 (g : ghost) (c : config) : Prop := exists j, Inv_A81ea8_at g j c.
(* 0x81e28 - F5 exit / F6 entry: the first turn of the 32-byte block-sum loop (a0 = a2 = phi + 18, a1 = 0,
   a3 = 32, s6 = s9 = phi + 18, [A+240] = b2z (t_8819 j)). *)
Definition Inv_A81ec0_at (g : ghost) (j : nat) (c : config) : Prop :=
  b5_CUT g 0x81ec0 j (fun phi fr regs m =>
    50 <= flen g j /\
    rg regs 10 (phi + 18) /\ rg regs 11 0 /\ rg regs 12 (phi + 18) /\ rg regs 13 32 /\
    rg regs 22 (phi + 18) /\ rg regs 24 (t_k (g_in g) j) /\ rg regs 25 (phi + 18) /\
    b5_sp regs m 240 (b2z (t_8819 (g_in g) j)) /\ u32 m (fr + 176) (t_k (g_in g) j) /\ IDj g fr j m /\
    b5_F17 g j phi fr regs m /\ b5_W240 g j regs m /\ b5_PF g j phi fr regs m) c.
Definition Inv_A81ec0 (g : ghost) (c : config) : Prop := exists j, Inv_A81ec0_at g j c.
(* 0x81ebc - F5 exit (the short arm's `j 81ebc`) and F6 internal join / F6 entry: the pre-state of the second
   reac_ctrl_parse call; both arms reach it with b5_K set (C3). New cut. *)
Definition Inv_A81f54_at (g : ghost) (j : nat) (c : config) : Prop :=
  b5_CUT g 0x81f54 j (fun phi fr regs m => b5_K g j phi fr regs m /\ IDj g fr j m /\
    b5_F17 g j phi fr regs m /\ b5_W240 g j regs m /\ b5_PF g j phi fr regs m) c.
Definition Inv_A81f54 (g : ghost) (c : config) : Prop := exists j, Inv_A81f54_at g j c.
(* 0x81ecc - F6 exit / F7 entry: a0 = s8 = the parse result (also the word at fr + 176). *)
Definition Inv_A81f64_at (g : ghost) (j : nat) (c : config) : Prop :=
  b5_CUT g 0x81f64 j (fun phi fr regs m =>
    b5_K g j phi fr regs m /\ rg regs 10 (t_k (g_in g) j) /\ IDj g fr j m /\
    b5_F17 g j phi fr regs m /\ b5_W240 g j regs m /\ b5_PF g j phi fr regs m) c.
Definition Inv_A81f64 (g : ghost) (c : config) : Prop := exists j, Inv_A81f64_at g j c.
(* 0x81ee4 - F7 exit (the first reac_ctrl_kind_name return) / F8 entry: a0 = the name address, non-null. *)
Definition Inv_A81f7c_at (g : ghost) (j : nat) (c : config) : Prop :=
  b5_CUT g 0x81f7c j (fun phi fr regs m =>
    b5_K g j phi fr regs m /\ rg regs 10 (KNA.kind_name_addr (t_k (g_in g) j)) /\ IDj g fr j m /\
    b5_F17 g j phi fr regs m /\ b5_W240 g j regs m /\ b5_PF g j phi fr regs m) c.
Definition Inv_A81f7c (g : ghost) (c : config) : Prop := exists j, Inv_A81f7c_at g j c.
(* 0x81ef0 - F8 exit (the second kind_name return) / F9 entry: the name address and its bytes. *)
Definition Inv_A81f88_at (g : ghost) (j : nat) (c : config) : Prop :=
  b5_CUT g 0x81f88 j (fun phi fr regs m =>
    b5_K g j phi fr regs m /\ rg regs 10 (KNA.kind_name_addr (t_k (g_in g) j)) /\
    bytes_at rsegs m (KNA.kind_name_addr (t_k (g_in g) j))
      (RcKind.cstr_bytes (RcKind.kind_name (t_k (g_in g) j))) /\ IDj g fr j m /\
    b5_F17 g j phi fr regs m /\ b5_W240 g j regs m /\ b5_PF g j phi fr regs m) c.
Definition Inv_A81f88 (g : ghost) (c : config) : Prop := exists j, Inv_A81f88_at g j c.
(* 0x81f5c - F9 exit (the reac_ctrl_identity_reply return) / F10 entry: a0 = the contract's result; under
   reply_ok the three reply cells hold the reply's bytes; b5_RC starts here. *)
Definition Inv_A81ff4_at (g : ghost) (j : nat) (c : config) : Prop :=
  b5_CUT g 0x81ff4 j (fun phi fr regs m =>
    b5_K g j phi fr regs m /\ b5_RC fr m /\
    rg regs 10 (RcReply.reply_ret phi (flen g j) (fr + 256) (fr + 272) (fr + 304) (t_g (g_in g) j)) /\
    (RcReply.reply_ok phi (flen g j) (fr + 256) (fr + 272) (fr + 304) (t_g (g_in g) j) = true ->
       b5_RPost phi fr (t_g (g_in g) j) m) /\ IDj g fr j m /\
    b5_F17 g j phi fr regs m /\ b5_W240 g j regs m /\ b5_PF g j phi fr regs m) c.
Definition Inv_A81ff4 (g : ghost) (c : config) : Prop := exists j, Inv_A81ff4_at g j c.
(* 0x81fd4 - F10 exit (fall-through) / F11 entry 1: the record-sum loop head of the reply arm. *)
Definition Inv_A8206c_at (g : ghost) (j : nat) (c : config) : Prop :=
  b5_CUT g 0x8206c j (fun phi fr regs m =>
    b5_K g j phi fr regs m /\ b5_RC fr m /\
    50 <= flen g j /\ t_sum_ok (g_in g) j = true /\
    RcReply.reply_ok phi (flen g j) (fr + 256) (fr + 272) (fr + 304) (t_g (g_in g) j) = true /\
    b5_RPost phi fr (t_g (g_in g) j) m /\
    rg regs 10 (phi + 34) /\ rg regs 11 (RcReply.ir_s (t_g (g_in g) j) - 8) /\ rg regs 12 (phi + 38) /\
    rg regs 13 (RcReply.ir_s (t_g (g_in g) j) - 13) /\ rg regs 14 0 /\ rg regs 15 (phi + 34) /\
    IDj g fr j m /\
    b5_F17 g j phi fr regs m /\ b5_W240 g j regs m /\ b5_PF g j phi fr regs m) c.
Definition Inv_A8206c (g : ghost) (c : config) : Prop := exists j, Inv_A8206c_at g j c.
(* 0x82014 - F10 exit (`beqz a1` at 0x81fc4 taken) / F11 entry 2: the reply arm with the loop skipped. New cut. *)
Definition Inv_A820ac_at (g : ghost) (j : nat) (c : config) : Prop :=
  b5_CUT g 0x820ac j (fun phi fr regs m =>
    b5_K g j phi fr regs m /\ b5_RC fr m /\
    50 <= flen g j /\ t_sum_ok (g_in g) j = true /\
    RcReply.reply_ok phi (flen g j) (fr + 256) (fr + 272) (fr + 304) (t_g (g_in g) j) = true /\
    b5_RPost phi fr (t_g (g_in g) j) m /\
    rg regs 11 0 /\ rg regs 12 (phi + 38) /\ rg regs 13 (RcReply.ir_s (t_g (g_in g) j) - 13) /\
    IDj g fr j m /\
    b5_F17 g j phi fr regs m /\ b5_W240 g j regs m /\ b5_PF g j phi fr regs m) c.
Definition Inv_A820ac (g : ghost) (c : config) : Prop := exists j, Inv_A820ac_at g j c.
(* 0x82060 - F11 exit (the reac_identity_ingest return) / F12 entry 2: the result is 0 or 1. *)
Definition Inv_A820f8_at (g : ghost) (j : nat) (c : config) : Prop :=
  b5_CUT g 0x820f8 j (fun phi fr regs m =>
    b5_K g j phi fr regs m /\ b5_RC fr m /\
    50 <= flen g j /\ (exists v, rg regs 10 v /\ 0 <= v < 2 ^ 63) /\ IDb1 g fr j m /\
    b5_F17 g j phi fr regs m /\ b5_W240 g j regs m /\ b5_PF g j phi fr regs m) c.
Definition Inv_A820f8 (g : ghost) (c : config) : Prop := exists j, Inv_A820f8_at g j c.
(* 0x820fc - F10 exit (`bne a0,1` at 0x81ffc taken: the reply arm is not entered) / F12 entry 1. Reached on BOTH
   frame arms, so it carries no length bound (C1). New cut. *)
Definition Inv_A820fc_at (g : ghost) (j : nat) (c : config) : Prop :=
  b5_CUT g 0x820fc j (fun phi fr regs m =>
    b5_K g j phi fr regs m /\ b5_RC fr m /\
    RcReply.ir (flen g j) (t_g (g_in g) j) = false /\ IDb1 g fr j m /\
    b5_F17 g j phi fr regs m /\ b5_W240 g j regs m /\ b5_PF g j phi fr regs m) c.
Definition Inv_A820fc (g : ghost) (c : config) : Prop := exists j, Inv_A820fc_at g j c.
(* ---- F13 / F14 / F15 / F16 entries (0x820a0, 0x820bc, 0x820dc, 0x820e0, 0x82134), push 11 group B: a Theorem Labs lane's
   texts at a working branch d70d9f38074 (seg_F13 .. seg_F16 Qed there on push 8), adopted verbatim:
   Seg/F13.v Inv_A820a0_loc / Inv_A820bc_loc with frcl / frrec and the bundles F17CARRY / F16CARRY, Seg/F14.v
   f14_tail / Inv_A820dc_loc / Inv_A820e0_loc, Seg/F15.v Inv_A82134_loc (= Seg/F16.v's, the same text). Only the
   names a Theorem Labs lane's files import unqualified are written with SlotInv's module prefixes: RcFrag.fg_case / fg_class /
   fg_ret / fg_addr (lib/Prog RcFrag), FGA.fg_mem / FGA.REAC_CTRL_IDENTITY_FRAGMENT_K, BWA.BCMP / REAL_BCMP /
   REAL_MEMCMP / GOT_CF / CF, MCA.MEMCMP and SFA.memcmp_model (the same constants). The record invariant rec_inv
   (a Theorem Labs lane's Seg/F18.v (a version not in this delivery)) moves from the F17 block to :2062, before b5_RPost / b5_W240 and F17CARRY; F17CARRY names it (as rec_inv0 / rec_parse).
   0x820a0 / 0x820bc / 0x820dc / 0x820e0 are reached on both frame arms (heap list `hb1 phi (AC.a_size (flen g j))`,
   record facts under `50 <= flen g j ->`); 0x82134 only when the turn closes a record (t_rf = 1, FgClose, so
   50 <= flen g j). Push 14 group B (a Theorem Labs lane's cut_hb inventory): 0x82134's heap list is now
   `hb1 phi (AC.a_size (flen g j))` like every other frame-loop cut (a Theorem Labs lane's text had `hb1 phi (flen g j)`; the two are
   equal here, since AC.a_size n = Z.max n 1 and flen g j >= 50 on the only path into 0x82134). *)
(* The fragment class and the record's post bytes, at this call site's pointers. *)
Definition frcl (g : ghost) (j : nat) (fr phi : Z) : RcFrag.fg_case :=
  RcFrag.fg_class (fragb fr) phi (fr + 256) (fr + 272) (fr + 304) (flen g j) (t_FG (g_in g) j) (t_g (g_in g) j).
Definition frrec (g : ghost) (j : nat) (fr phi : Z) : list byte :=
  fg_next (t_FG (g_in g) j) (t_g (g_in g) j) (frcl g j fr phi).
(* The fields of the F17 entry cuts Inv_A8229c_at / Inv_A822a0_at that F13-F16 neither read nor write, in that
   text's exact forms (a7). Two groups hold only on some arms: [A+240] is nonzero exactly on the 8819 arm (0x81db4
   stores the byte-13 test; 0x81e0c and 0x81dfc store 0), and the record facts hold for a frame of at least 50
   bytes (the short arm's block is shorter). s6 = phi + 18 only when the frame is long (0x81df4 `li s6,0`) and
   [A+232] is the length flag (0x81d18 / 0x81d20), so both take the turn's conditional value; [A+192] = phi + 18
   holds on every arm (0x81d6c / 0x81dc0). *)
Definition F17CARRY (g : ghost) (j : nat) (fr phi A : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  (* s7 = phi, s6, s8 = k, s2 = len; push 13 group A (a Theorem Labs lane): s4 = 1 - sum_ok, which F17's 0x821c8
     `or a0,a0,s4` reads to decide whether the opens_record body (and so its four first-fragment spill stores)
     runs. Set at 0x81e04 `li s4,1` (short arm) / 0x81eb8 `snez s4,a0` (long arm), callee-saved, and written by
     no instruction of 0x81ebc .. 0x821c4 (listing); b5_K has it up to 0x82064, so F12 and F13-F16 thread it. *)
  rg regs 23 phi /\ rg regs 22 (if t_big (g_in g) j then phi + 18 else 0) /\
  rg regs 24 (t_k (g_in g) j) /\ rg regs 18 (flen g j) /\
  rg regs 20 (1 - b2z (t_sum_ok (g_in g) j)) /\
  (* spills: [A+232] the length flag, [A+192] = phi + 18, [A+136] = fr + 128, [A+120] = fr + 160,
     [A+176] = fr + 64, [A+152] = tfill of the turn *)
  q64 m (A + 232) (if t_big (g_in g) j then 0 else 1) /\ q64 m (A + 200) (phi + 18) /\
  q64 m (A + 136) (fr + 128) /\ q64 m (A + 120) (fr + 160) /\ q64 m (A + 176) (fr + 64) /\
  spill regs m 152 (b2z (t_tfill (g_in g) j)) /\
  (* [A+240]: nonzero on the 8819 arm, 0 on every other arm *)
  (exists w240, q64 m (A + 240) w240 /\ 0 <= w240 < 2 ^ 64 /\
     (t_8819 (g_in g) j = true -> w240 <> 0) /\ (t_8819 (g_in g) j = false -> w240 = 0)) /\
  (* the record facts of a frame of at least 50 bytes: the first 38 bytes, the 50 model bytes, the frame body
     the memcpy at 0x81d34 left at phi, and the record invariant *)
  (50 <= flen g j ->
     (exists rb, bytes_at rsegs m phi rb /\ (38 <= length rb)%nat) /\
     bytes_at rsegs m phi (t_g (g_in g) j) /\ bytes_at rsegs m phi (t_phi (g_in g) j) /\
     rec_inv0 g j fr phi A m) /\
  (* the parse-made part of rec_inv (push 15: only on the 8819 arm, where ctrlparse's header check passes) and
     the two 6-byte compares of F18 / F19 ([A+56] = fr + 186 vs phi, [A+48] = fr + 180 vs phi + 6) *)
  (t_8819 (g_in g) j = true ->
     rec_parse g j fr phi m /\
     (exists (ls rs : list byte),
        q64 m (A + 72) (fr + 186) /\ bytes_at rsegs m (fr + 186) ls /\ (6 <= length ls)%nat /\
        bytes_at rsegs m phi rs /\ (6 <= length rs)%nat /\ SFA.memcmp_model ls rs 6 = Some 0 /\
        addressable m (fr + 186) 6) /\
     (exists (ls2 rs2 : list byte),
        q64 m (A + 64) (fr + 180) /\ bytes_at rsegs m (fr + 180) ls2 /\ (6 <= length ls2)%nat /\
        bytes_at rsegs m (phi + 6) rs2 /\ (6 <= length rs2)%nat /\ SFA.memcmp_model ls2 rs2 6 = Some 0 /\
        addressable m (fr + 180) 6)).
(* The F16 entry fields F16 reads but F13-F15 do not compute (frag_ok and the first-fragment spills of the
   0x82184 / 0x82198 / 0x821b4 tests; the ingest's identity buffer at fr + 2688 = [A+144]), and F17CARRY. *)
Definition F16CARRY (g : ghost) (j : nat) (fr phi A : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  frag_ok (t_FG (g_in g) j) /\ FSj g fr j regs m /\
  (exists idb, bytes_at rsegs m (fr + 2688) idb /\ length idb = 38%nat) /\ addressable m (fr + 2688) 38 /\
  q64 m (A + 144) (fr + 2688) /\
  F17CARRY g j fr phi A regs m.
(* F13 entry (0x820a0, pre-call): FRA + j/HB/LK, the six call arguments with their addressability, and the F14/F15
   data that must survive the call. Every placement fact comes from FRA (fra_frame / fra_win). 0x820a0 is reached
   on both frame arms (flen < 50 too: 0x82064 -> 0x820a0), so the heap list is the base's
   `hb1 phi (AC.a_size (flen g j))` (a 0-byte record is a 1-byte block), and the record's 50 model bytes are guarded
   by 50 <= flen, as in b5_PH. The record's placement against the frame and the callee's window and its 50
   addressable bytes on the long arm are not cut conjuncts: seg_F13 reads them off FRA, the block law of the heap
   list and HB. *)
Definition Inv_A82138_at (g : ghost) (j : nat) (c : config) : Prop :=
  exists phi, CUTST g 0x82138 (hb1 phi (AC.a_size (flen g j)))
    (fun fr regs m =>
       g_n g < 2 ^ 26 /\ (j <= 255)%nat /\ HB m phi (flen g j) /\ FLSI g j fr regs m /\ LK g fr j regs m /\
       exists (A v280 : Z),
         (* registers: s1 = A (spill base), s9 = the record; s7 = phi and s2 = len are in F16CARRY *)
         rg regs 9 A /\ rg regs 25 (fragb fr) /\
         0 <= A < 2 ^ 64 /\ 0 <= v280 < 2 ^ 64 /\ v280 = b2z (t_sum_ok (g_in g) j) /\
         (* the fragment precondition at the six arguments (the record's model bytes are in F16CARRY) *)
         rw_cells rsegs m (A + 256)
           [C8 (Z_to_bv 64 (fr + 256)); C8 (Z_to_bv 64 (fr + 304)); C8 (Z_to_bv 64 (fr + 272))] /\
         rw_cells rsegs m (fragb fr) [CB 72 (t_FG (g_in g) j)] /\
         addressable m (fragb fr) 72 /\
         addressable m (fr + 256) 2 /\ addressable m (fr + 272) 8 /\ addressable m (fr + 304) 8 /\
         asan_cells m /\ shadow_rw m /\
         bytes_at rsegs m BWA.REAL_BCMP (le8 (wa BWA.BCMP)) /\ bytes_at rsegs m BWA.REAL_MEMCMP (le8 (wa MCA.MEMCMP)) /\
         bytes_at rsegs m BWA.GOT_CF (le8 (wa BWA.CF)) /\
         bytes_at rsegs m (BWA.CF + 254) [Z_to_bv 8 1] /\ bytes_at rsegs m (BWA.CF + 255) [Z_to_bv 8 1] /\
         (* the F14 bcmp data (pre-call): the before-call copy of the record at fr + 336 and the pointer spills;
            [A+280] = sum_ok of the turn (stored 0x81eb4 / 0x81e00), read by the F14 test 0x820c8 *)
         q64 m (A + 184) (fr + 336) /\ q64 m (A + 192) (fragb fr) /\ q64 m (A + 280) v280 /\
         bytes_at rsegs m (fr + 336) (t_FG (g_in g) j) /\ addressable m (fr + 336) 72 /\
         (* the five loop-invariant frag spill pointers, threaded for F15 (FLV) *)
         q64 m (A + 80) (fragb fr + 15) /\ q64 m (A + 88) (fragb fr + 19) /\ q64 m (A + 96) (fragb fr + 8) /\
         q64 m (A + 272) (fr + 272) /\ q64 m (A + 264) (fr + 304) /\
         (* the fields of the F16 / F17 entry cuts that F13-F15 carry unchanged *)
         F16CARRY g j fr phi A regs m /\ IFS1 g fr j regs m)
    c.
Definition Inv_A82138 (g : ghost) (c : config) : Prop := exists j, Inv_A82138_at g j c.
(* F13 exit / F14 entry (0x820bc, post-call): both frame arms, as at 0x820a0. *)
Definition Inv_A82154_at (g : ghost) (j : nat) (c : config) : Prop :=
  exists phi, CUTST g 0x82154 (hb1 phi (AC.a_size (flen g j)))
    (fun fr regs m =>
       g_n g < 2 ^ 26 /\ (j <= 255)%nat /\ HB m phi (flen g j) /\ FLSI g j fr regs m /\ LK g fr j regs m /\
       exists (A v280 : Z),
         rg regs 9 A /\ rg regs 10 (RcFrag.fg_ret (frcl g j fr phi)) /\
         0 <= A < 2 ^ 64 /\ 0 <= v280 < 2 ^ 64 /\ v280 = b2z (t_sum_ok (g_in g) j) /\
         (phi + 50 <= fr \/ fr + FRAME_BYTES <= phi) /\
         (phi + 50 <= AC.aspZ regs - FGA.REAC_CTRL_IDENTITY_FRAGMENT_K \/ AC.aspZ regs <= phi) /\
         (* the bcmp operands of F14: the before-call copy and the record itself *)
         q64 m (A + 184) (fr + 336) /\ q64 m (A + 192) (fragb fr) /\ q64 m (A + 280) v280 /\
         bytes_at rsegs m (fr + 336) (t_FG (g_in g) j) /\ addressable m (fr + 336) 72 /\
         bytes_at rsegs m (fragb fr) (frrec g j fr phi) /\ addressable m (fragb fr) 72 /\
         bytes_at rsegs m BWA.REAL_BCMP (le8 (wa BWA.BCMP)) /\ bytes_at rsegs m BWA.REAL_MEMCMP (le8 (wa MCA.MEMCMP)) /\
         bytes_at rsegs m BWA.GOT_CF (le8 (wa BWA.CF)) /\
         bytes_at rsegs m (BWA.CF + 254) [Z_to_bv 8 1] /\ bytes_at rsegs m (BWA.CF + 255) [Z_to_bv 8 1] /\
         asan_cells m /\ shadow_rw m /\
         rw_cells rsegs m (A + 256)
           [C8 (Z_to_bv 64 (fr + 256)); C8 (Z_to_bv 64 (fr + 304)); C8 (Z_to_bv 64 (fr + 272))] /\
         q64 m (A + 80) (fragb fr + 15) /\ q64 m (A + 88) (fragb fr + 19) /\ q64 m (A + 96) (fragb fr + 8) /\
         q64 m (A + 272) (fr + 272) /\ q64 m (A + 264) (fr + 304) /\
         FGA.fg_mem (fragb fr) (fr + 256) (fr + 272) (fr + 304) (t_FG (g_in g) j) (t_g (g_in g) j)
           (frcl g j fr phi) m /\
         F16CARRY g j fr phi A regs m /\ IFS2 g fr j regs m)
    c.
Definition Inv_A82154 (g : ghost) (c : config) : Prop := exists j, Inv_A82154_at g j c.
(* The shared tail of the two F14 exit cuts: the record data, the spills and the runtime cells the later segments
   read. v is the a0 value at the cut, w280 the value of [A+280] (sum_ok of the turn).
   The frag range is unchanged on v1.9 (fr + 2768, 72 bytes), see Inv_A81b80. *)
Definition f14_tail (g : ghost) (j : nat) (fr phi : Z) (regs : bvmap 5 word) (m : word -> option byte)
    (A v w280 : Z) : Prop :=
  rg regs 9 A /\ rg regs 25 (RcFrag.fg_ret (frcl g j fr phi)) /\ rg regs 10 v /\
  asan_cells m /\ shadow_rw m /\
  0 <= A < 2 ^ 64 /\ 0 <= w280 < 2 ^ 64 /\ w280 = b2z (t_sum_ok (g_in g) j) /\
  (phi + 50 <= fr \/ fr + FRAME_BYTES <= phi) /\
  (phi + 50 <= AC.aspZ regs - FGA.REAC_CTRL_IDENTITY_FRAGMENT_K \/ AC.aspZ regs <= phi) /\
  stk rsegs m (AC.aspZ regs - FGA.REAC_CTRL_IDENTITY_FRAGMENT_K) (AC.aspZ regs) /\
  q64 m (A + 184) (fr + 336) /\ q64 m (A + 192) (fragb fr) /\ q64 m (A + 280) w280 /\
  bytes_at rsegs m (fr + 336) (t_FG (g_in g) j) /\ addressable m (fr + 336) 72 /\
  bytes_at rsegs m (fragb fr) (frrec g j fr phi) /\ addressable m (fragb fr) 72 /\
  bytes_at rsegs m BWA.REAL_BCMP (le8 (wa BWA.BCMP)) /\ bytes_at rsegs m BWA.REAL_MEMCMP (le8 (wa MCA.MEMCMP)) /\
  bytes_at rsegs m BWA.GOT_CF (le8 (wa BWA.CF)) /\
  bytes_at rsegs m (BWA.CF + 254) [Z_to_bv 8 1] /\ bytes_at rsegs m (BWA.CF + 255) [Z_to_bv 8 1] /\
  rw_cells rsegs m (A + 256)
    [C8 (Z_to_bv 64 (fr + 256)); C8 (Z_to_bv 64 (fr + 304)); C8 (Z_to_bv 64 (fr + 272))] /\
  FGA.fg_mem (fragb fr) (fr + 256) (fr + 272) (fr + 304) (t_FG (g_in g) j) (t_g (g_in g) j) (frcl g j fr phi) m /\
  F16CARRY g j fr phi A regs m.
(* F14 exit / F15 entry (0x820dc, the bcmp fall-through: [A+280] = 0 and a0 = the compare result). *)
Definition Inv_A82174_at (g : ghost) (j : nat) (c : config) : Prop :=
  exists phi, CUTST g 0x82174 (hb1 phi (AC.a_size (flen g j)))
    (fun fr regs m =>
       g_n g < 2 ^ 26 /\ (j <= 255)%nat /\ HB m phi (flen g j) /\ FLSI g j fr regs m /\ LK g fr j regs m /\
       FLV g fr j regs m /\
       exists (vcmp A : Z),
         SFA.memcmp_model (t_FG (g_in g) j) (frrec g j fr phi) 72 = Some vcmp /\
         f14_tail g j fr phi regs m A vcmp 0 /\ IFS2 g fr j regs m)
    c.
Definition Inv_A82174 (g : ghost) (c : config) : Prop := exists j, Inv_A82174_at g j c.
(* F15 internal split (found by the B6 prover): the identity_fragment-result block 0x820e0 (`820e0-820e4 >
   821c4, 820e8`: rf = 1 -> 0x821c4, else continue the ingest checks to 0x82134). Reached from F14 ([A+280] <> 0:
   the bcmp is skipped, a0 = [A+280]) and from F15 ([A+280] = 0: the bcmp fall-through, a0 = 0). a0 is dead there
   (0x820e0 `li a0,1`). Exits to Inv_A822a0 (F15b) or Inv_A821d0 (F16). *)
Definition Inv_A82178_at (g : ghost) (j : nat) (c : config) : Prop :=
  exists phi, CUTST g 0x82178 (hb1 phi (AC.a_size (flen g j)))
    (fun fr regs m =>
       g_n g < 2 ^ 26 /\ (j <= 255)%nat /\ HB m phi (flen g j) /\ FLSI g j fr regs m /\ LK g fr j regs m /\
       FLV g fr j regs m /\
       (exists A v w280 : Z, f14_tail g j fr phi regs m A v w280) /\ IFS2 g fr j regs m)
    c.
Definition Inv_A82178 (g : ghost) (c : config) : Prop := exists j, Inv_A82178_at g j c.
(* F15b exit / F16 entry (0x82134): the turn closes a record. *)
Definition Inv_A821d0_at (g : ghost) (j : nat) (c : config) : Prop :=
  exists phi, CUTST g 0x821d0 (hb1 phi (AC.a_size (flen g j)))
    (fun fr regs m =>
       g_n g < 2 ^ 26 /\ (j <= 255)%nat /\ HB m phi (flen g j) /\ FLSI g j fr regs m /\ LK g fr j regs m /\
       FLV g fr j regs m /\
       (* the fragment call closed a record (s9 = 1 at 0x820e4): the class of the turn is FgClose *)
       t_rf (g_in g) j = 1 /\
       (* loop registers, first turn: a0 = a5 = [A+64] = fragb fr + 15, a1 = 0 (the sum), a2 = pl = fragb fr + 19,
          a3 = pll, a4 = pll + 5 (the down-counter) *)
       rg regs 10 (fragb fr + 15) /\ rg regs 15 (fragb fr + 15) /\ rg regs 11 0 /\
       rg regs 12 (fragb fr + 19) /\ rg regs 13 (f_pll (t_FG (g_in g) j) (t_g (g_in g) j)) /\
       rg regs 14 (f_pll (t_FG (g_in g) j) (t_g (g_in g) j) + 5) /\
       (* the record the fragment call left at fragb fr (= frrec, F13.frcl_fcls), addressable; frag_ok and the
          first-fragment state FSj (v1.9: [A+104] / [A+112] / first.sroa.7, see FSb) with FI, of the state before
          the call (v1.9 F16 reads it at 0x821cc / 0x82210 / 0x82218 / 0x82250) *)
       bytes_at rsegs m (fragb fr) (t_FGf (g_in g) j) /\ addressable m (fragb fr) 72 /\
       frag_ok (t_FG (g_in g) j) /\ FSj g fr j regs m /\
       (* the fragment's address output cell [fr+256] (fg_mem FgClose, pa) *)
       u16 m (fr + 256) (RcFrag.fg_addr (t_FG (g_in g) j) (t_g (g_in g) j)) /\
       (* the identity buffer at fr + 2688 (the ingest's id = [A+144]): some 38 bytes, addressable *)
       (exists idb, bytes_at rsegs m (fr + 2688) idb /\ length idb = 38%nat) /\ addressable m (fr + 2688) 38 /\
       exists A, rg regs 9 A /\
         (* spills F16 reads: [A+208] = fragb fr, [A+256] = fr + 256, [A+144] = fr + 2688 (id) *)
         q64 m (A + 192) (fragb fr) /\ q64 m (A + 256) (fr + 256) /\ q64 m (A + 144) (fr + 2688) /\
         F17CARRY g j fr phi A regs m /\ IFS2 g fr j regs m /\
         (* v1.9, appended last: t0 = n of the turn's first-fragment state, loaded at 0x821cc (`ld t0,112(s1)`)
            before this pc and read by F16 at 0x82220 / 0x82258 with no reload; F15b (CHANGED) is its producer. *)
         rg regs 5 (fs_n (fst_at (g_in g) j)))
    c.
Definition Inv_A821d0 (g : ghost) (c : config) : Prop := exists j, Inv_A821d0_at g j c.
(* ---- F17 / F17b / F18 / F19 entries (0x821c0, 0x821c4, 0x8233c, 0x82354), push 6c: a Theorem Labs lane's Seg/F17.v (a version not in this delivery)
   Inv_A821c0_loc / Inv_A821c4_loc and Seg/F18.v (a version not in this delivery) Inv_A8233c_loc / Inv_A82354_loc / rec_inv (
   from a working branch 30bdb238d5a, seg_F17 / seg_F17b / seg_F18 / seg_F19 Qed). a Theorem Labs lane's `exists (j : nat)` is the official index j
   (Inv_A8229c := exists j, Inv_A8229c_at g j); the bodies are written on the FCUT skeleton with phi named (as in
   a Theorem Labs lane's B8Cuts.v, not in this delivery), so three things differ from a Theorem Labs lane's text: the live list is `hb1 phi (AC.a_size (flen g j))` (that text:
   `hb1 phi (flen g j)`; equal when 50 <= flen g j, and only the a_size form is the malloc block on the short arm,
   where flen g j may be 0), FLSI is conjoined (every frame-loop cut carries it), and the short-arm guards below
   (push 6c5b). BWA.BCMP_WRAP_K = 4560 is a Theorem Labs lane's F18.v local BCMP_WRAP_K.
   a Theorem Labs lane's comment (F17.v): the cut adds to the skeleton s7 = Phi (the record base, the heap block of HB), the ingest
   result in a0 nonneg (for `bltz a0,82b34` not taken; only at 0x821c0), the record addressable for its first 40
   bytes and readable for its first 38, the spill cells the body reads ([s1+232] the flag word, [s1+192] = Phi+18,
   [s1+176] reloaded into s9), the first-fragment spill window [s1+88, s1+120) in high app memory, with the record
   bytes [phi, phi+50) apart from it; for the F18 entry it carries the [s1+240] word, s8 = t_k, rec_inv, the
   placement of [phi, phi+50) against the wrapper_bcmp scratch [sp-K, sp), and the two 6-byte compare operands
   (fr + 186 vs phi, fr + 180 vs phi + 6) with their 6-byte match and addressability; for the F20 entry
   s6 = phi + 18 and the frame-pointer spills [s1+136] = fr + 128, [s1+120] = fr + 160, [s1+176] = fr + 64. *)
(* Short-arm guards (push 6c5b, a Theorem Labs lane via a Theorem Labs lane 00:24Z). 0x821c0, 0x821c4 and 0x8233c are reached on both
   arms of the turn: the short arm (len_j <= 49 or 0; 0x81df4 `li s6,0`, 0x81dfc [A+240] = 0) and the long arm.
   0x821c4 takes the opens_record body (0x821d8) only when `[A+232] | s4` is 0, and [A+232] = 1 exactly when
   len_j < 50 (0x81db0 `sltiu s6,s2,50`, 0x81db8; no other store in the loop), so the cut pins [A+232] (a1 had
   `exists v232`); 0x8233c falls into the two bcmp calls (0x82344 .. 0x8236c) only when [A+240] <> 0, and
   [A+240] = t_8819 (0x81db4 on the long arm, 0 at 0x81dfc / 0x81e0c). So: s6 is `if t_big then phi + 18 else 0`
   (a1: phi + 18), the record facts (phi's first 50 bytes addressable, rec_inv, the phi + 50 placements) are under
   `50 <= flen g j ->`, the [A+240] word is pinned by t_8819 in a Theorem Labs lane's guard form, and the two compare operands
   with their 6-byte matches are under `t_8819 (g_in g) j = true ->`. 0x82354 / 0x8236c (after the first bcmp,
   so t_8819 = true and 50 <= len_j) keep two Theorem Labs lanes' unguarded text.
   Round 6 (a Theorem Labs lane's cut request, F17b's store arm): `addressable m phi 40` became `addressable m phi 50` on
   this cut and on Inv_A822a0_at, same position. v1.9's F17b memcpy 0x823d4 reads phi + 27 for gg[26] in [1, 22]
   bytes, i.e. up to phi + 49. Origin: no upstream cut carries the 40; F15b proves it locally (Seg/F15.v:745-747)
   from the heap-block fact HB m phi (flen g j), which is a conjunct of this very cut: addressable m phi
   (AC.a_size (flen g j)) with a_size flen = flen >= 50, so addressable_sub gives 50 the same way. *)
Definition Inv_A8229c_at (g : ghost) (j : nat) (c : config) : Prop :=
  exists phi, CUTST g 0x8229c (hb1 phi (AC.a_size (flen g j)))
    (fun fr regs m =>
       g_n g < 2 ^ 26 /\ (j <= 255)%nat /\ HB m phi (flen g j) /\ FLSI g j fr regs m /\ LK g fr j regs m /\
       rg regs 23 phi /\ rg regs 22 (if t_big (g_in g) j then phi + 18 else 0) /\
       (50 <= flen g j -> addressable m phi 50 /\ (exists rb, bytes_at rsegs m phi rb /\ (38 <= length rb)%nat)) /\
       (exists v0, rg regs 10 v0 /\ 0 <= v0 < 2 ^ 63) /\
       (exists A, rg regs 9 A /\
          q64 m (A + 232) (if t_big (g_in g) j then 0 else 1) /\
          q64 m (A + 200) (phi + 18) /\
          q64 m (A + 136) (fr + 128) /\ q64 m (A + 120) (fr + 160) /\ q64 m (A + 176) (fr + 64) /\
          (forall a, A + 88 <= a < A + 120 -> HIGHMEM_BEG <= a < APPMEM_END) /\
          (exists w240, q64 m (A + 240) w240 /\ 0 <= w240 < 2 ^ 64 /\
             (t_8819 (g_in g) j = true -> w240 <> 0) /\ (t_8819 (g_in g) j = false -> w240 = 0)) /\
          rg regs 24 (t_k (g_in g) j) /\
          (50 <= flen g j ->
             rec_inv0 g j fr phi A m /\
             (phi + 50 <= AC.aspZ regs - BWA.BCMP_WRAP_K \/ AC.aspZ regs <= phi) /\
             (phi + 50 <= A + 88 \/ A + 120 <= phi)) /\
          (t_8819 (g_in g) j = true ->
             rec_parse g j fr phi m /\
             (exists (ls rs : list byte),
                q64 m (A + 72) (fr + 186) /\ bytes_at rsegs m (fr + 186) ls /\ (6 <= length ls)%nat /\
                bytes_at rsegs m phi rs /\ (6 <= length rs)%nat /\ SFA.memcmp_model ls rs 6 = Some 0 /\
                addressable m (fr + 186) 6) /\
             (exists (ls2 rs2 : list byte),
                q64 m (A + 64) (fr + 180) /\ bytes_at rsegs m (fr + 180) ls2 /\ (6 <= length ls2)%nat /\
                bytes_at rsegs m (phi + 6) rs2 /\ (6 <= length rs2)%nat /\ SFA.memcmp_model ls2 rs2 6 = Some 0 /\
                addressable m (fr + 180) 6))) /\
       (* push 6c8: what F18's taken exit to 0x826b0 needs and F17 does not write (see Inv_A823e8_at) *)
       rg regs 18 (flen g j) /\
       (50 <= flen g j ->
          bytes_at rsegs m phi (t_g (g_in g) j) /\ bytes_at rsegs m phi (t_phi (g_in g) j) /\
          Z.of_nat (length (t_phi (g_in g) j)) <= flen g j) /\
       spill regs m 152 (b2z (t_tfill (g_in g) j)) /\ spill regs m 280 (b2z (t_sum_ok (g_in g) j)) /\
       IFS3 g fr j regs m /\ rg regs 20 (1 - b2z (t_sum_ok (g_in g) j)))
    c.
Definition Inv_A8229c (g : ghost) (c : config) : Prop := exists j, Inv_A8229c_at g j c.
(* F17 internal split (found by the B6 prover): the opens_record entry block 0x821c4 (`821c4-821cc >
   821d8, 821d0`), reached from F15 (rf = 1 at 0x820e0, which never runs the bltz at 0x821c0) and from F17's
   bltz fall-through. a Theorem Labs lane's Inv_A821c4_loc: Inv_A8229c_at without the one conjunct the bltz consumes (the ingest
   result a0 nonneg); short-arm guards as Inv_A8229c_at. *)
Definition Inv_A822a0_at (g : ghost) (j : nat) (c : config) : Prop :=
  exists phi, CUTST g 0x822a0 (hb1 phi (AC.a_size (flen g j)))
    (fun fr regs m =>
       g_n g < 2 ^ 26 /\ (j <= 255)%nat /\ HB m phi (flen g j) /\ FLSI g j fr regs m /\ LK g fr j regs m /\
       rg regs 23 phi /\ rg regs 22 (if t_big (g_in g) j then phi + 18 else 0) /\
       (50 <= flen g j -> addressable m phi 50 /\ (exists rb, bytes_at rsegs m phi rb /\ (38 <= length rb)%nat)) /\
       (exists A, rg regs 9 A /\
          q64 m (A + 232) (if t_big (g_in g) j then 0 else 1) /\
          q64 m (A + 200) (phi + 18) /\
          q64 m (A + 136) (fr + 128) /\ q64 m (A + 120) (fr + 160) /\ q64 m (A + 176) (fr + 64) /\
          (forall a, A + 88 <= a < A + 120 -> HIGHMEM_BEG <= a < APPMEM_END) /\
          (exists w240, q64 m (A + 240) w240 /\ 0 <= w240 < 2 ^ 64 /\
             (t_8819 (g_in g) j = true -> w240 <> 0) /\ (t_8819 (g_in g) j = false -> w240 = 0)) /\
          rg regs 24 (t_k (g_in g) j) /\
          (50 <= flen g j ->
             rec_inv0 g j fr phi A m /\
             (phi + 50 <= AC.aspZ regs - BWA.BCMP_WRAP_K \/ AC.aspZ regs <= phi) /\
             (phi + 50 <= A + 88 \/ A + 120 <= phi)) /\
          (t_8819 (g_in g) j = true ->
             rec_parse g j fr phi m /\
             (exists (ls rs : list byte),
                q64 m (A + 72) (fr + 186) /\ bytes_at rsegs m (fr + 186) ls /\ (6 <= length ls)%nat /\
                bytes_at rsegs m phi rs /\ (6 <= length rs)%nat /\ SFA.memcmp_model ls rs 6 = Some 0 /\
                addressable m (fr + 186) 6) /\
             (exists (ls2 rs2 : list byte),
                q64 m (A + 64) (fr + 180) /\ bytes_at rsegs m (fr + 180) ls2 /\ (6 <= length ls2)%nat /\
                bytes_at rsegs m (phi + 6) rs2 /\ (6 <= length rs2)%nat /\ SFA.memcmp_model ls2 rs2 6 = Some 0 /\
                addressable m (fr + 180) 6))) /\
       (* push 6c8: as Inv_A8229c_at *)
       rg regs 18 (flen g j) /\
       (50 <= flen g j ->
          bytes_at rsegs m phi (t_g (g_in g) j) /\ bytes_at rsegs m phi (t_phi (g_in g) j) /\
          Z.of_nat (length (t_phi (g_in g) j)) <= flen g j) /\
       spill regs m 152 (b2z (t_tfill (g_in g) j)) /\ spill regs m 280 (b2z (t_sum_ok (g_in g) j)) /\
       IFS3 g fr j regs m /\ rg regs 20 (1 - b2z (t_sum_ok (g_in g) j)))
    c.
Definition Inv_A822a0 (g : ghost) (c : config) : Prop := exists j, Inv_A822a0_at g j c.
(* F18 entry (0x8233c), a Theorem Labs lane's Inv_A8233c_loc: the compare operands and the parsed-struct pointer are frame
   addresses stored once in the prologue ([s1+248] = fr + 176, [s1+56] = fr + 186, [s1+48] = fr + 180), so their
   app memory and placement are FRA's; only the shadow-decided facts (addressability) and the record bytes are
   cut conjuncts. Short-arm guards as Inv_A8229c_at: everything the two bcmp calls read is under
   `t_8819 (g_in g) j = true ->`, together with a Theorem Labs lane's `w240 <> 0`. *)
Definition Inv_A823e8_at (g : ghost) (j : nat) (c : config) : Prop :=
  exists phi, CUTST g 0x823e8 (hb1 phi (AC.a_size (flen g j)))
    (fun fr regs m =>
       g_n g < 2 ^ 26 /\ (j <= 255)%nat /\ HB m phi (flen g j) /\ FLSI g j fr regs m /\ LK g fr j regs m /\
       (exists (A w240 : Z),
          rg regs 9 A /\ 0 <= A < 2 ^ 64 /\ AC.aspZ regs <= A /\
          rg regs 23 phi /\ rg regs 24 (t_k (g_in g) j) /\ rg regs 22 (if t_big (g_in g) j then phi + 18 else 0) /\
          (50 <= flen g j -> rec_inv0 g j fr phi A m) /\
          q64 m (A + 136) (fr + 128) /\ q64 m (A + 120) (fr + 160) /\ q64 m (A + 176) (fr + 64) /\
          q64 m (A + 240) w240 /\ 0 <= w240 < 2 ^ 64 /\
          (t_8819 (g_in g) j = false -> w240 = 0) /\
          (t_8819 (g_in g) j = true ->
             w240 <> 0 /\ rec_parse g j fr phi m /\
             exists (ls rs ls2 rs2 : list byte),
               q64 m (A + 72) (fr + 186) /\
               bytes_at rsegs m (fr + 186) ls /\ (6 <= length ls)%nat /\
               bytes_at rsegs m phi rs /\ (6 <= length rs)%nat /\
               SFA.memcmp_model ls rs 6 = Some 0 /\
               addressable m (fr + 186) 6 /\ addressable m phi 6 /\
               (phi + 50 <= AC.aspZ regs - BWA.BCMP_WRAP_K \/ AC.aspZ regs <= phi) /\
               q64 m (A + 64) (fr + 180) /\
               bytes_at rsegs m (fr + 180) ls2 /\ (6 <= length ls2)%nat /\
               bytes_at rsegs m (phi + 6) rs2 /\ (6 <= length rs2)%nat /\
               SFA.memcmp_model ls2 rs2 6 = Some 0 /\
               addressable m (fr + 180) 6 /\ addressable m (phi + 6) 6)) /\
       (* push 6c8 (a Theorem Labs lane's F18 request via a Theorem Labs lane 00:57Z): what the taken exit (0x8233c `beqz [A+240]`
          -> 0x826b0, t_8819 = false) needs for Inv_A8275c_at's FLS: s2 = len_j, s9 = fr + 64 (F17 loads it from
          [A+176] at 0x821d0 / 0x821e8), the record bytes under 50 <= len_j, and the two per-turn spills, which the
          short arm sets to 0 (0x81e00 for [A+280]) and which rec_inv gives only under 50 <= len_j. F17 writes
          neither s2 nor [A+152] / [A+280] nor the record, so Inv_A822a0_at / Inv_A8229c_at carry the same facts
          (all but s9). *)
       rg regs 18 (flen g j) /\ rg regs 25 (fr + 64) /\
       (50 <= flen g j ->
          bytes_at rsegs m phi (t_g (g_in g) j) /\ bytes_at rsegs m phi (t_phi (g_in g) j) /\
          Z.of_nat (length (t_phi (g_in g) j)) <= flen g j) /\
       spill regs m 152 (b2z (t_tfill (g_in g) j)) /\ spill regs m 280 (b2z (t_sum_ok (g_in g) j)) /\
       LT g fr j regs m)
    c.
Definition Inv_A823e8 (g : ghost) (c : config) : Prop := exists j, Inv_A823e8_at g j c.
(* F19 entry (0x82354, after the first wrapper_bcmp: a0 = 0), a Theorem Labs lane's Inv_A82354_loc. *)
Definition Inv_A82400_at (g : ghost) (j : nat) (c : config) : Prop :=
  exists phi, CUTST g 0x82400 (hb1 phi (AC.a_size (flen g j)))
    (fun fr regs m =>
       g_n g < 2 ^ 26 /\ (j <= 255)%nat /\ HB m phi (flen g j) /\ FLSI g j fr regs m /\ LK g fr j regs m /\
       (exists (A : Z) (ls2 rs2 : list byte),
          rg regs 9 A /\ 0 <= A < 2 ^ 64 /\ AC.aspZ regs <= A /\
          rg regs 23 phi /\ rg regs 24 (t_k (g_in g) j) /\ rg regs 10 0 /\ rg regs 22 (phi + 18) /\
          rec_inv g j fr phi A m /\
          q64 m (A + 136) (fr + 128) /\ q64 m (A + 120) (fr + 160) /\ q64 m (A + 176) (fr + 64) /\
          q64 m (A + 64) (fr + 180) /\
          bytes_at rsegs m (fr + 180) ls2 /\ (6 <= length ls2)%nat /\
          bytes_at rsegs m (phi + 6) rs2 /\ (6 <= length rs2)%nat /\
          SFA.memcmp_model ls2 rs2 6 = Some 0 /\
          addressable m (fr + 180) 6 /\ addressable m (phi + 6) 6 /\
          (phi + 50 <= AC.aspZ regs - BWA.BCMP_WRAP_K \/ AC.aspZ regs <= phi)) /\
       (* push 12 group D (a Theorem Labs lane): the five FLS facts of Inv_A82750_at that 0x82354 .. 0x826a4 never writes.
          Unguarded here: this region is reached only through 0x8233c's `bnez [A+240]` arm, so t_8819 and hence
          t_big are true and 50 <= flen g j (rec_inv has it). *)
       rg regs 18 (flen g j) /\ spill regs m 152 (b2z (t_tfill (g_in g) j)) /\
       bytes_at rsegs m phi (t_g (g_in g) j) /\ bytes_at rsegs m phi (t_phi (g_in g) j) /\
       Z.of_nat (length (t_phi (g_in g) j)) <= flen g j /\ LT g fr j regs m)
    c.
Definition Inv_A82400 (g : ghost) (c : config) : Prop := exists j, Inv_A82400_at g j c.
(* F20 entry (0x8236c, the F19/F20 interface), push 6c: a Theorem Labs lane's concretized Seg/F20.v (a version not in this delivery) Inv_A8236c_loc
   (written on a working branch 84eade9b534, seg_F20 Qed; NOT the copy in a Theorem Labs lane's F19.v (not in this delivery), whose [A+248] pointer is existential), on the
   FCUT skeleton (a_size live list, FLSI, as F17-F19). It carries the is_8819 match data plus the frame/record
   state the downstream segments consume: s7 = phi, s4 = s6 = blk = phi + 18 (set 0x81e1c), s8 = k, the [A+280]
   spill and the four frame-pointer spills [A+248] = fr + 176 (set at 0x812f0-0x812f4) / [A+136] / [A+120] /
   [A+176] (set once at 0x812dc-0x812ec), so the u16 the compare at 0x823b0 reads sits at fr + 196. *)
Definition Inv_A82418_at (g : ghost) (j : nat) (c : config) : Prop :=
  exists phi, CUTST g 0x82418 (hb1 phi (AC.a_size (flen g j)))
    (fun fr regs m =>
       g_n g < 2 ^ 26 /\ (j <= 255)%nat /\ HB m phi (flen g j) /\ FLSI g j fr regs m /\ LK g fr j regs m /\
       rg regs 23 phi /\ rg regs 20 (phi + 18) /\ rg regs 22 (phi + 18) /\ rg regs 24 (t_k (g_in g) j) /\
       rg regs 10 0 /\
       0 < phi /\ phi + 50 <= 2 ^ 64 /\ 50 <= flen g j /\ 0 <= t_k (g_in g) j < 2 ^ 64 /\
       bytes_at rsegs m (phi + 18) (t_blk (g_in g) j) /\
       bytes_at rsegs m (phi + 34) (RcFrag.bsl (t_g (g_in g) j) 34 6) /\
       spill regs m 280 (b2z (t_sum_ok (g_in g) j)) /\
       spill regs m 136 (fr + 128) /\ spill regs m 120 (fr + 160) /\ spill regs m 176 (fr + 64) /\
       (exists v14 v15 v16 v17 field16,
          spill regs m 248 (fr + 176) /\
          u16 m (fr + 196) field16 /\
          b8 m (phi + 14) v14 /\ b8 m (phi + 15) v15 /\
          b8 m (phi + 16) v16 /\ b8 m (phi + 17) v17 /\
          0 <= v14 < 256 /\ 0 <= v15 < 256 /\ 0 <= v16 < 256 /\ 0 <= v17 < 256 /\
          b8 m (Z.shiftr (phi + 14) 3 + ASAN_K) 0 /\
          b8 m (Z.shiftr (phi + 15) 3 + ASAN_K) 0 /\
          b8 m (Z.shiftr (phi + 16) 3 + ASAN_K) 0 /\
          b8 m (Z.shiftr (phi + 17) 3 + ASAN_K) 0 /\
          field16 = v14 + 256 * v15 /\
          (if v16 =? 0 then (if v17 =? 0 then 1 else 0) else 0) = (if t_k (g_in g) j =? 1 then 1 else 0)) /\
       (* push 12 group D (a Theorem Labs lane): the five FLS facts, see 0x82354 *)
       rg regs 18 (flen g j) /\ spill regs m 152 (b2z (t_tfill (g_in g) j)) /\
       bytes_at rsegs m phi (t_g (g_in g) j) /\ bytes_at rsegs m phi (t_phi (g_in g) j) /\
       Z.of_nat (length (t_phi (g_in g) j)) <= flen g j /\ LT g fr j regs m)
    c.
Definition Inv_A82418 (g : ghost) (c : config) : Prop := exists j, Inv_A82418_at g j c.
(* F21 entry (0x82408), push 6c8: a Theorem Labs lane's Seg/F20.v (a version not in this delivery; written on a working branch 84eade9b534) Inv_A82408_loc (seg_F20's
   exit, Qed), on the FCUT skeleton (a_size live list, FLSI, as F20). After the CKV call: a0 is the call's result
   (0 exactly when the block sum is 0); the record state is unchanged (the callee wrote only its own 16 stack
   bytes). Reached only after 0x8236c, so t_8819 = true and 50 <= len_j: no short-arm guard. *)
Definition Inv_A824b4_at (g : ghost) (j : nat) (c : config) : Prop :=
  exists phi, CUTST g 0x824b4 (hb1 phi (AC.a_size (flen g j)))
    (fun fr regs m =>
       g_n g < 2 ^ 26 /\ (j <= 255)%nat /\ HB m phi (flen g j) /\ FLSI g j fr regs m /\ LK g fr j regs m /\
       rg regs 10 (if RcModel.blocksum (t_blk (g_in g) j) =? 0 then 0 else -1) /\
       rg regs 23 phi /\ rg regs 20 (phi + 18) /\ rg regs 22 (phi + 18) /\ rg regs 24 (t_k (g_in g) j) /\
       0 < phi /\ phi + 50 <= 2 ^ 64 /\ 50 <= flen g j /\ 0 <= t_k (g_in g) j < 2 ^ 64 /\
       bytes_at rsegs m (phi + 18) (t_blk (g_in g) j) /\
       bytes_at rsegs m (phi + 34) (RcFrag.bsl (t_g (g_in g) j) 34 6) /\
       spill regs m 280 (b2z (t_sum_ok (g_in g) j)) /\
       spill regs m 136 (fr + 128) /\ spill regs m 120 (fr + 160) /\ spill regs m 176 (fr + 64) /\
       (* push 12 group D (a Theorem Labs lane): the five FLS facts, see 0x82354 *)
       rg regs 18 (flen g j) /\ spill regs m 152 (b2z (t_tfill (g_in g) j)) /\
       bytes_at rsegs m phi (t_g (g_in g) j) /\ bytes_at rsegs m phi (t_phi (g_in g) j) /\
       Z.of_nat (length (t_phi (g_in g) j)) <= flen g j /\ LT g fr j regs m)
    c.
Definition Inv_A824b4 (g : ghost) (c : config) : Prop := exists j, Inv_A824b4_at g j c.
(* ---- F22-F28 entries (0x824a8 .. 0x825b0, and F28's internal split 0x82628), push 6c8: a Theorem Labs lane's
   Seg/B7Cuts.v (a working branch 2c8bf01f57e), the head-amp record check and the inlined check_ports. All of
   B7 is taken (not only F26 / F27), so that each body's producer has its own entry: F25 produces 0x82548 from
   0x82528, and so on back to F21's exits 0x824a8 / 0x824f4 (a Theorem Labs lane's F21 exits into a Theorem Labs lane's texts). a Theorem Labs lane's B7CUT is
   written on the official skeleton: the live list is `hb1 phi (AC.a_size (flen g j))` (a Theorem Labs lane: `flen g j`; equal,
   B7K has 50 <= flen g j: the region is reached only after 0x8236c) and FLSI is conjoined. a Theorem Labs lane's 0x826a4 body is
   NOT taken: 0x826a4 is a Theorem Labs lane's F29 entry (push 6c5), and F28 must give that one (see the push 6c report). *)
(* The frame-pointer spills the region reads (a Theorem Labs lane; FLSI has them too). *)
Definition B7SPL (fr : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  spill regs m 136 (fr + 128) /\ spill regs m 120 (fr + 160) /\ spill regs m 176 (fr + 64).
(* Facts kept through the whole region: the frame-loop state, s7 = phi (the frame copy), s6 = blk = phi + 18
   (set 0x81e1c; the frame is at least 50 bytes here), the 32 block bytes, the sum_ok spill, s8 = k, the spills. *)
Definition B7K (g : ghost) (j : nat) (phi fr : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  LK g fr j regs m /\ rg regs 23 phi /\ rg regs 22 (phi + 18) /\
  0 < phi /\ phi + 50 <= 2 ^ 64 /\ 50 <= flen g j /\
  bytes_at rsegs m (phi + 18) (t_blk (g_in g) j) /\
  spill regs m 280 (b2z (t_sum_ok (g_in g) j)) /\ rg regs 24 (t_k (g_in g) j) /\
  (* push 12 group D (a Theorem Labs lane's cutreq-826a4-and-flsh.md item 2 (a working note, not in this delivery)): the five facts of Inv_A82750_at's FLS that no
     instruction of 0x824a8 .. 0x826a4 writes (s2 = len_j, the [A + 152] tfill spill and the record at phi), so
     F28 can hand them on. Unguarded: B7K already has 50 <= flen g j, where FLS's `if t_big then phi + 18 else 0`
     is phi + 18 and its `50 <= flen g j ->` group is unconditional (push 12 group C). *)
  rg regs 18 (flen g j) /\ spill regs m 152 (b2z (t_tfill (g_in g) j)) /\
  bytes_at rsegs m phi (t_g (g_in g) j) /\ bytes_at rsegs m phi (t_phi (g_in g) j) /\
  Z.of_nat (length (t_phi (g_in g) j)) <= flen g j /\
  (* push 12 group B: LT = IFS g fr (S j), carried from 0x8233c (F17 makes it) to Inv_A82750_at. *)
  LT g fr j regs m /\
  B7SPL fr regs m.
(* A B7 cut: the FCUT skeleton with phi passed to the body. *)
Definition B7CUT (g : ghost) (pc : Z) (j : nat) (P : Z -> Z -> bvmap 5 word -> (word -> option byte) -> Prop)
    (c : config) : Prop :=
  exists phi, CUTST g pc (hb1 phi (AC.a_size (flen g j)))
    (fun fr regs m => g_n g < 2 ^ 26 /\ (j <= 255)%nat /\ HB m phi (flen g j) /\ FLSI g j fr regs m /\
                      B7K g j phi fr regs m /\ P phi fr regs m) c.
(* F22 entry, 0x824a8 (record-sum loop head, first turn): a0 = a2 = phi + 34, a3 = 6, a1 = 0; the six record
   bytes; frame[18] = 4, frame[19] = 3 (the branches 0x82474 / 0x82494 fell through). *)
Definition Inv_A82554_at (g : ghost) (j : nat) (c : config) : Prop :=
  B7CUT g 0x82554 j (fun phi fr regs m =>
    bytes_at rsegs m (phi + 34) (RcFrag.bsl (t_g (g_in g) j) 34 6) /\
    RcParse.cp_v (t_g (g_in g) j) 18 = 4 /\ RcParse.cp_v (t_g (g_in g) j) 19 = 3 /\
    rg regs 10 (phi + 34) /\ rg regs 12 (phi + 34) /\ rg regs 13 6 /\ rg regs 11 0) c.
Definition Inv_A82554 (g : ghost) (c : config) : Prop := exists j, Inv_A82554_at g j c.
(* F23 entry, 0x824f4 (reac_ctrl_headamp_record_verify returned): a0 = the result, s4 = want_v, both t_want_v. *)
Definition Inv_A825a0_at (g : ghost) (j : nat) (c : config) : Prop :=
  B7CUT g 0x825a0 j (fun phi fr regs m =>
    rg regs 10 (t_want_v (g_in g) j) /\ rg regs 20 (t_want_v (g_in g) j)) c.
Definition Inv_A825a0 (g : ghost) (c : config) : Prop := exists j, Inv_A825a0_at g j c.
(* F24 entry, 0x8251c (after the 12-byte copy of {-7, -7, -7} into ports): s4 = q = fr + 128, the three words,
   and the ports bytes addressable (shadow 00 04 written at 0x824f8 / 0x82500). *)
Definition Inv_A825c8_at (g : ghost) (j : nat) (c : config) : Prop :=
  B7CUT g 0x825c8 j (fun phi fr regs m =>
    rg regs 20 (fr + 128) /\
    u32 m (fr + 128) (-7) /\ u32 m (fr + 132) (-7) /\ u32 m (fr + 136) (-7) /\
    addressable m (fr + 128) 12) c.
Definition Inv_A825c8 (g : ghost) (c : config) : Prop := exists j, Inv_A825c8_at g j c.
(* F25 entry, 0x82528 (after reac_ports_parse): a0 = r = t_rp, the ports words as PORTS. *)
Definition Inv_A825d4_at (g : ghost) (j : nat) (c : config) : Prop :=
  B7CUT g 0x825d4 j (fun phi fr regs m =>
    rg regs 10 (t_rp (g_in g) j) /\ PORTS g fr j m /\ addressable m (fr + 128) 12) c.
Definition Inv_A825d4 (g : ghost) (c : config) : Prop := exists j, Inv_A825d4_at g j c.
(* F26 entry, 0x82548 (after reac_ports_unknown(blk, &first)): s9 = r, a0 = unk = t_unk, first = t_first
   (shadow 01 written at 0x82530). *)
Definition Inv_A825f4_at (g : ghost) (j : nat) (c : config) : Prop :=
  B7CUT g 0x825f4 j (fun phi fr regs m =>
    rg regs 25 (t_rp (g_in g) j) /\ rg regs 10 (t_unk (g_in g) j) /\
    PORTS g fr j m /\ FIRSTb g fr j m /\
    addressable m (fr + 128) 12 /\ addressable m (fr + 160) 1) c.
Definition Inv_A825f4 (g : ghost) (c : config) : Prop := exists j, Inv_A825f4_at g j c.
(* F27 entry, 0x82558 (after reac_ports_unknown(blk, NULL)): s4 = unk, a0 = the second count (the same value). *)
Definition Inv_A82604_at (g : ghost) (j : nat) (c : config) : Prop :=
  B7CUT g 0x82604 j (fun phi fr regs m =>
    rg regs 25 (t_rp (g_in g) j) /\ rg regs 20 (t_unk (g_in g) j) /\ rg regs 10 (t_unk (g_in g) j) /\
    PORTS g fr j m /\ FIRSTb g fr j m /\
    addressable m (fr + 128) 12 /\ addressable m (fr + 160) 1) c.
Definition Inv_A82604 (g : ghost) (c : config) : Prop := exists j, Inv_A82604_at g j c.
(* F28 entry, 0x825b0 (port-slot loop head, first turn; reached only when r = 0): t2 = q = fr + 128, s4 = unk,
   the loop registers a0 = a4 = blk + 8, a5 = 12, a1 = a2 = a3 = a6 = 0. *)
Definition Inv_A8265c_at (g : ghost) (j : nat) (c : config) : Prop :=
  B7CUT g 0x8265c j (fun phi fr regs m =>
    t_rp (g_in g) j = 0 /\ 0 <= t_unk (g_in g) j /\ rg regs 20 (t_unk (g_in g) j) /\ rg regs 7 (fr + 128) /\
    PORTS g fr j m /\ FIRSTb g fr j m /\
    rg regs 10 (phi + 26) /\ rg regs 14 (phi + 26) /\ rg regs 15 12 /\
    rg regs 11 0 /\ rg regs 12 0 /\ rg regs 13 0 /\ rg regs 16 0) c.
Definition Inv_A8265c (g : ghost) (c : config) : Prop := exists j, Inv_A8265c_at g j c.
(* Inside F28 (F28a | F28b), 0x82628 (the port-slot loop has run its 12 turns over blk[8 .. 20)): a2 = the count
   of codes {00, 02}, a1 = the count of code 01, a3 = the count of code 03, a7 = the first code >= 4 (0 if none).
   New cut. *)
Definition Inv_A826d4_at (g : ghost) (j : nat) (c : config) : Prop :=
  B7CUT g 0x826d4 j (fun phi fr regs m =>
    t_rp (g_in g) j = 0 /\ 0 <= t_unk (g_in g) j /\ rg regs 20 (t_unk (g_in g) j) /\ rg regs 7 (fr + 128) /\
    PORTS g fr j m /\ FIRSTb g fr j m /\
    rg regs 12 (RcLeaf.n_in (t_pbs (g_in g) j)) /\ rg regs 11 (RcLeaf.n_out (t_pbs (g_in g) j)) /\
    rg regs 13 (RcLeaf.cnt is_empty (t_pbs (g_in g) j) 12) /\
    rg regs 17 (RcPorts.pu_first (t_pbs (g_in g) j) 12)) c.
Definition Inv_A826d4 (g : ghost) (c : config) : Prop := exists j, Inv_A826d4_at g j c.
(* ---- F29-F38 (0x826a4 .. 0x82894), push 6c: a Theorem Labs lane's Seg/B8Cuts.v (not in this delivery) (a working branch 4eed0e3747c), one
   body per segment boundary, so the exit cut of a segment and the entry cut of its neighbour are the same term.
   Each is the FCUT skeleton written out (phi named, since FLS / FLSX / RL take it), then LK, the frame-loop
   pass-through FLS (FLSX from 0x827b0 on), the facts the batch's instructions read, and last the hand-on bundle
   LT. Seven boundaries had no cut before (0x82754, 0x8281c, 0x827f4, 0x82810, 0x828b8, 0x82814, 0x82820), and
   0x827f0 now carries the row index i like 0x827c0 / 0x827dc. *)
(* 0x826a4 (F28's exit, F29's entry; both paths of check_ports load s9 = [A+176] = fr + 64 before it). LK and the
   frame-loop pass-through only: 0x82750-0x82758 are `sb s11,16/17/20(s3)` (frame shadow). *)
Definition Inv_A82750_at (g : ghost) (j : nat) (c : config) : Prop :=
  exists phi, CUTST g 0x82750 (hb1 phi (AC.a_size (flen g j)))
    (fun fr regs m => g_n g < 2 ^ 26 /\ (j <= 255)%nat /\ HB m phi (flen g j) /\ FLSI g j fr regs m /\
       (LK g fr j regs m /\ FLS g j phi fr regs m /\ LT g fr j regs m)) c.
Definition Inv_A82750 (g : ghost) (c : config) : Prop := exists j, Inv_A82750_at g j c.
(* 0x826b0 (F29's exit, F30's entry). F30 reads from the pass-through: s7 = Phi, s2 = len_j, the 50 bytes at Phi
   and 0 < Phi, 50 <= len_j (the classify callee's premise), [A+160] = fr + 528, [A+168] = fr + 2624,
   [A+200] = fr + 448. *)
Definition Inv_A8275c_at (g : ghost) (j : nat) (c : config) : Prop :=
  exists phi, CUTST g 0x8275c (hb1 phi (AC.a_size (flen g j)))
    (fun fr regs m => g_n g < 2 ^ 26 /\ (j <= 255)%nat /\ HB m phi (flen g j) /\ FLSI g j fr regs m /\
       (LK g fr j regs m /\ FLS g j phi fr regs m /\ LT g fr j regs m)) c.
Definition Inv_A8275c (g : ghost) (c : config) : Prop := exists j, Inv_A8275c_at g j c.
(* 0x826ec (F30's exit, F31's entry; reac_ctrl_classify_box_frame returned): a0 = the classify return value, the
   36 output bytes at o = fr + 448, [o+4, o+10) addressable (the bcmp wrapper's premise), the event word at
   fr + 528. *)
Definition Inv_A82798_at (g : ghost) (j : nat) (c : config) : Prop :=
  exists phi, CUTST g 0x82798 (hb1 phi (AC.a_size (flen g j)))
    (fun fr regs m => g_n g < 2 ^ 26 /\ (j <= 255)%nat /\ HB m phi (flen g j) /\ FLSI g j fr regs m /\
       (LK g fr j regs m /\ FLS g j phi fr regs m /\
        rg regs 10 (RcClassify.cl_r (t_cls (g_in g) j)) /\
        bytes_at rsegs m (fr + 448) (t_B (g_in g) j) /\
        addressable m (fr + 452) 6 /\
        (forall e, t_cls (g_in g) j = Some e -> u32 m (fr + 528) e) /\
        LT g fr j regs m)) c.
Definition Inv_A82798 (g : ghost) (c : config) : Prop := exists j, Inv_A82798_at g j c.
(* 0x8272c (F31's exit 1, F32's entry 1; the bcmp wrapper returned): the classify call produced an event, a0 = 0
   exactly when the 6 source bytes of the classify output equal OUR, the event word at fr + 528. *)
Definition Inv_A827d8_at (g : ghost) (j : nat) (c : config) : Prop :=
  exists phi, CUTST g 0x827d8 (hb1 phi (AC.a_size (flen g j)))
    (fun fr regs m => g_n g < 2 ^ 26 /\ (j <= 255)%nat /\ HB m phi (flen g j) /\ FLSI g j fr regs m /\
       (LK g fr j regs m /\ FLS g j phi fr regs m /\
        t_cls (g_in g) j <> None /\
        (getr regs 10 = Z_to_bv 64 0 <-> firstn 6 (skipn 4 (t_B (g_in g) j)) = OUR (g_in g)) /\
        (forall e, t_cls (g_in g) j = Some e -> u32 m (fr + 528) e) /\
        LT g fr j regs m)) c.
Definition Inv_A827d8 (g : ghost) (c : config) : Prop := exists j, Inv_A827d8_at g j c.
(* 0x82754 (F31's exit 2, F32's entry 2; the target of `bnez a0` at 0x826ec, and the fall-through of 0x82750).
   New cut. The pass-through alone: 0x82804 `bne s8,a0` reads s8 = k_j (FLS), 0x82808 reads s7 = Phi, and
   0x82770 / 0x82790 read the bytes at Phi+16 / Phi+17 (FLS); their checks pass because [Phi, Phi + len) is
   addressable (HB). *)
Definition Inv_A82800_at (g : ghost) (j : nat) (c : config) : Prop :=
  exists phi, CUTST g 0x82800 (hb1 phi (AC.a_size (flen g j)))
    (fun fr regs m => g_n g < 2 ^ 26 /\ (j <= 255)%nat /\ HB m phi (flen g j) /\ FLSI g j fr regs m /\
       (LK g fr j regs m /\ FLS g j phi fr regs m /\ LT g fr j regs m)) c.
Definition Inv_A82800 (g : ghost) (c : config) : Prop := exists j, Inv_A82800_at g j c.
(* 0x8281c (F32's exit 1, F36's entry 5; the target of `bne s8,a0` at 0x82758 and of the byte compares at
   0x82778 / 0x82798). New cut. The row is not selected (the wanted row is 0, `li s4,0`); s8 still holds the kind
   on every path to here, so the full FLS holds. *)
Definition Inv_A828c8_at (g : ghost) (j : nat) (c : config) : Prop :=
  exists phi, CUTST g 0x828c8 (hb1 phi (AC.a_size (flen g j)))
    (fun fr regs m => g_n g < 2 ^ 26 /\ (j <= 255)%nat /\ HB m phi (flen g j) /\ FLSI g j fr regs m /\
       (LK g fr j regs m /\ FLS g j phi fr regs m /\
        t_rowsel (g_in g) j = false /\ LT g fr j regs m)) c.
Definition Inv_A828c8 (g : ghost) (c : config) : Prop := exists j, Inv_A828c8_at g j c.
(* 0x827b0 (F32's exit 2, F33's entry; reac_box_catalogue returned): the row path was taken, a0 = BOX_CATALOGUE,
   s8 = fr + 32 (loaded from [A+40] at 0x827a0) and the count word 11 at fr + 32. From here on the bundle is FLSX. *)
Definition Inv_A8285c_at (g : ghost) (j : nat) (c : config) : Prop :=
  exists phi, CUTST g 0x8285c (hb1 phi (AC.a_size (flen g j)))
    (fun fr regs m => g_n g < 2 ^ 26 /\ (j <= 255)%nat /\ HB m phi (flen g j) /\ FLSI g j fr regs m /\
       (LK g fr j regs m /\ FLSX g j phi fr regs m /\
        t_rowsel (g_in g) j = true /\
        rg regs 10 CATA.BOX_CATALOGUE /\ rg regs 24 (fr + 32) /\ q64 m (fr + 32) 11 /\
        LT g fr j regs m)) c.
Definition Inv_A8285c (g : ghost) (c : config) : Prop := exists j, Inv_A8285c_at g j c.
(* 0x827c0 (F33's exit 1 and F36's exit 1, F34's entry; the head of the row loop W00 at row i). The four stores
   0x827c0-0x827cc mark the row slot's 32 bytes usable, so the slot is NOT addressable at this pc. *)
Definition Inv_A8286c_at (g : ghost) (j i : nat) (c : config) : Prop :=
  exists phi, CUTST g 0x8286c (hb1 phi (AC.a_size (flen g j)))
    (fun fr regs m => g_n g < 2 ^ 26 /\ (j <= 255)%nat /\ HB m phi (flen g j) /\ FLSI g j fr regs m /\
       (LK g fr j regs m /\ (i <= 10)%nat /\ RL g j i phi fr regs m /\ LT g fr j regs m)) c.
Definition Inv_A8286c (g : ghost) (c : config) : Prop := exists j i, Inv_A8286c_at g j i c.
(* 0x827dc (F34's exit, F35's entry; declaration_of returned): a0 = 1, the row slot fr + 64 holds row i's
   declaration and its 32 bytes are addressable. *)
Definition Inv_A82888_at (g : ghost) (j i : nat) (c : config) : Prop :=
  exists phi, CUTST g 0x82888 (hb1 phi (AC.a_size (flen g j)))
    (fun fr regs m => g_n g < 2 ^ 26 /\ (j <= 255)%nat /\ HB m phi (flen g j) /\ FLSI g j fr regs m /\
       (LK g fr j regs m /\ (i <= 10)%nat /\ RL g j i phi fr regs m /\
        rg regs 10 1 /\
        bytes_at rsegs m (fr + 64) (decl_i (Z.of_nat i)) /\ addressable m (fr + 64) 32 /\
        LT g fr j regs m)) c.
Definition Inv_A82888 (g : ghost) (c : config) : Prop := exists j i, Inv_A82888_at g j i c.
(* 0x827f0 (F35's exit 1, F36's entry 1; the bcmp wrapper returned): a0 = 0 exactly when the 32 block bytes equal
   row i's declaration; the row slot's bytes and their addressability are kept. *)
Definition Inv_A8289c_at (g : ghost) (j i : nat) (c : config) : Prop :=
  exists phi, CUTST g 0x8289c (hb1 phi (AC.a_size (flen g j)))
    (fun fr regs m => g_n g < 2 ^ 26 /\ (j <= 255)%nat /\ HB m phi (flen g j) /\ FLSI g j fr regs m /\
       (LK g fr j regs m /\ RL g j i phi fr regs m /\
        (getr regs 10 = Z_to_bv 64 0 <-> t_blk (g_in g) j = decl_i (Z.of_nat i)) /\
        bytes_at rsegs m (fr + 64) (decl_i (Z.of_nat i)) /\ addressable m (fr + 64) 32 /\
        LT g fr j regs m)) c.
Definition Inv_A8289c (g : ghost) (c : config) : Prop := exists j i, Inv_A8289c_at g j i c.
(* 0x827f4 (F35's exit 2, F36's entry 2; the fall-through of 0x827f0). New cut. Row i did not match; the slot is
   still addressable here (0x827f4-0x82800 mark it unusable). *)
Definition Inv_A828a0_at (g : ghost) (j i : nat) (c : config) : Prop :=
  exists phi, CUTST g 0x828a0 (hb1 phi (AC.a_size (flen g j)))
    (fun fr regs m => g_n g < 2 ^ 26 /\ (j <= 255)%nat /\ HB m phi (flen g j) /\ FLSI g j fr regs m /\
       (LK g fr j regs m /\ RL g j i phi fr regs m /\
        t_blk (g_in g) j <> decl_i (Z.of_nat i) /\ addressable m (fr + 64) 32 /\
        LT g fr j regs m)) c.
Definition Inv_A828a0 (g : ghost) (c : config) : Prop := exists j i, Inv_A828a0_at g j i c.
(* 0x82810 (F33's exit 2 and F36's exit 3; the target of `beqz a0` at 0x827b0, of `beqz s8` at 0x827b8 and the
   fall-through of `bnez s8` at 0x8280c after row 10). New cut. No row matched: the wanted row is 0. *)
Definition Inv_A828bc_at (g : ghost) (j : nat) (c : config) : Prop :=
  exists phi, CUTST g 0x828bc (hb1 phi (AC.a_size (flen g j)))
    (fun fr regs m => g_n g < 2 ^ 26 /\ (j <= 255)%nat /\ HB m phi (flen g j) /\ FLSI g j fr regs m /\
       (LK g fr j regs m /\ FLSX g j phi fr regs m /\
        t_rowsel (g_in g) j = true /\ t_want_m (g_in g) j = 0 /\ LT g fr j regs m)) c.
Definition Inv_A828bc (g : ghost) (c : config) : Prop := exists j, Inv_A828bc_at g j c.
(* 0x828b8 (F36's exit 2; the target of `beqz a0` at 0x827f0). New cut. Row i matched, so s4 holds the wanted
   row; 0x828b8-0x828c4 mark the row slot's shadow, then `j 82814`. *)
Definition Inv_A82964_at (g : ghost) (j : nat) (c : config) : Prop :=
  exists phi, CUTST g 0x82964 (hb1 phi (AC.a_size (flen g j)))
    (fun fr regs m => g_n g < 2 ^ 26 /\ (j <= 255)%nat /\ HB m phi (flen g j) /\ FLSI g j fr regs m /\
       (LK g fr j regs m /\ FLSX g j phi fr regs m /\
        rg regs 20 (t_want_m (g_in g) j) /\ LT g fr j regs m)) c.
Definition Inv_A82964 (g : ghost) (c : config) : Prop := exists j, Inv_A82964_at g j c.
(* 0x82814 (F36's entry 4; from 0x82810 and 0x828c8). New cut. s4 = the wanted row on both edges. *)
Definition Inv_A828c0_at (g : ghost) (j : nat) (c : config) : Prop :=
  exists phi, CUTST g 0x828c0 (hb1 phi (AC.a_size (flen g j)))
    (fun fr regs m => g_n g < 2 ^ 26 /\ (j <= 255)%nat /\ HB m phi (flen g j) /\ FLSI g j fr regs m /\
       (LK g fr j regs m /\ FLSX g j phi fr regs m /\
        rg regs 20 (t_want_m (g_in g) j) /\ LT g fr j regs m)) c.
Definition Inv_A828c0 (g : ghost) (c : config) : Prop := exists j, Inv_A828c0_at g j c.
(* 0x82820 (F36's internal join; from `j 82820` at 0x82818 and the fall-through of 0x8281c). New cut. 0x82820 /
   0x82824 read Phi and len_j for the call at 0x82828, whose premise on the 50 bytes at Phi is FLSX's. *)
Definition Inv_A828cc_at (g : ghost) (j : nat) (c : config) : Prop :=
  exists phi, CUTST g 0x828cc (hb1 phi (AC.a_size (flen g j)))
    (fun fr regs m => g_n g < 2 ^ 26 /\ (j <= 255)%nat /\ HB m phi (flen g j) /\ FLSI g j fr regs m /\
       (LK g fr j regs m /\ FLSX g j phi fr regs m /\
        rg regs 20 (t_want_m (g_in g) j) /\ LT g fr j regs m)) c.
Definition Inv_A828cc (g : ghost) (c : config) : Prop := exists j, Inv_A828cc_at g j c.
(* 0x8282c (F36's exit 3, F37's entry; reac_box_catalogue_match returned): a0 = the match result and s4 = the
   wanted row (0x8282c `bne a0,s4,82b34` not taken); register 24 is not the kind here. *)
Definition Inv_A828d8_at (g : ghost) (j : nat) (c : config) : Prop :=
  exists phi, CUTST g 0x828d8 (hb1 phi (AC.a_size (flen g j)))
    (fun fr regs m => g_n g < 2 ^ 26 /\ (j <= 255)%nat /\ HB m phi (flen g j) /\ FLSI g j fr regs m /\
       (LK g fr j regs m /\ FLSX g j phi fr regs m /\
        rg regs 20 (t_want_m (g_in g) j) /\ rg regs 10 (t_want (g_in g) j) /\ LT g fr j regs m)) c.
Definition Inv_A828d8 (g : ghost) (c : config) : Prop := exists j, Inv_A828d8_at g j c.
(* 0x82894 (F37's exit, F38's entry; the free wrapper returned, so the heap list is empty). FLSF and LT: F38 reads
   s2 = len_j (FLSF) and [A+216] / [A+224] (FLSI in FLSF), and hands IFS g fr (S j) (LT), f1_IN and [A+248]
   (FLSI) to the loop-head cut of turn j + 1 at the back branch 0x828b0. *)
Definition Inv_A82940_at (g : ghost) (j : nat) (c : config) : Prop :=
  exists phi, CUTST g 0x82940 []
    (fun fr regs m => g_n g < 2 ^ 26 /\ LK g fr j regs m /\ FLSF g j phi fr regs m /\ LT g fr j regs m) c.
Definition Inv_A82940 (g : ghost) (c : config) : Prop := exists j, Inv_A82940_at g j c.

(* ---- Epilogue, release, abort (X1, X2, Jrel, Y). *)
(* X1 entry (0x82a58) and X2 entry (0x82a74), push 7 (a Theorem Labs lane 01:04Z): a Theorem Labs lane's Seg/X12.v (a version not in this delivery) Inv_A82a58_loc /
   Inv_A82a74_loc (written on a working branch e94ad2a6bfb, seg_X1 / seg_X2 Qed) word for word, so the segments move by a
   rename. X1 reads the identity record pointer spill [A + 144] = fr + 2688, the 21 identity bytes there with a 0
   in bytes 3 .. 19 (the memchr wrapper's 17-byte search from fr + 2691 finds it), and those 17 bytes addressable;
   X2 reads a0 <> 0 (0x82b20 `beqz a0`, the abort pair, not taken). X12.v's `SF` is lib/A/Spec/StrFun, which this
   file names SFA. F38's exit into 0x82a58 must produce Inv_A82b04's three new conjuncts. *)
Definition Inv_A82b04 (g : ghost) (c : config) : Prop :=
  CUTST g 0x82b04 [] (fun fr regs m =>
    g_n g < 2 ^ 26 /\ OURb g fr m /\
    spill regs m 144 (fr + 2688) /\
    (exists nm, bytes_at rsegs m (fr + 2688) nm /\ length nm = 21%nat /\
       SFA.find_byte 0 (firstn 17 (skipn 3 nm)) <> None) /\
    addressable m (fr + 2691) 17) c.
Definition Inv_A82b20 (g : ghost) (c : config) : Prop :=
  CUTST g 0x82b20 [] (fun fr regs m =>
    g_n g < 2 ^ 26 /\ OURb g fr m /\ (exists q, a0v regs q /\ 0 < q < 2 ^ 64)) c.
(* Jrel (release join, 0x82ac0): FRA, H = the entry heap (HB = []); reached from X2 (normal return) and from A4
   (n >= 2^26, slot_early, 0x812c4 j 0x82ac0). The release writes 0x45e0360e to fr then beqz s5 (0x82acc): the side
   arm frees the FS frame (jal frame_release_6, Y1 0x82adc), the real arm clears the frame shadow (jal meta_fill_00,
   Y2 0x82aec); both reach the post-release epilogue (0x82af0, no FRA). Arms told apart by FRA's frame-location
   disjunction. *)
(* Both edges into 0x82ac0 reach it with the selector in register 21 and the frame base in register 22: the early
   edge 0x812c4 keeps the 0x80f34/0x80f3c selector and the 0x80f40/0x80f50 frame base, the normal path reloads
   them at 0x82ab8 (`ld s5,32(s1)`) and 0x82abc (`ld s6,24(s1)`). The join reads register 22 at 0x82b88
   (`sd a0,0(s6)`), so the cut pins it; it pins no spill, since the early edge wrote neither [A + 32] nor
   [A + 24]. *)
Definition Inv_Jrel (g : ghost) (c : config) : Prop :=
  CUTST0 g 0x82b80 [] (fun fr s5 regs _ => rg regs 21 s5 /\ rg regs 22 fr) c.
(* Y1 (side release call, 0x82adc): a0 = s5 = fr and a1 = 3040 for jal frame_release_6 (the FS frame is freed;
   asan_stack_free_c.v reads the size in a1, 0x82ad0-0x82ad4 lui/addiw give 0xbe0 = 3040). Past the header store
   at 0x82ac8, so CUTSTR: the frame header word is 0x45e0360e, not 0x41b58ab3. *)
Definition Inv_A82b9c (g : ghost) (c : config) : Prop :=
  CUTSTR g 0x82b9c [] (fun fr s5 regs _ => s5 = fr /\ a0v regs fr /\ rg regs 11 FRAME_BYTES) c.
(* Y2 (real release call, 0x82bac): the selector is 0, a0 = s3 = S(fr) and a1 = 380 (0x82ae4 li a1,380) for jal
   meta_fill_00; also past the header store. *)
Definition Inv_A82bac (g : ghost) (c : config) : Prop :=
  CUTSTR g 0x82bac [] (fun fr s5 regs _ => s5 = 0 /\ a0v regs (Sfr fr) /\ rg regs 11 FRAME_SHADOW) c.
(* Y3 (0x82af0): the post-release epilogue head, reached from Y1 (0x82ae0 `j 0x82af0`) and from Y2's return. No
   FRA: the frame is released (side arm) or its shadow cleared (real arm). It carries what the 13 reloads
   0x82bb4-0x82bec and the slot post need: s0 = S (0x82bb4 `addi sp,s0,-416` restores the entry sp), the saved
   caller registers at [S - 104, S), gp and tp still the entry ones (Post's a_regs_kept), the runtime and heap
   invariants, errno writable, the slot window writable and addressable again (alib_post:97; Y1 released the
   frame, Y2 cleared its shadow), and ENT, out of which ent_post (Seg/Tac_slot.v) builds every clause of the post
   that compares the return state with the entry state. a0 is NOT 0 here: 0x82af0 `li a0,0` is the first
   instruction of this segment, so the cut before it holds the callee's result (push 5c; push 5 had a0 = 0).
   Push 13 group D (a Theorem Labs lane's Inv_A82af0_loc, lib/A/Prog/SegCF/YTail.v (not in this delivery) at a working branch e4f35fe410a): the
   stklo bound, right after the aa_AH conjunct. Y3's reload area [S - 104, S) needs a place in the at-main window
   (Cf_run.stk_base_le_stklo bounds the window base by stklo); Y1 / Y2 prove it at their exit from FRAH's bound,
   which the release writes keep (a_laws_store / a_laws_fs_store, a_laws_mat_le). *)
Definition Inv_A82bb0 (g : ghost) (c : config) : Prop :=
  exists regs mem md,
    c = mkCfg (mkst regs (Z_to_bv 64 0x82bb0) mem (seg_rom segs)) md /\
    AsanRTInv.RT (g_S g - 416) mem md /\ AC.aa_AH AC.ASYMS AsanRTInv.RT API (g_H g) mem md /\
    AC.aa_stklo AC.ASYMS AsanRTInv.RT API mem md <= g_S g - AF.SLOT_STACK /\
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

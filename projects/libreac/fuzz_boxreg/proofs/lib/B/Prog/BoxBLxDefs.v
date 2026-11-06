(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: made from proofs/cgif/cgif_file_fuzzer/lib/A/ACfh.v (srz_enter, the journal over a token list), ACk2.v (the file system a closed journal keeps), ACfj.v (tfib_lib_x) and ACfi.v (tfib_lib_x_all) for libreac/fuzz_grant: module paths, GrantB, the library shape grant_shape, and the entry function's phase machine of lib/A/Prog/GrantEntryDefs.v in place of cgif's. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/GrantLibX.v, with its module paths and module names changed; 309 of its 349 lines of code are new or changed and 132 lines of the source are left out. *)
(* The walk of fuzz_boxreg.asan-ubsan's LLVMFuzzerTestOneInput (0x7ffac, 1058 instructions), cut into phases:
   the data every phase shares. The phases (lib/B/Prog/BoxBLx*.v) prove, each from its own cut, that the run
   reaches the function's post-condition; lib/B/Prog/BoxBLibX.v closes them into tbfib_lib_contract_x_all.

   The function keeps two frames:
   - a machine-stack frame: `addi sp,sp,-0x100` at 0x7ffac saves ra at sp0 - 8 and s0, s1, s2 .. s11 at
     sp0 - 16 .. sp0 - 104; s0 = sp0; `andi sp,sp,-0x20` (0x7ffec) sets sp = s1 = sp1 = 32 * ((sp0 - 256) / 32),
     and the body keeps its spill slots at sp1 + 0x08 .. sp1 + 0x97 (the input cursor `struct fuzz_in in` at
     sp1 + 0x88: the pointer at +0x88, the bytes left at +0x90);
   - a side-stack frame of class 3 (512-byte slots): the GOT-loaded use-after-return flag is 1 (AR's const law),
     so `__asan_stack_malloc_3 (0x1a0)` (0x8001c) gives the frame F; mac[6] lives at F + 0x20, the copy `prev`
     of the registry at F + 0x40 .. F + 0x15f, and the slot's flag address at F + 0x1f8. s6 holds its shadow
     base SHADOW_OFF + F / 8; the prologue writes 52 shadow bytes (LSH_entry), each loop turn marks mac and prev
     in scope (LSH_iter) and out of scope again at its end.
   The machine-stack fallback (flag 0, a stack probe) is refuted by the const law; the early return of an input
   of 2 ^ 26 bytes or more is refuted by the entry contract (n < 2 ^ 26).

   One phase = one file; the cut between two phases is a predicate on the machine state (`lx_from` below), never
   a symbolic state (fuzz_grant's lib/A/Prog/GrantEntryDefs.v, a working branch 86810443184, is the model).
   Cuts (offsets from the function's address):
   - LP_J 0x2ac (0x80258): the loop head, before `in.n == 0`;
   - LP_T 0x3a0 (0x8034c): an op byte is read and `prev` is copied (memcpy returned); the switch follows;
   - LP_K 0xb5c (0x80b08): the case is done, check (r, fabric) and the inline check_kept follow;
   - LP_X 0xea8 (0x80e54): free (r), the frame's release and the return follow. *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG0s YI16 YM05.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaRun PaShadow PaJournal BoxBase.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBSyms BoxBList BoxBPa BoxBPaLib BoxBFrame.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBCJ.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import
BoxBReacBoxregInit BoxBCheck BoxBReadMac BoxBReadName BoxBRangeFree BoxBReacBoxregFind
BoxBReacBoxregDeclare BoxBReacBoxregAdd BoxBReacBoxregSetName.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Rt Require Import StrncmpDefB SetShadowDef SnprintfDefB StrncmpViewB.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import BoxRo.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YImgTop.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require Boxreg.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- the function's stack, its frame on the side stack, and its budgets ---- *)
(* BoxBLibX.v's LLVMF_STKB, EV_LIBB, LIVE_LIBB (equal by their definitions). *)
Definition LX_STK : Z := 32768.
Definition LX_EV : Z := 2000.
Definition LX_LIVE : Z := 2 ^ 33.
(* `__asan_stack_malloc_3`: class 3, 512-byte slots; the flag address is the slot's last word. *)
Definition LX_CID : Z := 3.
(* sizeof (struct reac_boxreg) (BoxBReacBoxregInit.v's REG_SIZEB). *)
Definition LX_REG : Z := 288.

(* ---- the pcs of the cuts, as offsets in the listing (address - 0x7ffac) ---- *)
Definition LP_entry : Z := 0x0.
Definition LP_J : Z := 0x2ac.
Definition LP_T : Z := 0x3a0.
Definition LP_K : Z := 0xb5c.
Definition LP_X : Z := 0xea8.

(* The return addresses of the function's own calls of the malloc wrapper (0x8017c) and of the free wrapper
   (0x808b4 case 3, 0x808f4 case 0, 0x80e58 exit), as offsets in the listing. *)
Definition LX_MSITES : list Z := [0x1d4].
Definition LX_FSITES : list Z := [0x90c; 0x94c; 0xeb0].

(* The 52 shadow bytes the prologue writes (0x80088 .. 0x80160): 0xf1 left redzone (F .. F + 31), 0xf8 for mac
   (out of scope), 0xf2 between mac and prev, 0xf8 for prev (36 granules), 0xf3 right redzone; and the same bytes
   while a loop turn runs (0x80290, 0x802ac .. 0x80338): mac (6 bytes) and prev (288 bytes) in scope. *)
Definition LSH_entry : list Z := [241; 241; 241; 241; 248; 242; 242; 242] ++ repeat 248 36 ++ repeat 243 8.
Definition LSH_iter : list Z := [241; 241; 241; 241; 6; 242; 242; 242] ++ repeat 0 36 ++ repeat 243 8.

(* The registry rows a turn kept (fuzz_boxreg.c check_kept, Pau's lib/Prog/LLVMFuzzerTestOneInput_inv.v
   llvm_kept): each row of the table before the call keeps its base, width and pinned; a bound MAC stays; the name
   stays unless the turn renamed that row. *)
Definition lkept (bs bs' : list byte) (ren : Z) : Prop :=
  forall j, 0 <= j < Boxreg.bx_n bs ->
    Boxreg.bx_base bs' j = Boxreg.bx_base bs j /\ Boxreg.bx_nch bs' j = Boxreg.bx_nch bs j /\
    Boxreg.bx_pinned bs' j = Boxreg.bx_pinned bs j /\
    (Boxreg.bx_mac bs j = Boxreg.zero6 \/ Boxreg.bx_mac bs' j = Boxreg.bx_mac bs j) /\
    (j = ren \/ Boxreg.bx_name bs' j = Boxreg.bx_name bs j).

(* The image's globals the walk hands to callees (asan_globals 0x9db90 of fuzz_boxreg.asan-ubsan, 32-byte slots):
   ZERO (A_OBJ 4, 6 bytes), "" (A_OBJ 5, 1), read_mac.base (A_OBJ 6, 5), "%s" (A_OBJ 10, 3), "" (A_OBJ 11, 1). The
   start-up registration (__asan_register_elf_globals) writes each slot's 4 shadow bytes: the size, then 0xf9. *)
Definition LX_GLOBS : list (nat * Z) := [(4%nat, 6); (5%nat, 1); (6%nat, 5); (10%nat, 3); (11%nat, 1)].
Definition lx_glob_cells (val : nat -> Z) : list acell :=
  flat_map (fun g => let a := shadow_addr (val (A_OBJ (fst g))) in
    [z1 (ANum a) (snd g); z1 (ANum (a + 1)) 249; z1 (ANum (a + 2)) 249; z1 (ANum (a + 3)) 249]) LX_GLOBS.
(* The bytes the image's read-only data holds at each of those globals (fuzz_boxreg.asan-ubsan .rodata, measured on
   the original image: 0x20cc0 00 00 00 00 00 00, 0x20ce0 00, 0x20d00 00 40 ab 00 00, 0x20d40 25 73 00, 0x20d60 00). *)
Definition LX_GLOB_BYTES : list (nat * list Z) :=
  [(4%nat, [0; 0; 0; 0; 0; 0]); (5%nat, [0]); (6%nat, [0; 64; 171; 0; 0]); (10%nat, [37; 115; 0]); (11%nat, [0])].

(* ---- the FP state across a call that may reach the snprintf wrapper (reac_boxreg_declare, reac_boxreg_set_name) ----
   The callee returns at SOME fx' (BoxBase.v apost_baseF): f registers equal except f10, and fcsr the caller's or with
   rounding mode 0. The relation is reflexive and transitive. Every cut predicate (lx_body) pins the FP state to the
   fx of the Section it is used in; a segment that crosses such a call lands at fx' and continues with the cut taken
   at fx' (a Theorem Labs lane's srr_fx_continue, a working branch ad235a56db0 lib/A/FMsnprintfSx.v:58-72).
   Shape of a cross-call segment (fx = the Section's FP state; POSTF a post-condition family indexed by the FP state
   at the cut, closed under lx_fxr by lx_post_mono):
     forall (POSTF : YK11.FPState -> lxcx -> world SEGS -> config -> Prop) <args>,
       lx_post_mono POSTF ->
       (forall fx', lx_fxr fx fx' -> lx_from B MT (POSTF fx') (NEXT (fx := fx') B MT <args>)) ->
       lx_from B MT (POSTF fx) (PREV B MT <args>).
   Every other segment keeps its POST-generic statement at the Section fx; the composition instantiates it at each
   fx with POST := POSTF fx. *)
Definition lx_fxr (fxa fxb : YK11.FPState) : Prop :=
  (forall k : bv 5, bv_unsigned k <> 10 -> Sem.reg_get (@fp_regs fxb) k = Sem.reg_get (@fp_regs fxa) k) /\
  (@fp_csr fxb = @fp_csr fxa \/ Z.land (Z.shiftr (bv_unsigned (@fp_csr fxb)) 5) 7 = 0).

Lemma lx_fxr_refl : forall fxa, lx_fxr fxa fxa.
Proof. intros fxa. split; [intros k _; reflexivity | left; reflexivity]. Qed.

Lemma lx_fxr_trans : forall fxa fxb fxc, lx_fxr fxa fxb -> lx_fxr fxb fxc -> lx_fxr fxa fxc.
Proof.
  intros fxa fxb fxc [Rab Cab] [Rbc Cbc]. split.
  - intros k Hk. rewrite (Rbc k Hk). exact (Rab k Hk).
  - destruct Cbc as [Ebc | Zc]; [|right; exact Zc]. rewrite Ebc.
    destruct Cab as [Eab | Zb]; [left; exact Eab | right; exact Zb].
Qed.

(* Rounding mode 0 at the entry (freeze change 4: the premise declare / set_name / snprintf take) holds at every FP
   state a call reaches: lx_fxr keeps fcsr or gives rounding mode 0. *)
Lemma lx_fxr_rm0 : forall fxa fxb : YK11.FPState,
  Z.land (Z.shiftr (bv_unsigned (@fp_csr fxa)) 5) 7 = 0 -> lx_fxr fxa fxb ->
  Z.land (Z.shiftr (bv_unsigned (@fp_csr fxb)) 5) 7 = 0.
Proof. intros fxa fxb H [_ [E | Z0]]; [rewrite E; exact H | exact Z0]. Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg boxb_listing}.
#[local] Notation SEGS := (@pa_segs _ boxb_listing PI).
#[local] Notation VAL := (@pa_val _ boxb_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ boxb_listing PI).
#[local] Notation BASE := (@pa_val _ boxb_listing PI A_TEXT).

Section c.
Variable B : asyms.
Variable MT : ameter_ops.

(* What the walk needs of the image's allocator symbols and of the listing's objects beyond PALib / PALibF:
   AR fixes the shadow of the globals above (they are cells of as_const); each of them starts a 32-byte slot,
   lies 64 bytes or more inside the image's read range, and holds its bytes in the read-only image; every
   allocator-owned byte of the read-only image is a const cell carrying the image's word (abfm_ro_owned_pinned,
   lib/B/Rt/StrncmpViewB.v; strncmp's rom_viewO). *)
Record BLxLib : Prop := {
  blx_cells : forall ly c, In c (lx_glob_cells VAL) -> In c (as_const B ly);
  blx_al : forall g, In g LX_GLOBS -> VAL (A_OBJ (fst g)) mod 32 = 0;
  blx_marg : forall g, In g LX_GLOBS -> IMG_LO + 64 <= VAL (A_OBJ (fst g)) /\ VAL (A_OBJ (fst g)) + snd g + 64 <= IMG_HI;
  (* R2: "%s" (A_OBJ 10) below the image's GOT canary slot, the P2 premise of declare's and set_name's specs *)
  blx_fmt_got : VAL (A_OBJ 10) + 3 <= 0x99f60;
  blx_pinned : abfm_ro_owned_pinned SEGS B;
  blx_rom_bytes : forall g, In g LX_GLOB_BYTES -> absn_rom_bytes SEGS B (VAL (A_OBJ (fst g))) (snd g);
  blx_rom_strs : absn_rom_str SEGS B (VAL (A_OBJ 5)) [] /\ absn_rom_str SEGS B (VAL (A_OBJ 11)) [] /\
    absn_rom_str SEGS B (VAL (A_OBJ 10)) [37; 115];
  blx_isv : img_shadow_vis SEGS B;
  (* musl memchr's 32 constant bytes at MCH_LOB (0x10350), read inside check (BoxBCheck.v premise). *)
  blx_mch : absn_rom_bytes SEGS B MCH_LOB MCH_CONSTSB
}.

(* The runtime entries and the contracts of the called functions (each the callee's own statement, at its
   address in the listing), and the facts on B and MT the walk uses: the Section hypotheses of the walk. *)
Record lx_hyps : Prop := {
  lh_laws : AR_laws SEGS B;
  lh_tl : PALib B;
  lh_tlf : PALibF B;
  lh_glob : BLxLib;
  lh_ml : model_laws (as_universe B);
  lh_mtl : ameter_laws MT;
  lh_mtfl : ameter_fs_laws MT;
  lh_asm3 : astack_malloc_realizes SEGS B 3;
  lh_smp : stack_malloc_progressP B;
  lh_asf : astack_free_law SEGS B;
  lh_ffl : frame_flag_lawP SEGS B;
  lh_malloc : amalloc04_rule SEGS B MT;
  lh_free : afree04_rule SEGS B MT;
  lh_memcpy : aintrin_realizes SEGS B OCpy (SIGMA BB___asan_memcpy);
  lh_bcmp : abcmp_realizes SEGS B (SIGMA BB___interceptor_trampoline_bcmp);
  lh_strncmp : abstrncmp_realizes SEGS B (SIGMA BB___interceptor_trampoline_strncmp);
  lh_setsh_f5 : aset_shadow_realizes SEGS B (SIGMA BB___asan_set_shadow_f5) 0xf5;
  lh_init : tbreac_boxreg_init_spec B;
  lh_check : tbcheck_spec B;
  lh_read_mac : tbread_mac_spec B;
  lh_read_name : tbread_name_spec B MT;
  lh_range_free : tbrange_free_spec B;
  lh_find : tbreac_boxreg_find_spec B;
  lh_declare : tbreac_boxreg_declare_spec B;
  lh_add : tbreac_boxreg_add_spec B;
  lh_set_name : tbreac_boxreg_set_name_spec B;
  lh_rn_trace : In [pc_malloc_ra0 (as_code B); AB_read_name_mallocRA] (as_universe B)
}.

(* What the call may spend with the allocator: the registry, then per loop turn at most one name (1 .. 48
   bytes) and its free, then the registry's free. *)
Definition LX_A1 : Z := mo_malloc MT LX_REG.
Definition LX_AI : Z := mo_malloc MT 48 + mo_free MT.
Definition LX_NEED : Z := LX_A1 + 64 * LX_AI + mo_free MT.

(* ---- the function's context: what the call starts from ---- *)
Record lxcx := mkLXCX {
  lc_ly : alayout; lc_S : astate; lc_W : world SEGS; lc_regs : bvmap 5 word;
  lc_mem : word -> option byte; lc_md : Model;
  lc_p : Z;                  (* the caller's input buffer *)
  lc_pl : list byte;         (* its bytes *)
  lc_T : Z                   (* the allocator budget the caller grants *)
}.
Definition lc_n (cx : lxcx) : Z := Z.of_nat (length (lc_pl cx)).
Definition lsp0 (cx : lxcx) : Z := spZ (lc_regs cx).
Definition lsp1 (cx : lxcx) : Z := 32 * ((lsp0 cx - 256) / 32).

(* The frame this call owns on the side stack, its flag, and its shadow. *)
Definition lF (cx : lxcx) (fp : Z) : Z := frame_addr (lc_ly cx) LX_CID fp.
Definition lFL (cx : lxcx) (fp : Z) : Z := flag_addr (lc_ly cx) LX_CID fp.
Definition lSH (cx : lxcx) (fp : Z) : Z := shadow_addr (lF cx fp).

(* The call chain this call hands to the functions it calls (cgif lib/A/ACf5.v:128-131; GrantEntryDefs.v gch). *)
Definition lch (cx : lxcx) : list (Z * Z * Z) :=
  if lsp0 cx + 16 <? ly_top (lc_ly cx)
  then [(lsp0 cx, raZ (lc_regs cx), s0Z (lc_regs cx))] else [].

Definition lx_base (cx : lxcx) : Prop :=
  afn_pre SEGS B LX_STK (lc_ly cx) (lc_S cx) (lc_W cx) (lc_regs cx) (lc_mem cx) (lc_md cx) [] /\
  getr (lc_regs cx) 10 = w64 (lc_p cx) /\ getr (lc_regs cx) 11 = w64 (lc_n cx) /\
  ((lc_n cx = 0 /\ 0 <= lc_p cx < 2 ^ 64) \/
   (0 < lc_n cx < 2 ^ 26 /\ In (lc_p cx, lc_n cx) (ablocks B (lc_ly cx) (lc_S cx)))) /\
  garr8 SEGS (mrestrict (w_H (lc_W cx)) (lc_mem cx)) (lc_p cx) (map (fun b : byte => bv_unsigned b) (lc_pl cx)) /\
  frames (lc_S cx) = [] /\
  st_nev (lc_S cx) + LX_EV <= EV_MAX /\ blocks_bytes (lc_S cx) + LX_LIVE <= LIVE_MAX /\
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H (lc_W cx)) (lc_mem cx)) /\
  mo_ok MT (lc_S cx) (lc_T cx) /\ LX_NEED <= lc_T cx /\
  (forall pcf (regsT : bvmap 5 word),
     (pcf = pc_malloc_ra0 (as_code B) /\ In (raZ regsT - BASE) LX_MSITES) \/
     (pcf = pc_free_ra0 (as_code B) /\ In (raZ regsT - BASE) LX_FSITES) ->
     In (call_trace0 pcf regsT (lch cx)) (as_universe B)).

(* ---- the memory of a cut ---- *)
Definition lview (W3 : world SEGS) (ms3 : machine_state) : reader := aview SEGS (w_H W3) (ms_mem ms3).

(* A spill slot of the machine frame. *)
Definition lslot (cx : lxcx) (W3 : world SEGS) (ms3 : machine_state) (off v : Z) : Prop :=
  rdword (lview W3 ms3) (lsp1 cx + off) = Some v.

(* The saved registers of the machine frame, which the epilogue reads back (ra, s0, s1, s2 .. s11). *)
Definition lsaved (cx : lxcx) (W3 : world SEGS) (ms3 : machine_state) : Prop :=
  rdword (lview W3 ms3) (lsp0 cx - 8) = Some (raZ (lc_regs cx)) /\
  (forall j, 0 <= j < 12 ->
     rdword (lview W3 ms3) (lsp0 cx - 16 - 8 * j) =
     Some (bv_unsigned (getr (lc_regs cx) (Z_to_bv 5 (if j <? 2 then 8 + j else 16 + j))))).

(* The shadow bytes of the frame. *)
Definition lshadow (cx : lxcx) (fp : Z) (W3 : world SEGS) (ms3 : machine_state) (sh : list Z) : Prop :=
  forall i, (i < length sh)%nat -> lview W3 ms3 (lSH cx fp + Z.of_nat i) = Some (nth i sh 0).

(* The registers every cut keeps: sp = s1 = sp1, s0 = sp0, gp, tp, s2 = the shadow offset, s6 = the frame's
   shadow base. *)
Definition lregs (cx : lxcx) (fp : Z) (ms3 : machine_state) : Prop :=
  getr (ms_regs ms3) 2 = w64 (lsp1 cx) /\
  getr (ms_regs ms3) 8 = w64 (lsp0 cx) /\
  getr (ms_regs ms3) 9 = w64 (lsp1 cx) /\
  getr (ms_regs ms3) 3 = getr (lc_regs cx) 3 /\
  getr (ms_regs ms3) 4 = getr (lc_regs cx) 4 /\
  getr (ms_regs ms3) 18 = w64 SHADOW_OFF /\
  getr (ms_regs ms3) 22 = w64 (lSH cx fp).

(* What every cut carries: the pc, the registers, the saved registers, the frame's shadow and flag word, the
   slots that hold the frame (sp1 + 0x10 = __asan_stack_malloc_3's result, sp1 + 0x18 and sp1 + 0x80 = the frame
   in use), and the caller's input as it gave it. *)
Definition lx_body (cx : lxcx) (fp : Z) (pc : Z) (W3 : world SEGS) (ms3 : machine_state) (sh : list Z) : Prop :=
  ms_pc_val ms3 = w64 (BASE + pc) /\ ms_resv ms3 = None /\ ms_svc_pending ms3 = None /\
  ms_rom ms3 = seg_rom SEGS /\ ms_fregs ms3 = fp_regs /\ ms_fcsr ms3 = fp_csr /\
  lregs cx fp ms3 /\ lsaved cx W3 ms3 /\ lshadow cx fp W3 ms3 sh /\
  rdword (lview W3 ms3) (lF cx fp + fs_frame_bytes LX_CID - 8) = Some (lFL cx fp) /\
  lslot cx W3 ms3 0x10 (lF cx fp) /\ lslot cx W3 ms3 0x18 (lF cx fp) /\ lslot cx W3 ms3 0x80 (lF cx fp) /\
  garr8 SEGS (mrestrict (w_H W3) (ms_mem ms3)) (lc_p cx) (map (fun b : byte => bv_unsigned b) (lc_pl cx)).

(* The registry struct: the 288-byte heap block at r holds bs (the form of BoxBReacBoxregDeclare.v's
   tbdecl_reg_bytes and BoxBCheck.v's premise). *)
Definition lreg (W3 : world SEGS) (ms3 : machine_state) (r : Z) (bs : list byte) : Prop :=
  forall i, 0 <= i < LX_REG -> lview W3 ms3 (r + i) = Some (bv_unsigned (nth (Z.to_nat i) bs (Z_to_bv 8 0))).

(* `prev`, the turn's copy of the registry, at F + 0x40. *)
Definition lprev (cx : lxcx) (fp : Z) (W3 : world SEGS) (ms3 : machine_state) (bs : list byte) : Prop :=
  forall i, 0 <= i < LX_REG -> lview W3 ms3 (lF cx fp + 64 + i) = Some (bv_unsigned (nth (Z.to_nat i) bs (Z_to_bv 8 0))).

(* The blocks: the caller's, and the registry. *)
Definition lblk (cx : lxcx) (ly3 : alayout) (S3 : astate) (r : Z) : Prop :=
  ablocks B ly3 S3 = ablocks B (lc_ly cx) (lc_S cx) ++ [(r, LX_REG)].

(* The input cursor: pos bytes are read. *)
Definition lcur (cx : lxcx) (W3 : world SEGS) (ms3 : machine_state) (pos : nat) : Prop :=
  (pos <= length (lc_pl cx))%nat /\
  lslot cx W3 ms3 0x88 (lc_p cx + Z.of_nat pos) /\ lslot cx W3 ms3 0x90 (lc_n cx - Z.of_nat pos).

(* The slots the loop keeps from 0x80214 on (registry r, fabric fab, frame F): the address of r->n and its shadow
   byte and the partial-granule bound, the fabric, r's alignment test, mac's address, ~r and ~prev. *)
Definition lslots_loop (cx : lxcx) (fp : Z) (W3 : world SEGS) (ms3 : machine_state) (r fab : Z) : Prop :=
  lslot cx W3 ms3 0x08 3 /\
  lslot cx W3 ms3 0x28 (r + 280) /\
  lslot cx W3 ms3 0x30 fab /\
  lslot cx W3 ms3 0x38 0 /\
  lslot cx W3 ms3 0x40 (shadow_addr (r + 280)) /\
  lslot cx W3 ms3 0x68 (lF cx fp + 32) /\
  lslot cx W3 ms3 0x70 (2 ^ 64 - 1 - r) /\
  lslot cx W3 ms3 0x78 (2 ^ 64 - 1 - (lF cx fp + 64)).

(* ---- the invariant at each cut ---- *)

(* 0x80258, the loop head of turn i: the registry r holds bs, a table that passes Pau's checks for the fabric fab;
   pos input bytes are read. s3 = 1, s4 = r, s5 = prev, s8 = i, s11 = fab. *)
Definition LI_J (i : nat) (cx : lxcx) (fp k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists (pos : nat) (r fab : Z) (bs : list byte),
  lx_body cx fp LP_J W3 ms3 LSH_entry /\ (i < 64)%nat /\
  k <= 1 + 2 * Z.of_nat i /\ acc <= LX_A1 + Z.of_nat i * LX_AI /\
  lblk cx ly3 S3 r /\ lreg W3 ms3 r bs /\ Boxreg.boxreg_inv bs /\ Boxreg.bx_fabric bs = fab /\
  lcur cx W3 ms3 pos /\ lslots_loop cx fp W3 ms3 r fab /\
  getr (ms_regs ms3) 19 = w64 1 /\ getr (ms_regs ms3) 20 = w64 r /\
  getr (ms_regs ms3) 21 = w64 (lF cx fp + 64) /\ getr (ms_regs ms3) 24 = w64 (Z.of_nat i) /\
  getr (ms_regs ms3) 27 = w64 fab.

(* 0x8034c, turn i: the op byte op (the input byte at pos, op & 3 = c) is read and prev holds a copy of the
   registry; mac and prev are in scope. s7 = op, s10 = r->n. *)
Definition LI_T (c : Z) (i : nat) (cx : lxcx) (fp k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists (pos : nat) (r fab op : Z) (bs : list byte),
  lx_body cx fp LP_T W3 ms3 LSH_iter /\ (i < 64)%nat /\
  k <= 1 + 2 * Z.of_nat i /\ acc <= LX_A1 + Z.of_nat i * LX_AI /\
  lblk cx ly3 S3 r /\ lreg W3 ms3 r bs /\ Boxreg.boxreg_inv bs /\ Boxreg.bx_fabric bs = fab /\
  lprev cx fp W3 ms3 bs /\
  (pos < length (lc_pl cx))%nat /\ op = bv_unsigned (nth pos (lc_pl cx) (Z_to_bv 8 0)) /\ Z.land op 3 = c /\
  lcur cx W3 ms3 (S pos) /\ lslots_loop cx fp W3 ms3 r fab /\
  getr (ms_regs ms3) 19 = w64 1 /\ getr (ms_regs ms3) 20 = w64 r /\
  getr (ms_regs ms3) 21 = w64 (lF cx fp + 64) /\ getr (ms_regs ms3) 23 = w64 op /\
  getr (ms_regs ms3) 24 = w64 (Z.of_nat i) /\ getr (ms_regs ms3) 26 = w64 (Boxreg.bx_n bs) /\
  getr (ms_regs ms3) 27 = w64 fab.

(* 0x80b08, turn i: the case is done; the registry holds bs', which passes Pau's checks and keeps prev's rows
   (renamed: ren, -1 for none), and the name block, if any, is freed. s8 = ren as an unsigned 32-bit value,
   the turn number at sp1 + 0x58. *)
Definition LI_K (i : nat) (cx : lxcx) (fp k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists (pos : nat) (r fab ren : Z) (bs bs' : list byte),
  lx_body cx fp LP_K W3 ms3 LSH_iter /\ (i < 64)%nat /\
  k <= 3 + 2 * Z.of_nat i /\ acc <= LX_A1 + (Z.of_nat i + 1) * LX_AI /\
  lblk cx ly3 S3 r /\ lprev cx fp W3 ms3 bs /\ Boxreg.boxreg_inv bs /\ Boxreg.bx_fabric bs = fab /\
  lreg W3 ms3 r bs' /\ Boxreg.boxreg_inv bs' /\ Boxreg.bx_fabric bs' = fab /\ lkept bs bs' ren /\
  -1 <= ren < Boxreg.bx_n bs /\
  lcur cx W3 ms3 pos /\ lslots_loop cx fp W3 ms3 r fab /\ lslot cx W3 ms3 0x58 (Z.of_nat i) /\
  getr (ms_regs ms3) 20 = w64 r /\ getr (ms_regs ms3) 21 = w64 (lF cx fp + 64) /\
  getr (ms_regs ms3) 24 = w64 (ren mod 2 ^ 32) /\ getr (ms_regs ms3) 27 = w64 fab.

(* 0x80e54: the loop is done (the input is used up, or 64 turns ran); free (r) follows. *)
Definition LI_X (cx : lxcx) (fp k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists r : Z,
  lx_body cx fp LP_X W3 ms3 LSH_entry /\ k <= 129 /\ acc <= LX_A1 + 64 * LX_AI /\
  lblk cx ly3 S3 r /\ getr (ms_regs ms3) 20 = w64 r.

(* ---- a phase ---- *)
(* `lx_from POST GI`: from any machine state that GI describes, the run reaches the post-condition. *)
Definition lx_from (POST : lxcx -> world SEGS -> config -> Prop)
  (GI : lxcx -> Z -> Z -> Z -> alayout -> astate -> world SEGS -> machine_state -> Model -> Prop) : Prop :=
  forall (cx : lxcx) (fp k acc : Z) ly3 S3 W3 (ms3 : machine_state) md3,
  lx_base cx ->
  ajournal SEGS B LX_STK (lsp0 cx) [] (lc_ly cx) (lc_S cx) (lc_W cx) (lc_mem cx) (lc_md cx)
    [(LX_CID, fp)] ly3 S3 W3 (ms_mem ms3) md3 k ->
  frames S3 = [(LX_CID, fp)] ->
  mo_le MT (lc_S cx) S3 acc ->
  GI cx fp k acc ly3 S3 W3 ms3 md3 ->
  SRr SEGS W3 (mkCfg ms3 md3) (POST cx).

(* A post-condition family indexed by the FP state at the cut is closed under the relation of a call that may reach
   the snprintf wrapper (see lx_fxr). *)
Definition lx_post_mono (POSTF : YK11.FPState -> lxcx -> world SEGS -> config -> Prop) : Prop :=
  forall fxa fxb, lx_fxr fxa fxb -> forall cx W c, POSTF fxb cx W c -> POSTF fxa cx W c.

(* A phase proved for one post-condition holds for a weaker one. *)
Lemma lx_from_mono : forall (POST POST' : lxcx -> world SEGS -> config -> Prop) GI,
  (forall cx W c, POST cx W c -> POST' cx W c) -> lx_from POST GI -> lx_from POST' GI.
Proof.
  intros POST POST' GI HPP H cx fp k acc ly3 S3 W3 ms3 md3 HB HJ HFR MLE HGI.
  apply (SRr_mono SEGS W3 (mkCfg ms3 md3) (POST cx) (POST' cx)); [exact (H cx fp k acc ly3 S3 W3 ms3 md3 HB HJ HFR MLE HGI)|].
  intros W' c' _ HQ. exact (HPP cx W' c' HQ).
Qed.

(* The whole call: from the function's first slot under `lx_base`. *)
Definition lx_start (POST : lxcx -> world SEGS -> config -> Prop) : Prop :=
  forall cx : lxcx, lx_base cx ->
  SRr SEGS (lc_W cx)
    (mkCfg (mkst (lc_regs cx) (w64 (BASE + LP_entry)) (lc_mem cx) (seg_rom SEGS)) (lc_md cx))
    (POST cx).

(* The post-condition of the whole call, in apost_base's shape: back at the caller's return address, the journal
   (no frame left, no footprint), callee-saved registers kept, a0 = 0, the caller's blocks, the budget, the
   caller's input bytes unchanged. *)
Definition lx_post (cx : lxcx) : world SEGS -> config -> Prop :=
  fun W' c' => exists ly' S' regs' mem' md' k,
    c' = mkCfg (mkst regs' (getr (lc_regs cx) 1) mem' (seg_rom SEGS)) md' /\
    ajournal SEGS B LX_STK (lsp0 cx) [] (lc_ly cx) (lc_S cx) (lc_W cx) (lc_mem cx) (lc_md cx)
      [] ly' S' W' mem' md' k /\ k <= LX_EV /\
    aregs_preserved (lc_regs cx) regs' /\ getr regs' 10 = w64 0 /\
    Permutation (ablocks B ly' S') (ablocks B (lc_ly cx) (lc_S cx)) /\
    mo_le MT (lc_S cx) S' (lc_T cx) /\
    (forall i, 0 <= i < lc_n cx ->
       aview SEGS (w_H W') mem' (lc_p cx + i) = aview SEGS (w_H (lc_W cx)) (lc_mem cx) (lc_p cx + i)).

End c.

(* ---- facts every phase uses ---- *)
Section d.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.

(* The read-only data stays as the image has it across a journal with no footprint (BoxBase.v's
   arodata_ok_journalP without its ro_below_ofl instance: an empty footprint opens no sink). *)
Lemma lx_arodata_kept : forall STK sp0 ly S (W : world SEGS) mem md own ly' S' W' mem' md' k,
  ajournal SEGS B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W') mem').
Proof.
  intros STK sp0 ly S W mem md own ly' S' W' mem' md' k HJ HR a Hro Ho He.
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
  rewrite (F3 a); [exact (HR a Hro Ho He) | | exact Ho | exact He |].
  - destruct Hro as [(s & Hs & _ & Hr) | Hgot]; [exists s; split; [exact Hs | exact Hr]|].
    exact (pa_relro_img a Hgot).
  - apply fp_spares_closed. intros Hopen. exact (sink_closed_nil Hopen).
Qed.

(* A byte the image carries is visible in every state: aview reads memory, else the image (YP09.v mbyte). *)
Lemma lx_aview_some : forall (H : word -> bool) mem a,
  seg_rom SEGS (Z_to_bv 64 a) <> None -> aview SEGS H mem a <> None.
Proof.
  intros H mem a Hs. unfold aview, mbyte.
  destruct (mrestrict H mem (Z_to_bv 64 a)); [cbn; discriminate|].
  destruct (seg_rom SEGS (Z_to_bv 64 a)); [cbn; discriminate | contradiction].
Qed.
(* The read-only image as every call keeps it (SnprintfDefB.v absn_rom_kept: a byte of a read-only segment that is
   neither an owned static nor errno reads as the image's byte): the M-form premise proposed for the restated
   strncmp / memchr contracts (a Theorem Labs lane, rt2/FM-RELOC.md section 10), from arodata_okP alone. *)
Lemma lx_absn_rom_kept : forall (W : world SEGS) mem,
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) -> absn_rom_kept SEGS B W mem.
Proof. intros W mem HR a Ha Ho He. exact (HR a (or_introl Ha) Ho He). Qed.

(* The two read-only views the frozen strncmp contract takes (lib/B/Rt/StrncmpDefB.v): abfm_rom_viewN from arodata_okP
   (kept by every journal with no footprint, lx_arodata_kept), abfm_rom_viewO from AR's constant law and BLxLib's
   blx_pinned (abfm_rom_viewO_of_AR, lib/B/Rt/StrncmpViewB.v). *)
Lemma lx_rom_viewN : forall (W : world SEGS) mem,
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) -> abfm_rom_viewN SEGS B W mem.
Proof. intros W mem HR a Ha Ho He. exact (HR a (or_introl Ha) Ho He). Qed.

Lemma lx_rom_viewO : forall ly S (W : world SEGS) mem md,
  abfm_ro_owned_pinned SEGS B -> AR SEGS B ly S W mem md -> abfm_rom_viewO SEGS B W mem.
Proof. intros ly S W mem md HP HAR. exact (abfm_rom_viewO_of_AR SEGS B ly S W mem md HP HAR). Qed.


(* A journal with no footprint holds for any footprint (cgif lib/A/ACfh.v:29-43; GrantLibX.v grant_journal_fp). *)
Lemma lx_inFP_nil : forall a, ~ inFP [] a.
Proof. intros a (r & Hin & _). exact Hin. Qed.

Lemma lx_journal_fp : forall STK sp0 FP ly S (W : world SEGS) mem md own ly' S' W' mem' md' k,
  ajournal SEGS B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
  ajournal SEGS B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k.
Proof.
  intros STK sp0 FP ly S W mem md own ly' S' W' mem' md' k
    (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres & Hstatic & F5 & HQT).
  split; [exact HAR|]. split; [exact Hly|]. split; [exact Hsecs|]. split; [exact Hwle|].
  split; [eapply aos_step_mono; [|exact Hio]; intros Ho; exfalso; exact (sink_closed_nil Ho)|].
  split; [exact Hfrs|]. split; [exact Hnev|]. split; [exact Hk|]. split; [exact F1|].
  split; [intros q m i H1 H2 Hi _; apply (F2 q m i H1 H2 Hi); apply lx_inFP_nil|].
  split; [intros a Hi Hns He _; apply (F3 a Hi Hns He); apply fp_spares_closed;
          intros Ho; exact (sink_closed_nil Ho)|].
  split; [intros cid pos a H1 H2 _; apply (F4 cid pos a H1 H2); apply lx_inFP_nil|].
  split; [intros q m i H1 H2 Hi; exfalso; exact (lx_inFP_nil _ (Hgone q m i H1 H2 Hi))|].
  split; [exact Hpres|]. split; [exact Hstatic|]. split; [exact F5 | exact HQT].
Qed.

(* What a journal with no footprint leaves of the file system (GrantLibX.v grant_journal_io). *)
Lemma lx_journal_io : forall STK sp0 ly S (W : world SEGS) mem md own ly' S' W' mem' md' k,
  ajournal SEGS B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
  m_fds md' = m_fds md /\ m_fs md' = m_fs md.
Proof.
  intros STK sp0 ly S W mem md own ly' S' W' mem' md' k HJ.
  pose proof HJ as (_ & _ & _ & _ & Hos & _).
  destruct (aos_step_closed [] md md' sink_closed_nil Hos) as (Efd & Efsys & _ & _).
  unfold m_fds, m_fs. rewrite Efd, Efsys. split; reflexivity.
Qed.

(* The chain a callee sees: the function's own frame record (ra at sp0 - 8, the caller's s0 at sp0 - 16) on top
   of the empty chain of the entry contract. *)
Lemma lx_achain : forall (cx : lxcx) (rd : reader) (sp' : Z),
  achain (lc_ly cx) (aview SEGS (w_H (lc_W cx)) (lc_mem cx)) (lsp0 cx) (s0Z (lc_regs cx)) [] ->
  ly_top (lc_ly cx) <= 2 ^ 64 -> alloc_ceiling <= lsp0 cx -> lsp0 cx mod 8 = 0 -> 4096 <= raZ (lc_regs cx) ->
  (forall a, lsp0 cx <= a < 2 ^ 64 -> rd a = aview SEGS (w_H (lc_W cx)) (lc_mem cx) a) ->
  rdword rd (lsp0 cx - 8) = Some (raZ (lc_regs cx)) ->
  rdword rd (lsp0 cx - 16) = Some (s0Z (lc_regs cx)) ->
  sp' + 16 <= lsp0 cx ->
  achain (lc_ly cx) rd sp' (lsp0 cx) (lch cx).
Proof.
  intros cx rd sp' Hc Htop Hceil Hal Hra Hk H8 H16 Hsp. unfold lch.
  destruct (Z.ltb_spec (lsp0 cx + 16) (ly_top (lc_ly cx))) as [Hlt | Hge].
  - exact (achain_push _ _ _ _ _ _ _ _ Hc Htop Hk H8 H16 Hra Hceil Hal ltac:(lia) Hsp).
  - left. split; [right; left; lia | reflexivity].
Qed.

End d.
End b.
End a.

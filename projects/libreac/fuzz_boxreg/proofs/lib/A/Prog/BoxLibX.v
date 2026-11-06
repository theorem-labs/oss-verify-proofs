(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/ACfn.v (origin/ossv/recipes c8557374ad2), as fuzz_grant's lib/A/ACfn.v (a working branch 03b974dd117) copies it, with its module paths changed, its addresses moved to libreac/fuzz_boxreg's ASan build (fuzz_boxreg.asan), and the three changes below. *)
(* The whole-run contract of LLVMFuzzerTestOneInput on fuzz_boxreg.asan (0x7ff4c, 1065 instructions): the hypothesis
   that the ported ASan top (TFIB_T, lib/A/BoxTFIB.v) consumes, in cgif's shape (tfib_lib_pre_x, tfib_lib_post_x,
   tfib_lib_contract_x, tfib_lib_contract_x_all). Statement only.
   Values (each measured on fuzz_boxreg.asan with elfdis):
   - A_LLVMF = box_text + AF_LLVMFuzzerTestOneInput = 0x7ff4c (BoxAddr.v, BoxList.v).
   - RA_LLVMF = 0x7fe48: the driver's only call of the function is target_run's `jal` at 0x7fe44 (target_run
     0x7fd7c); 0x7fe48 is the instruction after it.
   - A_EMPTY = 0x5d35e0 (symbol oft_aligned_copy.empty): for n = 0 target_run branches at 0x7fdd4 to 0x7fe24 and
     passes a0 = s4 + 0x10, s4 = 0x5d35d0 (auipc/addi at 0x7fdb0, symbol target_run.initialized). For n > 0 it passes
     the __wrap_malloc copy of the input (0x7fddc, memcpy at 0x7fdf0): a heap block of length n.
   - EV_LIB = 2000, cgif's value: one run makes at most 2 + 2 * 64 = 130 allocator events (registry malloc 0x80118
     and free 0x80e18; one read_name malloc and one free in each of at most 64 loop iterations; PROGRAM.md P3 section
     4). 130 <= 2000, and the top's composition is written for 2000 (4 * 2000 + 3 <= EV_MAX = 8192), so the exact
     value is not needed.
   - LIVE_LIB = 2 ^ 33, cgif's value: one run holds at most 288 + 48 = 336 live bytes above the entry's blocks.
   - LLVMF_STK = 32768, cgif's value, a bound: the function's own machine stack is at most 688 bytes (addi sp,sp,-0x100
     at 0x7ff4c, andi sp,sp,-0x20 at 0x7ff8c (16 more), then without a side-stack frame the 0x1a0-byte frame below it
     at 0x7ffd4 .. 0x7ffec); its deepest callee needs ASTACK + 48 = 16432 (read_name: frame 0x30 and the __wrap_malloc
     call, whose acall_pre needs ASTACK = 16384, YG0d.v); its own malloc and free calls need ASTACK; check needs 160 +
     2 * ESTACK, reac_boxreg_add 80 + reac_boxreg_find's 48 + 2 * ESTACK, the bcmp wrapper 2 * ESTACK
     (abcmp_realizes). 688 + 16432 = 17120 <= 32768. The strncmp wrapper (__wrap_strncmp 0x413f8, called at 0x805f0,
     0x80a48, 0x80bc4) has no contract in lib/Reusable yet; it has 32768 - 688 = 32080 bytes of room.
   Changes from cgif's shape (each because fuzz_boxreg's tree and images differ from cgif's):
   - cgif's pre and post state asink_none segs tfib_K and ameta_inv segs tfib_K (lib/YE00.v, lib/YE01.v, over the
     stdio and malloc-meta record tfib_K of lib/A/AE2k.v), and arodata_okS segs B (lib/YE01.v). None of these three
     files is in fuzz_boxreg's tree, and fuzz_boxreg.asan holds no "/tmp/out.gif" string (YE00.v astdio_env needs it at
     ak_path), so cgif's sink record has no instance here. The sink and meta invariants are therefore two variables
     of the section, SINKN (in place of asink_none segs tfib_K) and METAI (in place of ameta_inv segs tfib_K), which
     the ported top instantiates; tfib_lib_contract_x_all takes them as its two last arguments. fuzz_grant instead
     copies lib/Reusable/YE00.v and lib/Reusable/YE01.v (a working branch f8f56869a0c) and lib/A/AB1v.v and
     lib/A/AE2k.v (03b974dd117, its tfib_K moved to fuzz_grant.asan), and its lib/A/ACfn.v uses them unchanged.
   - arodata_okS segs B RLO RHI is BoxBase.v's arodata_okP segs RLO RHI B: the same read-only predicate (in_roP is
     arodata_okS's premise), with the arguments in BoxBase.v's order.
   - segs is BoxImg.v's box_segs (images.Asan's loaded segments, cgif's tfibsegs of lib/A/AB1v.v), and the sink head
     is the section's context {SK : YI16.sink_head}, as in every spec of lib/A/Prog (cgif takes it from AE2k.v's
     instance tfib_sink_head).
   Hazards of the function (for its proof):
   - Its ASan frame: if the GOT-loaded use-after-return flag is set it calls __asan_stack_malloc_3 (a0 = 0x1a0) at
     0x7ffbc (a side-stack frame); otherwise it takes the 0x1a0 bytes on the machine stack with a stack probe that
     stores 8 zero bytes 4096 bytes below the 32-aligned sp (0x7ffe0 .. 0x7ffe8). It writes the frame's shadow
     (0x80028 .. 0x80100). On every exit (0x80e24) it writes the retired-frame magic 0x45e0360e into the frame's
     first word, then calls __asan_set_shadow_f5 (0x80e3c, side-stack frame) or clears the frame's shadow
     (0x80e4c .. 0x80f18), and returns a0 = 0 (0x80f1c).
   - n >= 2 ^ 26 returns 0 at once (srli a0, s5, 0x1a; bnez at 0x80104); the registry is __wrap_malloc (0x120) at
     0x80118 (a NULL result branches at 0x8011c to the abort path) and __wrap_free at 0x80e18.
   - The __asan_report_* calls and __asan_handle_no_return + abort (0x80f60, 0x80f64) do not return. LIBK at
     box_shape is K (LL 0 fs []) (lib/A/BoxShape.v), so the proof must show each of these paths unreachable.
   - No f* or csr instruction occurs in the function (measured), so the fixed FP state fx of the section is sound. *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK11 YK0s YK15 YK18 YP09 YI00.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YI16.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import BoxList BoxAddr BoxImg BoxBase.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Definition A_LLVMF : Z := box_text + AF_LLVMFuzzerTestOneInput.
Definition RA_LLVMF : Z := 0x7fe48.
Definition A_EMPTY : Z := 0x5d35e0.
Definition EV_LIB : Z := 2000.
Definition LIVE_LIB : Z := 2 ^ 33.
Definition LLVMF_STK : Z := 32768.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable SINKN : (word -> option byte) -> Model -> Prop.
Variable METAI : alayout -> (word -> option byte) -> Z -> Prop.
Local Notation segs := box_segs.
Local Notation rd W mem := (mrestrict (w_H W) mem).
Definition tfib_lib_pre_x (regs : bvmap 5 word) (ly : alayout) (S : astate) (W : world segs) (mem : word -> option byte) (md : Model)
(p n : Z) (pl : list byte) (M : Z) : Prop :=
afn_pre segs B LLVMF_STK ly S W regs mem md [] /\
raZ regs = RA_LLVMF /\
getr regs 10 = w64 p /\ getr regs 11 = w64 n /\
((n = 0 /\ p = A_EMPTY) \/ (0 < n < 2 ^ 26 /\ In (p, n) (ablocks B ly S))) /\
n = Z.of_nat (length pl) /\ garr8 segs (rd W mem) p (map (fun b : byte => bv_unsigned b) pl) /\
frames S = [] /\ st_nev S + EV_LIB <= EV_MAX /\ blocks_bytes S + LIVE_LIB <= LIVE_MAX /\
arodata_okP segs RLO RHI B (aview segs (w_H W) mem) /\
SINKN (rd W mem) md /\
fd_lookup (m_fds md) (alloc_fd (m_fds md)) = None /\
Fs.fs_sorted (m_fs md) = true /\
METAI ly (rd W mem) M /\
mo_ok MT S (XM_LIB n) /\
(* the rounding mode at the harness entry, which the walk hands to reac_boxreg_declare and
   reac_boxreg_set_name, and they to the snprintf wrapper (lib/A/Rt/SnprintfDef.v). This is the core's own
   fx-slot premise (a Theorem Labs lane, bd0315ce146 ACfn.v:104 tfib_lib_pre_xf). *)
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0.
Definition tfib_lib_post_x (regs : bvmap 5 word) (ly : alayout) (S : astate) (W : world segs) (mem : word -> option byte) (md : Model)
(p n : Z) (M : Z) (l : lleaf)
(ly' : alayout) (S' : astate) (W' : world segs) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) (k : Z) : Prop :=
ajournal segs B LLVMF_STK (spZ regs) [sink_token] ly S W mem md [] ly' S' W' mem' md' k /\ k <= EV_LIB /\
aregs_preserved regs regs' /\ getr regs' 10 = w64 0 /\
Permutation (ablocks B ly' S') (ablocks B ly S) /\
(forall fd, fd_lookup (m_fds md') fd = fd_lookup (m_fds md) fd) /\
m_fs md' = ll_fs l /\ ll_ret l = 0 /\ ll_out l = [] /\ Fs.fs_sorted (ll_fs l) = true /\
SINKN (rd W' mem') md' /\
METAI ly' (rd W' mem') M /\
mo_le MT S S' (XN_LIB n) /\
(forall i, 0 <= i < n -> aview segs (w_H W') mem' (p + i) = aview segs (w_H W) mem (p + i)).
Definition tfib_lib_contract_x : Prop :=
forall ly S (W : world segs) (regs : bvmap 5 word) mem md p n pl M (K : lleaf -> TSet),
AI segs (w_H W) (w_A W) md ->
tfib_lib_pre_x regs ly S W mem md p n pl M ->
(forall (l : lleaf) (W' : world segs) (c' : config),
wle W W' -> AI segs (w_H W') (w_A W') (cfg_model c') ->
(exists (fx' : YK11.FPState) ly' S' regs' mem' md' k,
c' = @cfg_at fx' segs RA_LLVMF regs' mem' md' /\
(forall k0 : bv 5, bv_unsigned k0 <> 10 -> Sem.reg_get (@fp_regs fx') k0 = Sem.reg_get (@fp_regs fx) k0) /\
(@fp_csr fx' = @fp_csr fx \/ Z.land (Z.shiftr (bv_unsigned (@fp_csr fx')) 5) 7 = 0) /\
tfib_lib_post_x regs ly S W mem md p n M l ly' S' W' regs' mem' md' k) ->
srealizes segs c' (K l)) ->
srealizes segs (cfg_at segs A_LLVMF regs mem md) (LIBK pl (m_fs md) K).
End a.
Definition tfib_lib_contract_x_all {rc : YM05.RunCeil} {LS : lib_shape} {SK : YI16.sink_head} (B : asyms) (MT : ameter_ops) (XM_LIB XN_LIB : Z -> Z) (RLO RHI : Z)
(SINKN : (word -> option byte) -> Model -> Prop) (METAI : alayout -> (word -> option byte) -> Z -> Prop) : Prop :=
forall fx : YK11.FPState, @tfib_lib_contract_x fx rc LS SK B MT XM_LIB XN_LIB RLO RHI SINKN METAI.

(* ---- the walk of the function, closed at the statement ----
   The walk is lib/A/Prog/BoxLx*.v (the cuts BoxLxDefs.v, the loop BoxLxLoop.v, one file per phase); this part turns
   its whole-call result (`gb_start ... gb_post`, from the function's first slot) into tfib_lib_contract_x at
   fuzz_boxreg's library shape (lib/A/BoxShape.v: LIBK pl fs K = K (LL 0 fs [])), in the form of fuzz_grant's
   lib/A/Prog/GrantLibX.v (a working branch). *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK14 YI04 YI09 YN3v YG0v.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A Require Import BoxShape.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaTable PaSym BoxSyms BoxPa BoxLxDefs BoxLxLoop.
Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* From a run that keeps the world to the set of traces the statement speaks of (cgif_file lib/A/ACfh.v:47-50). *)
Lemma box_srz_enter : forall segs (W : world segs) (c : config) (T : TSet),
  AI segs (w_H W) (w_A W) (cfg_model c) ->
  SRr segs W c (fun W' c' => AI segs (w_H W') (w_A W') (cfg_model c') -> srealizes segs c' T) ->
  srealizes segs c T.
Proof. intros segs W c T HAI HS. apply (HS HAI T). intros W' c' _ HAI' HK. exact (HK HAI'). Qed.
Context {SK : YI16.sink_head}.
Variable B : asyms.
(* A journal that opened no sink carries over to any token list (GrantLibX.v grant_journal_fp, cgif_file
   lib/A/ACfh.v:29-43). *)
Lemma box_journal_fp : forall STK sp0 FP ly S (W : world box_segs) mem md own ly' S' W' mem' md' k,
  ajournal box_segs B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
  ajournal box_segs B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k.
Proof.
  intros STK sp0 FP ly S W mem md own ly' S' W' mem' md' k
    (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres & Hstatic & F5 & HQT).
  split; [exact HAR|]. split; [exact Hly|]. split; [exact Hsecs|]. split; [exact Hwle|].
  split; [eapply aos_step_mono; [|exact Hio]; intros Ho; exfalso; exact (sink_closed_nil Ho)|].
  split; [exact Hfrs|]. split; [exact Hnev|]. split; [exact Hk|]. split; [exact F1|].
  split; [intros q m i H1 H2 Hi _; apply (F2 q m i H1 H2 Hi); apply inFP_nil|].
  split; [intros a Hi Hns He _; apply (F3 a Hi Hns He); apply fp_spares_closed;
          intros Ho; exact (sink_closed_nil Ho)|].
  split; [intros cid pos a H1 H2 _; apply (F4 cid pos a H1 H2); apply inFP_nil|].
  split; [intros q m i H1 H2 Hi; exfalso; exact (inFP_nil _ (Hgone q m i H1 H2 Hi))|].
  split; [exact Hpres|]. split; [exact Hstatic|]. split; [exact F5 | exact HQT].
Qed.
(* What a journal that opened no sink leaves of the file system. *)
Lemma box_journal_io : forall STK sp0 ly S (W : world box_segs) mem md own ly' S' W' mem' md' k,
  ajournal box_segs B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
  m_fds md' = m_fds md /\ m_fs md' = m_fs md.
Proof.
  intros STK sp0 ly S W mem md own ly' S' W' mem' md' k HJ.
  pose proof HJ as (_ & _ & _ & _ & Hos & _).
  destruct (aos_step_closed [] md md' sink_closed_nil Hos) as (Efd & Efsys & _ & _).
  unfold m_fds, m_fs. rewrite Efd, Efsys. split; reflexivity.
Qed.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable SINKN : (word -> option byte) -> Model -> Prop.
Variable METAI : alayout -> (word -> option byte) -> Z -> Prop.
Hypothesis MTL : ameter_laws MT.
(* The sink and meta invariants of the statement survive every journal that opened no sink: cgif_file's
   lib/YE01.v:82 asink_none_kept and :153 ameta_inv_kept, which the top that instantiates SINKN / METAI cites. *)
Hypothesis AIL_SINKN : forall STK sp0 FP ly S (W : world box_segs) mem md own ly' S' (W' : world box_segs) mem' md' k,
  ajournal box_segs B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k -> ~ YI16.sink_open_fp FP ->
  SINKN (mrestrict (w_H W) mem) md -> SINKN (mrestrict (w_H W') mem') md'.
Hypothesis AIL_METAI : forall STK sp0 FP ly S (W : world box_segs) mem md own ly' S' (W' : world box_segs) mem' md' k M,
  ajournal box_segs B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
  METAI ly (mrestrict (w_H W) mem) M -> METAI ly' (mrestrict (w_H W') mem') M.
(* The read-only range the statement names covers the image's PT_GNU_RELRO, which the listing's instance names. *)
Hypothesis HRO : forall rd, arodata_okP box_segs RLO RHI B rd ->
  arodata_okP box_segs (pa_relro_lo (PAImg := PI_box)) (pa_relro_hi (PAImg := PI_box)) B rd.
(* The call traces of the malloc and free wrappers at this function's four call sites (GB_MSITES, GB_FSITES). *)
Hypothesis HTR : forall (ly : alayout) (regs regsT : bvmap 5 word) (pcf : Z),
  raZ regs = RA_LLVMF ->
  (pcf = pc_malloc_ra0 (as_code B) /\ In (raZ regsT - box_text) GB_MSITES) \/
  (pcf = pc_free_ra0 (as_code B) /\ In (raZ regsT - box_text) GB_FSITES) ->
  In (call_trace0 pcf regsT
       (if spZ regs + 16 <? ly_top ly then [(spZ regs, raZ regs, s0Z regs)] else []))
     (as_universe B).
(* The allocator budget the caller grants covers what the call spends (HXL, cgif_file ACfj.v:124), and the budget
   the post reports is at least that. *)
Hypothesis HXL : forall n, GB_NEED MT <= XM_LIB n.
Hypothesis HXLN : forall n, XM_LIB n <= XN_LIB n.
(* The context of the call, as the statement hands it over. *)
Definition box_cx (ly : alayout) (S : astate) (W : world box_segs) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) (p : Z) (pl : list byte) (T : Z) : bcx (PI := PI_box) :=
  mkBCX (PI := PI_box) ly S W regs mem md p pl
    (32 * ((spZ regs + -256) / 32)) (Ereg regs [w64 SHADOW_OFF]) T.
(* The walk runs from the entry under the statement's pre, whose last conjunct is the entry fcsr's rounding mode 0
   (the declare / set_name contracts ask for it at their calls). *)
Theorem box_lib_x_of_start :
  (Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
   gb_start (PI := PI_box) B MT (gb_postF (PI := PI_box) fx B MT)) ->
  @tfib_lib_contract_x fx rc box_shape SK B MT XM_LIB XN_LIB RLO RHI SINKN METAI.
Proof.
  intros START ly S W regs mem md p n pl M K HAI HPRE HK.
  destruct HPRE as (HFN & Hra & Hp & Hn & Hpn & Hnpl & HPL & Hfr & Hev & Hlive & HROS &
                    HSNK & HFD & HSORT & HAM & HMOK & HRM0).
  assert (HB : gb_base (PI := PI_box) B MT (box_cx ly S W regs mem md p pl (XM_LIB n))).
  { unfold gb_base, box_cx, c_n.
    cbn [c_ly c_S c_W c_regs c_mem c_md c_p c_pl c_sp1 c_E0 c_T].
    rewrite <- Hnpl.
    split; [exact HFN|]. split; [exact Hp|]. split; [exact Hn|].
    split; [exact Hpn|]. split; [exact HPL|]. split; [exact Hfr|].
    split; [exact Hev|]. split; [exact Hlive|].
    split; [exact (HRO _ HROS)|].
    split; [reflexivity|].
    split; [intros m0 r Hm0; exact (ew_Ereg_nat regs _ m0 r Hm0)|].
    split; [exact (f_equal (fun w => bv_unsigned w) (ew_Ereg_nat regs _ 2 2%bv eq_refl))|].
    split; [exact (ew_Ereg_extra regs [w64 SHADOW_OFF] 0)|].
    split; [exact HMOK|].
    split; [intros pcf regsT Hsite; exact (HTR ly regs regsT pcf Hra Hsite)|].
    exact (HXL n). }
  change (LIBK pl (m_fs md) K) with (K (LL 0 (m_fs md) [])).
  refine (box_srz_enter box_segs W (cfg_at box_segs A_LLVMF regs mem md) _ HAI _).
  eapply SRr_mono.
  { exact (START HRM0 _ HB). }
  intros W' c' Hwle HPOST HAI'.
  unfold gb_postF, gb_post, box_cx in HPOST.
  cbn [c_ly c_S c_W c_regs c_mem c_md c_p c_pl c_T] in HPOST.
  destruct HPOST as (fxe & (HRf & HRc) & ly' & S' & regs' & mem' & md' & k & Ec & HJ & Hk & HPR & Ha0 & HPerm &
                     HMLE & HFkeep).
  destruct (box_journal_io GB_STK (spZ regs) ly S W mem md [] ly' S' W' mem' md' k HJ) as [Efds Efs].
  apply (HK (LL 0 (m_fs md) []) W' c' Hwle HAI').
  exists fxe, ly', S', regs', mem', md', k.
  split.
  { rewrite Ec. unfold cfg_at. f_equal. f_equal.
    unfold w64. rewrite <- Hra. unfold raZ. symmetry. apply Z_to_bv_bv_unsigned. }
  split; [exact HRf|]. split; [exact HRc|].
  unfold tfib_lib_post_x. cbn [ll_fs ll_ret ll_out].
  split; [exact (box_journal_fp GB_STK (spZ regs) [sink_token] ly S W mem md [] ly' S' W' mem' md' k HJ)|].
  split; [exact Hk|]. split; [exact HPR|]. split; [exact Ha0|]. split; [exact HPerm|].
  split; [intros fd; rewrite Efds; reflexivity|].
  split; [exact Efs|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact HSORT|].
  split; [exact (AIL_SINKN _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ sink_closed_nil HSNK)|].
  split; [exact (AIL_METAI _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HAM)|].
  split; [exact (mle_weaken MT S S' (XM_LIB n) (XN_LIB n) MTL HMLE (HXLN n))|].
  intros i Hi. apply HFkeep. unfold c_n. cbn [c_pl]. lia.
Qed.
End g.

(* ---- the walk, composed ----
   The loop (BoxLxLoop.v gb_loop) over the phase lemmas head (BoxLxHead.v), cases 0 .. 3 (BoxLxCase<k>.v), join
   (BoxLxJoin.v) and exit (BoxLxExit.v), entered by the entry phase (BoxLxEntry.v), at fuzz_boxreg.asan's listing instance
   PI_box, closed at the statement by box_lib_x_of_start. Every premise below is a Section hypothesis: the callee
   contracts (their walks are separate files), the runtime's entries, the allocator's laws and the image facts that hold
   for the asyms record B the top builds. *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YImgTop.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import BoxPaLib BoxRo BoxFrame.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import
  Check ReadName ReacBoxregInit ReacBoxregFind ReacBoxregDeclare ReacBoxregAdd ReacBoxregSetName RangeFree LowestFree.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Rt Require Import SnprintfDef StrncmpDef StrncmpView SetShadowDef.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require BoxLxEntry BoxLxHead BoxLxCase0 BoxLxCase1 BoxLxCase2 BoxLxCase3A BoxLxCase3Top BoxLxJoin
  BoxLxExit.
Section h. Context {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable SINKN : (word -> option byte) -> Model -> Prop.
Variable METAI : alayout -> (word -> option byte) -> Z -> Prop.
(* (1) the allocator meter (cgif_file ACfj.v:97, :105; YC5d.v) *)
Hypothesis MTL : ameter_laws MT.
Hypothesis MTF : ameter_fs_laws MT.
(* (2) the statement's sink and meta invariants are kept by every journal that opened no sink (cgif_file YE01.v:82
   asink_none_kept, :153 ameta_inv_kept) *)
Hypothesis AIL_SINKN : forall STK sp0 FP ly S (W : world box_segs) mem md own ly' S' (W' : world box_segs) mem' md' k,
  ajournal box_segs B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k -> ~ YI16.sink_open_fp FP ->
  SINKN (mrestrict (w_H W) mem) md -> SINKN (mrestrict (w_H W') mem') md'.
Hypothesis AIL_METAI : forall STK sp0 FP ly S (W : world box_segs) mem md own ly' S' (W' : world box_segs) mem' md' k M,
  ajournal box_segs B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
  METAI ly (mrestrict (w_H W) mem) M -> METAI ly' (mrestrict (w_H W') mem') M.
(* (3) the statement's read-only range covers the listing instance's, which lies below the sink's list head *)
Hypothesis HRO : forall rd, arodata_okP box_segs RLO RHI B rd ->
  arodata_okP box_segs (pa_relro_lo (PAImg := PI_box)) (pa_relro_hi (PAImg := PI_box)) B rd.
Hypothesis RO : @ro_below_ofl box_segs (pa_relro_lo (PAImg := PI_box)) (pa_relro_hi (PAImg := PI_box)) SK.
(* (4) the function's own malloc / free call traces and read_name's malloc trace *)
Hypothesis HTR : forall (ly : alayout) (regs regsT : bvmap 5 word) (pcf : Z),
  raZ regs = RA_LLVMF ->
  (pcf = pc_malloc_ra0 (as_code B) /\ In (raZ regsT - box_text) GB_MSITES) \/
  (pcf = pc_free_ra0 (as_code B) /\ In (raZ regsT - box_text) GB_FSITES) ->
  In (call_trace0 pcf regsT
       (if spZ regs + 16 <? ly_top ly then [(spZ regs, raZ regs, s0Z regs)] else []))
     (as_universe B).
Hypothesis HRNTR : In [pc_malloc_ra0 (as_code B); A_read_name_mallocRA (PI := PI_box)] (as_universe B).
(* (5) the budget: what the call spends is within what the caller grants, and the post's bound is at least that *)
Hypothesis HXL : forall n, GB_NEED MT <= XM_LIB n.
Hypothesis HXLN : forall n, XM_LIB n <= XN_LIB n.
(* (6) the allocator, the side stack and the runtime's entries the function and its inline code call *)
Hypothesis LAWS : forall fx : YK11.FPState, AR_laws box_segs B.
Hypothesis TL : forall fx : YK11.FPState, PALib (PI := PI_box) B.
Hypothesis TLF : forall fx : YK11.FPState, PALibF (PI := PI_box) B.
Hypothesis ML : forall fx : YK11.FPState, model_laws (as_universe B).
Hypothesis ASM3 : forall fx : YK11.FPState, astack_malloc_realizes box_segs B 3.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis ASF : forall fx : YK11.FPState, astack_free_law box_segs B.
Hypothesis FFL : forall fx : YK11.FPState, frame_flag_lawP box_segs B.
Hypothesis AMALLOC4 : forall fx : YK11.FPState, amalloc04_rule (SK := SK) box_segs B MT.
Hypothesis AFREE4 : forall fx : YK11.FPState, afree04_rule (SK := SK) box_segs B MT.
Hypothesis AMEMCPY : forall fx : YK11.FPState,
  aintrin_realizes box_segs B OCpy (pa_sigma (PAImg := PI_box) BS___asan_memcpy).
Hypothesis ABCMP : forall fx : YK11.FPState,
  abcmp_realizes box_segs B (pa_sigma (PAImg := PI_box) BS___interceptor_trampoline_bcmp).
Hypothesis ASTRNCMP : forall fx : YK11.FPState,
  astrncmp_realizes box_segs B (pa_sigma (PAImg := PI_box) BS___interceptor_trampoline_strncmp).
Hypothesis ASETF5 : forall fx : YK11.FPState,
  aset_shadow_realizes box_segs B (pa_sigma (PAImg := PI_box) BS___asan_set_shadow_f5) 0xf5.
(* (7) the program functions the function calls, by their contracts *)
Hypothesis TINIT : forall fx : YK11.FPState, treac_boxreg_init_spec (SK := SK) (PI := PI_box) B.
Hypothesis TCHECK : forall fx : YK11.FPState, tcheck_spec (SK := SK) (PI := PI_box) B.
Hypothesis TREADNAME : forall fx : YK11.FPState, tread_name_spec (SK := SK) (PI := PI_box) B MT.
Hypothesis TFIND : forall fx : YK11.FPState, treac_boxreg_find_spec (SK := SK) (PI := PI_box) B.
Hypothesis TDECL : forall fx : YK11.FPState, treac_boxreg_declare_spec (SK := SK) (PI := PI_box) B.
Hypothesis TADD : forall fx : YK11.FPState, treac_boxreg_add_spec (SK := SK) (PI := PI_box) B.
Hypothesis TSETNAME : forall fx : YK11.FPState, treac_boxreg_set_name_spec (SK := SK) (PI := PI_box) B.
Hypothesis TRANGEFREE : forall fx : YK11.FPState, trange_free_spec (SK := SK) (PI := PI_box) B.
Hypothesis TLOWFREE : forall fx : YK11.FPState, tlowest_free_spec (SK := SK) (PI := PI_box) B.
(* (8) the image's shadow and its registered globals' shadow (the start-up certificate), and the read-only bytes the
   function and its callees read (state-free over B: each byte read is no owned static and no errno byte; past a
   string's NUL, asn_rom_str asks only that the NUL's 8-byte word is image data) *)
Hypothesis HISV : forall fx : YK11.FPState, img_shadow_vis box_segs B.
Hypothesis HGLOB : forall fx : YK11.FPState, globs_marked box_segs B (BX_G (PI := PI_box)).
Hypothesis HZERO : asn_rom_bytes box_segs B (box_val (A_OBJ 6)) (map (fun b : byte => bv_unsigned b) Boxreg.zero6).
Hypothesis HRMB : asn_rom_bytes box_segs B (box_val (A_OBJ 4)) [0; 64; 171; 0; 0].
Hypothesis HEMP5 : asn_rom_str box_segs B (box_val (A_OBJ 5)) [].
Hypothesis HFMT : asn_rom_bytes box_segs B (box_val (A_OBJ 10)) ASN_FMT.
Hypothesis HEMP11 : asn_rom_str box_segs B (box_val (A_OBJ 11)) [].
Hypothesis HMCH : asn_rom_bytes box_segs B MCH_LO MCH_CONSTS.
(* (9) the strncmp contract's view of the read-only bytes the runtime owns: B pins each of them in its constant
   cells (lib/A/Rt/StrncmpView.v ro_owned_pinned; the asyms instance discharges it), so fm_rom_viewO holds at every
   AR state (fm_rom_viewO_of_AR). Its other view (fm_rom_viewN) the walk derives at each call from the journal's
   arodata_okP. *)
Hypothesis HROP : ro_owned_pinned box_segs B.

(* The 64-byte margins of the registered globals inside the image range, at fuzz_boxreg.asan's addresses. The listing
   instance is unfolded to box_val by cbn first: vm_compute must never evaluate PI_box, whose fields hold the image. *)
Lemma box_globs_margins :
  Forall (fun g => IMG_LO + 64 <= fst g /\ fst g + snd g + 64 <= IMG_HI) (BX_G (PI := PI_box)).
Proof.
  unfold BX_G. cbn [pa_val PI_box].
  repeat constructor; cbn [fst snd]; unfold IMG_HI; vm_compute; discriminate.
Qed.

Theorem pb_llvmf_libx : @tfib_lib_contract_x_all rc box_shape SK B MT XM_LIB XN_LIB RLO RHI SINKN METAI.
Proof.
  intros fx.
  pose proof box_globs_margins as HMRG.
  assert (HZ1 : IMG_LO + 64 <= box_val (A_OBJ 6)) by (vm_compute; discriminate).
  assert (HZ2 : box_val (A_OBJ 6) + 6 + 64 <= IMG_HI) by (vm_compute; discriminate).
  assert (HROMO : forall (fx1 : YK11.FPState) ly S (W : world box_segs) mem md,
            AR box_segs B ly S W mem md -> fm_rom_viewO box_segs B W mem)
    by (intros fx1 ly S W mem md HAR; exact (fm_rom_viewO_of_AR box_segs B ly S W mem md HROP HAR)).
  apply (box_lib_x_of_start B MT XM_LIB XN_LIB RLO RHI SINKN METAI MTL AIL_SINKN AIL_METAI HRO HTR HXL HXLN).
  intros HRM0.
  set (POST := gb_postF (PI := PI_box) fx B MT).
  apply (@BoxLxEntry.gb_entry fx rc SK PI_box B MT (LAWS fx) (TL fx) (TLF fx) MTL MTF (ML fx) (ASM3 fx) SMP
           (AMALLOC4 fx) (TINIT fx) (TCHECK fx) (HISV fx) (HGLOB fx) HZERO HZ1 HZ2 HMCH POST).
  apply (gb_loop (PI := PI_box) fx B MT POST).
  - intros fx1 i HT HX.
    exact (@BoxLxHead.gb_head fx1 rc SK PI_box B MT (LAWS fx1) (AMEMCPY fx1) MTL POST i HT HX).
  - intros fx1 op3 i HR1 Hop3 HK.
    (* the rounding mode the declare / set_name calls ask for, kept from the entry along lx_fxr *)
    pose proof (lx_fxr_frm0 fx fx1 HR1 HRM0) as HRM1.
    assert (Hc : op3 = 0 \/ op3 = 1 \/ op3 = 2 \/ op3 = 3) by lia.
    destruct Hc as [-> | [-> | [-> | ->]]].
    + exact (@BoxLxCase0.gb_case0 fx1 rc SK PI_box RO B MT POST (LAWS fx1) (TL fx1) MTL AFREE4 (TREADNAME fx1) HRNTR
               (TRANGEFREE fx1) (TLOWFREE fx1) (TDECL fx1) (HISV fx1) (HGLOB fx1) HMRG HFMT
               ltac:(cbn [pa_val PI_box]; vm_compute; discriminate) HZERO HEMP5 ABCMP ASTRNCMP
               (HROMO fx1) i HRM1 HK).
    + exact (@BoxLxCase1.gb_case1 fx1 rc SK PI_box B MT (LAWS fx1) MTL (HISV fx1) (HGLOB fx1) (AMEMCPY fx1)
               (ABCMP fx1) (TFIND fx1) (TADD fx1) (TLOWFREE fx1) HZERO HRMB HMRG POST i (HK fx1 (lx_fxr_refl fx1))).
    + exact (@BoxLxCase2.gb_case2 fx1 rc SK PI_box B MT (LAWS fx1) MTL (AMEMCPY fx1) (TFIND fx1) (ABCMP fx1)
               (HGLOB fx1) (HISV fx1) HZERO HRMB HMRG POST i (HK fx1 (lx_fxr_refl fx1))).
    + exact (@BoxLxCase3Top.gb_case3 fx1 rc SK PI_box B MT (LAWS fx1) (TL fx1) MTL (fun fx' _ => AFREE4 fx')
               (fun fx' _ => ASTRNCMP fx') (HISV fx1) (HGLOB fx1) (TSETNAME fx1)
               HFMT ltac:(cbn [pa_val PI_box]; vm_compute; discriminate) ltac:(cbn [pa_val PI_box]; vm_compute; discriminate)
               ltac:(cbn [pa_val PI_box]; vm_compute; discriminate)
               HEMP11 ltac:(cbn [pa_val PI_box]; vm_compute; discriminate) ltac:(cbn [pa_val PI_box]; vm_compute; discriminate)
               HEMP5 ltac:(cbn [pa_val PI_box]; vm_compute; discriminate) ltac:(cbn [pa_val PI_box]; vm_compute; discriminate)
               (HROMO fx1)
               (BoxLxCase3A.c3_segA (fx := fx1) (PI := PI_box) B MT (LAWS fx1) MTL (TREADNAME fx1) HRNTR)
               POST i HRM1 HK).
  - intros fx1 i HJ HX.
    exact (BoxLxJoin.gb_join (fx := fx1) (PI := PI_box) (RO := RO) B (LAWS fx1) MT (TCHECK fx1)
             (ABCMP fx1) (ASTRNCMP fx1) (HISV fx1) (HGLOB fx1) HZERO HZ1 HZ2 HMCH (HROMO fx1) POST i HJ HX).
  - intros fx1 HR cx fp k acc ly3 S3 W3 ms3 md3 HB HJ HF HM HG.
    eapply SRr_mono.
    { exact (@BoxLxExit.gb_exit fx1 rc SK PI_box B MT (LAWS fx1) (TL fx1) MTL MTF (ML fx1) (ASF fx1) (FFL fx1)
               (AFREE4 fx1) (ASETF5 fx1) cx fp k acc ly3 S3 W3 ms3 md3 HB HJ HF HM HG). }
    intros W' c' _ HP. exact (gb_postF_of fx B MT fx1 cx W' c' HR HP).
Qed.
End h.

(* ---- the values pb_llvmf_libx names, at fuzz_boxreg.asan's literals ----
   So that the closing (lib/A/Prog/BoxClose.v, row W_ENTRY_A) instantiates pb_llvmf_libx with its own constants
   (BOX_GLOBS, BOX_MSITES, BOX_FSITES, BOX_RN_MALLOC_RA, BOX_RLO / BOX_RHI, BXL0) by rewriting only. *)
Section i. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma box_bxg_lits : BX_G (PI := PI_box) = [(0x20cc0, 6); (0x20ce0, 1); (0x20d00, 5); (0x20d40, 3); (0x20d60, 1)].
Proof. unfold BX_G. cbn [pa_val PI_box]. vm_compute. reflexivity. Qed.
Lemma box_msites_lits : GB_MSITES = [0x1d0].
Proof. reflexivity. Qed.
Lemma box_fsites_lits : GB_FSITES = [0x6b4; 0xb60; 0xed0].
Proof. reflexivity. Qed.
Lemma box_rn_malloc_ra_lit : A_read_name_mallocRA (PI := PI_box) = 0x813a0.
Proof. unfold A_read_name_mallocRA, A_read_nameP. cbn [pa_val PI_box]. vm_compute. reflexivity. Qed.
Lemma box_relro_lits : pa_relro_lo (PAImg := PI_box) = 0x98958 /\ pa_relro_hi (PAImg := PI_box) = 0x99bb0.
Proof. cbn [pa_relro_lo pa_relro_hi PI_box]. vm_compute. split; reflexivity. Qed.
Lemma box_need_sum : forall MT : ameter_ops,
  GB_NEED MT = mo_malloc MT 288 + 64 * (mo_malloc MT 48 + mo_free MT) + mo_free MT.
Proof. intros MT. reflexivity. Qed.
End i.

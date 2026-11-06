(* m_file on fuzz_segconf.asan-ubsan (image B, pin c3796c0b38f3, twin 80e82127e8ca; 0x86140): the inner cut and the
   snprintf call-step statement of the half ENTRY 0x86140 -> 0x862ac of the segment S_MF_ENTRY (lib/B/Prog/mf_entry_d.v).
   A walk lane of the image-B m_file-family owner's G2B (a sub-lane). Statement text only: no instruction is executed here.
   proves no function (kind: the statements that split the half 0x86140 -> 0x862ac of m_file's image-B walk).

   The half is proved in two pieces at the cut MFE_P1 = 0x86270, the instruction after the UBSan trap branch 0x8626c:
     mf_entry_1.v   0x86140 -> 0x86270: the prologue, the class-1 side-stack frame (frame_alloc_1 at 0x861b4), the
                    frame header, the frame's 16 shadow bytes, the trap 0x8626c not taken; then the two pieces joined.
     mf_entry_1b.v  0x86270 -> 0x862a8 (128(s1) = c + 0x2000, a0 = c + 0x23b4, the label test 0x86288, a1 = 96, a2 =
                    "%s", 64(s1) = a0, a3 = the label), the snprintf call by MFE_SNP_STEP, and at the return 0x862ac
                    the cut MFE_MID of mf_entry_d.v at the FP state the wrapper returns.
     mf_entry_1s.v  MFE_SNP_STEP from image B's snprintf row (RtPFSeg.seg_asnprintf_realizes at
                    SIGMA SS___interceptor_trampoline_snprintf).

   WHAT HOLDS AT 0x86270 (MFE_P1_stmt): the frame (1, pos) taken, its header and shadow written, low.i's eight shadow
   bytes 0xf8 (MF_LOW_OFF), 120(s1) = FB, the flag pointer at FB + 120, the saved registers, and the block still
   holding the entry's model mv_mc v: that is mf_core at MF_LOW_OFF (mv_mc v). The text at the head of the loop
   (mf_loop at line 0, p = t, rest = s, cur = None). The registers: mf_regs_ex (sp = s1, gp, tp, s0 = sp0, s1,
   s2 = SHADOW_OFF, s7 = FB, s8 = shadow(FB)), s6 = the label pointer lp, s9 = c, s10 = t. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI04 YI09 YN3v YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require RtPFSeg.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable SegSyms SegList SegPa PaFx.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import m_file_c m_file_m mf_entry_d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require SegInstB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* 0x86270, the instruction after the UBSan trap branch 0x8626c (`lui a0,0x2`; 0x86270 - 0x86140 = 0x130) *)
Definition MFE_P1 : Z := AF_m_file + 0x130.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ seg_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Section e.
Variable B : asyms.

(* the inner cut 0x86270: what mf_entry_1.v proves there and mf_entry_1b.v starts from *)
Definition MFE_P1_stmt : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos,
mf_cx B v -> sa_frm0 -> mf_ls v lyc Sc ->
mf_core B v lyc Sc Wc memc mdc pos MF_LOW_OFF (mv_mc v) ->
mf_loop v Wc memc (mv_mc v) None 0 (mv_t v) (mv_s v) ->
(* every byte of every heap block of the entry still holds its entry value (nothing 0x86140-0x86270 writes a
   heap block: the label, when it is a heap object, keeps its bytes even inside the mconf block) *)
(forall b m a, In (b, m) (ablocks B (mv_ly v) (mv_S v)) -> b <= a < b + req_size m ->
  rdW Wc memc a = rdW (mv_W v) (mv_mem v) a) ->
mf_regs_ex B v lyc pos regs1 ->
getr regs1 22 = w64 (mv_lp v) -> getr regs1 25 = w64 (mv_c v) -> getr regs1 26 = w64 (mv_t v) ->
mf_at B v Wc regs1 memc mdc MFE_P1.

(* the snprintf call 0x862a8, snprintf(c->reading, 96, "%s", w), from the wrapper's entry (the `jal` executed: pc =
   SIGMA SS___interceptor_trampoline_snprintf, ra = BASE + MFE_RET_SNP, sp = s1, a0 = c + MC_READING, a1 = 96, a2 =
   the literal "%s", a3 = w, the C string txt: the label lp, or the literal "reac-pw.conf" when the label is NULL):
   at the FP state fx1 the wrapper returns, c->reading holds snprintf's text and its NUL, nothing else changed
   outside the callee's window [s1 - SEG_SNP_K, s1) *)
Definition MFE_SNP_STEP : Prop :=
forall v lyc Sc Wc (regsc : bvmap 5 word) memc mdc pos (w : Z) (txt : list Z),
mf_cx B v -> mf_ls v lyc Sc -> sa_frm0 ->
ajournal SEGS B SegInstB.STK_m_file (mv_sp v) (M_FILE_FP (mv_c v) (mv_k0 v) (mf_final v)) (mv_ly v) (mv_S v)
  (mv_W v) (mv_mem v) (mv_md v) [(1, pos)] lyc Sc Wc memc mdc 0 ->
Permutation (ablocks B lyc Sc) (ablocks B (mv_ly v) (mv_S v)) ->
sa_addr (rdW Wc memc) (mv_c v) seg_spec.SEG_M_SIZE -> sa_tail (rdW Wc memc) (mv_c v + seg_spec.SEG_M_SIZE - 1) ->
0 < w -> sa_str (rdW Wc memc) w txt -> sa_addr (rdW Wc memc) w (Z.of_nat (length txt) + 1) ->
Z.of_nat (length txt) <= 65535 ->
(sa_heap B lyc Sc w (Z.of_nat (length txt) + 1) \/ sa_fframe lyc Sc w (Z.of_nat (length txt) + 1) \/
 sa_img SEGS B w (Z.of_nat (length txt) + 1)) ->
sa_disj w (seg_spec.cstr_span w txt) (mv_c v + seg_spec.MC_READING) 96 ->
getr regsc 2 = w64 (mf_s1 (mv_sp v)) -> getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
getr regsc 1 = Z_to_bv 64 (BASE + MFE_RET_SNP) ->
getr regsc 10 = w64 (mv_c v + seg_spec.MC_READING) -> getr regsc 11 = w64 96 ->
getr regsc 12 = w64 (SegInstB.seg_litA_fz F_s) -> getr regsc 13 = w64 w ->
(forall (fx1 : YK11.FPState) (regs2 : bvmap 5 word) mem2 md2,
  fxrel fx fx1 ->
  ajournal SEGS B SegInstB.STK_m_file (mv_sp v) (M_FILE_FP (mv_c v) (mv_k0 v) (mf_final v)) (mv_ly v) (mv_S v)
    (mv_W v) (mv_mem v) (mv_md v) [(1, pos)] lyc Sc Wc mem2 md2 0 ->
  aregs_preserved regsc regs2 ->
  sa_zs (rdW Wc mem2) (mv_c v + seg_spec.MC_READING) (snprintf_s 96 F_s [AS txt] ++ [0]) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (mf_s1 (mv_sp v) - RtPFSeg.SEG_SNP_K <= a < mf_s1 (mv_sp v)) ->
    ~ (mv_c v + seg_spec.MC_READING <= a <
       mv_c v + seg_spec.MC_READING + Z.of_nat (length (snprintf_s 96 F_s [AS txt])) + 1) ->
    rdW Wc mem2 a = rdW Wc memc a) ->
  SRr SEGS Wc (mkCfg (@mkst fx1 regs2 (Z_to_bv 64 (BASE + MFE_RET_SNP)) mem2 (seg_rom SEGS)) md2)
    (MF_POST (fx := fx1) B v)) ->
SRr SEGS Wc (mkCfg (mkst regsc (Z_to_bv 64 (SIGMA SS___interceptor_trampoline_snprintf)) memc (seg_rom SEGS)) mdc)
  (MF_POST B v).

End e.
End f.
End d.

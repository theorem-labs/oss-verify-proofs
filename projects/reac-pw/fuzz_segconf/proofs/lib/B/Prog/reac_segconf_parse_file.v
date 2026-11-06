(* reac_segconf_parse_file (reac_segconf.c:120-296) on reac-pw/fuzz_segconf's ASan+UBSan image B (fuzz_segconf.asan-ubsan,
   pin c3796c0b38f3, twin 80e82127e8ca; 0x87e38, 5312 bytes, 1328 instructions, 41 inline checks, 34 UBSan trap
   branches to the `unimp` at 0x891c8, 53 calls, a 352-byte real frame and a class-5 side-stack frame of 1152 bytes):
   the walk proving reac_segconf_parse_file_contract (lib/B/Prog/reac_segconf_parse_file_c.v, the B-kit copy lane's B copy of
   the image-A owner's image-independent text, closed against G3 FINAL at 6f783602b5e3) at image B's numbers. The
   image-B composition and assembly lanes of the image-B G3 walk owner, 2026-10-30.
    ADAPTED from the image-A G3 walk owner's image-A split (lib/A/Prog/pf_pieces.v and pf_compose.v on working
    branches) and the unit owner's UBSan piece walks (lib/U/Prog/pf_*.v on working branches),
   re-derived on image B's code as 16 segments (lib/B/Prog/pf_pieces.v, the image-B piece statements at 80a6c9c97a8b: its head comment
   holds the B cut table, the trap facts and the positional names checked) and one composition (lib/B/Prog/pf_comp.v,
   pf_pieces_give_contract_holds).
   The theorem is the composition applied to the 16 segment statements S_B1 .. S_B12 (with S_B5 = S_B5h /\ S_B5t),
   each given by its lane's theorem over ONE set of callee and record hypotheses (below):
     S_B1   pf_seg_B1.S_B1_holds      (pb1,  0x87e38-0x87edc,   41 insns: ENTRY -> FTAKEN, the frame take)
     S_B2   pf_seg_B2.S_B2_holds      (pb2,  102: FTAKEN -> FRAME)
     S_B3   pf_seg_B3.S_B3_holds      (pb3,  0x88074-0x881f8 + 0x891cc-0x891f8, 108: FRAME -> HEAD / DONE; T01, T02)
     S_B4   pf_seg_B4.pf_seg_B4_holds (pb4,  0x89114-0x891cc + 0x891f8-0x89224, 57: DONE -> the return, the release)
     S_B5   pf_seg_B5.pf_seg_B5_holds (pb5, 116: HEAD -> LONG / HDR / KEY / TAIL; TAIL -> HEAD (pred n) / DONE;
            T03-T05, T07-T09)
     S_B6   pf_seg_B6.pf_seg_B6_holds (pb6,  29: LONG, REF3 -> TAIL; T06)
     S_B7   pf_seg_B7.S_B7_holds      (pb7,  101: HDR -> SEG / TAIL; HREF, REFTL, CLR -> TAIL; T10, T13, T19)
     S_B8a  pf_seg_B8a.pf_seg_B8a_holds (pb8a, 61: SEG -> NEW / FOUND / REFTL; T28, T29)
     S_B8b  pf_seg_B8b.S_B8b_holds    (pb8b, 98: NEW, FOUND, PROV2 -> TAIL; T32-T34)
     S_B9   pf_seg_B9.S_B9_holds      (pb9,  131: KEY -> ROLE / MODEL / IGN / REF3 / HREF / TAIL; KREF -> TAIL; T11,
            T12, T14-T16)
     S_B10a pf_seg_B10a.S_B10a_holds  (pb10a, 61: ROLE -> INTENT; T17, T20)
     S_B10b pf_seg_B10b.S_B10b_holds  (pb10b, 89: INTENT -> TAIL; T30)
     S_B11a pf_seg_B11a.S_B11a_holds  (pb11a, 91: MODEL -> MISS / LOWOUT; T18, T21, T22)
     S_B11b pf_seg_B11b.S_B11b_holds  (pb11b, 98: MISS -> KREFM; T23-T27)
     S_B11c pf_seg_B11c.S_B11c_holds  (pb11c, 44: KREFM, LOWOUT -> TAIL)
     S_B12  pf_seg_B12.S_B12_holds    (pb12, 101: IGN -> KREF / PROV2; T31)
   41 + 102 + 108 + 57 + 116 + 29 + 101 + 61 + 98 + 131 + 61 + 89 + 91 + 98 + 44 + 101 = 1328 instructions; the
   34 trap branches are discharged in the segments named.
   THE SECTION HYPOTHESES, one per distinct statement (the lanes' names for the same statement in brackets; the
   call targets are listing terms, pf_pieces.v's list before `Section s`), each at every FP state where it says so:
     MALLOC5     astack_malloc_realizes 5 (lib/B/YG0d.v), the frame take                    B1 [ASM5]
     MALLOCP     stack_malloc_progressP B (lib/B/YCbq.v)                                    B1 [SMP]
     FREE5       RtStack.astack_free_cls_realizes at SS___asan_stack_free_5, 5               B4 [ASF5]
     SHADOWF8    RtShadow.aset_shadow_realizes at SS___asan_set_shadow_f8, 0xf8              B2, B5 [ASHF8]
     SHADOW00    RtShadow.aset_shadow_realizes at SS___asan_set_shadow_00, 0x00              B5 [ASH00]
     MEMCPY      aintrin_realizes OCpy at SS___asan_memcpy (lib/B/YG0d.v)                    B5 [AMEMCPY]
     MEMSET      aintrin_realizes OSet at SS___asan_memset (lib/B/YG0d.v)                    B3 [AMEMSET], B8b [MEMSET]
     SNPRINTF    RtFormat.asnprintf_realizes at SS___interceptor_trampoline_snprintf, gotwA, guardA
                   B3, B11a, B11b [ASNPRINTF], B8b [SNP], B10b [ASNP]
     STRSPN      RtString.astrspn_realizes at SS___interceptor_trampoline_strspn, gotwA, guardA   B6 [STRSPN]
     STRCMP      RtString.astrcmp_realizes at SS___interceptor_trampoline_strcmp              B8a [ASTRCMP]
     STRCHR      RtSeg.astrchr_realizes at SS___interceptor_trampoline_strchr                 B5, B7, B9 [ASTRCHR]
     STRLEN      RtString.astrlen_realizes at SS___interceptor_trampoline_strlen              B5, B7, B9 [ASTRLEN]
     STRCASECMP  RtSeg.astrcasecmp_realizes at SS___interceptor_trampoline_strcasecmp         B9 [ASTRCASECMP],
                   B12 [ASCMP]
     STRNCASECMP RtSeg.astrncasecmp_realizes at SS___interceptor_trampoline_strncasecmp       B7 [ANCASE]
     BCMP        abcmp_realizes at SS___interceptor_trampoline_bcmp (lib/B/YG0d.v)          B10b [ABCMP]
     REFUSE      refuse_contract at BASE + AF_refuse, STK_refuse, RLO_A, RHI_A, seg_litA_rc, gotwA, guardA
                   B6, B7, B9 [REFUSE], B8b, B10b, B11c [REF]
     TRIM        trim_contract at BASE + AF_trim, STK_trim, RLO_A, RHI_A                     B5, B7, B9 [TRIM]
     BYTOKEN     reac_box_catalogue_by_token_contract at BASE + AF_reac_box_catalogue_by_token,
                   STK_reac_box_catalogue_by_token, RLO_A, RHI_A, catA                       B11a [BYTOKEN]
     CATALOGUE   reac_box_catalogue_contract at BASE + AF_reac_box_catalogue, STK_reac_box_catalogue, catA
                                                                                             B11b [CAT]
     TL          PALib B (B's SegPaLib.v: the GOT words and cells of the runtime)    B1, B5, B6, B7, B8a, B9, B12
     TLF         PALibF B (B's PaLibF.v: the uar cell, the stack-malloc targets)             B1
     VRO         seg_val_relro (B's SegObj.v: the read-only range)                 B1, B6, B7, B8b, B9, B10b, B11c
     OBJ         seg_val_objs (B's SegObj.v: the listing objects)
                   B3, B7, B8a, B8b, B9, B10b, B11b, B11c, B12 [OBJ], B11a [VO]
     SIGP        seg_sig_prog (B's SegObj.v: the program call targets)
                   B5, B6, B7, B8b, B9, B10b, B11a, B11b, B11c
     SSPX        the stack-protector cells at every AR state                       B1, B6, B7, B8b, B9, B10b, B11c
   SSPX stays a hypothesis here; SegRecCells.seg_rec_cells discharges it at the close.
   IMAGE B'S PARAMETER VALUES (lib/B/Prog/SegInstB.v, the image-B harness owner 1f771e2f2066; pf_pieces.pf_B_values checks them by
   computation): the entry BASE + AF_reac_segconf_parse_file (= seg_text + 0x3078 = 0x87e38, B's SegList.v);
   STK_reac_segconf_parse_file = 12832; RLO_A = 0xa1c60, RHI_A = 0xa3f08 (.data.rel.ro start .. .got end of the
   twin); catA = 0xa20a0 (fuzz_catalogue); gotwA = 0xa3e98 (the GOT word of the stack-protector guard), guardA =
   0x5ff838; seg_litA_rc (the 38 literals of PARSE_FILE_LITS at their image-B addresses, the same as image A's). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI04 YI09 YN3v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05 YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require RtFormat RtString RtSeg RtShadow RtStack.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable SegSyms SegList SegAddr SegPa
  SegObj SegGlob SegPaLib PaLibF.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase refuse_c trim_c
  reac_box_catalogue_c reac_box_catalogue_by_token_c reac_segconf_parse_file_c SegInstB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import pf_pieces pf_comp.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require pf_seg_B1 pf_seg_B2 pf_seg_B3 pf_seg_B4
  pf_seg_B5 pf_seg_B6 pf_seg_B7 pf_seg_B8a pf_seg_B8b pf_seg_B9 pf_seg_B10a pf_seg_B10b pf_seg_B11a pf_seg_B11b
  pf_seg_B11c pf_seg_B12.
Import ListNotations.
Local Open Scope Z_scope.

Section d.
Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ seg_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Variable B : asyms.
(* the runtime entries: the side-stack frame of class 5, the shadow, the checked memcpy / memset *)
Hypothesis MALLOC5 : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc SEGS B 5.
Hypothesis MALLOCP : stack_malloc_progressP B.
Hypothesis FREE5 : forall fx0 : YK11.FPState,
  @RtStack.astack_free_cls_realizes fx0 rc SEGS B (SIG SS___asan_stack_free_5) 5.
Hypothesis SHADOWF8 : forall fx0 : YK11.FPState,
  @RtShadow.aset_shadow_realizes fx0 rc SEGS B (SIG SS___asan_set_shadow_f8) 0xf8.
Hypothesis SHADOW00 : forall fx0 : YK11.FPState,
  @RtShadow.aset_shadow_realizes fx0 rc SEGS B (SIG SS___asan_set_shadow_00) 0.
Hypothesis MEMCPY : forall fx0 : YK11.FPState, @aintrin_realizes fx0 rc SEGS B OCpy (SIG SS___asan_memcpy).
Hypothesis MEMSET : forall fx0 : YK11.FPState, @aintrin_realizes fx0 rc SEGS B OSet (SIG SS___asan_memset).
(* the libc interceptors at the listing's trampolines *)
Hypothesis SNPRINTF : forall fx0 : YK11.FPState,
  @RtFormat.asnprintf_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_snprintf) gotwA guardA.
Hypothesis STRSPN : forall fx0 : YK11.FPState,
  @RtString.astrspn_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_strspn) gotwA guardA.
Hypothesis STRCMP : forall fx0 : YK11.FPState,
  @RtString.astrcmp_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_strcmp).
Hypothesis STRCHR : forall fx0 : YK11.FPState,
  @RtSeg.astrchr_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_strchr).
Hypothesis STRLEN : forall fx0 : YK11.FPState,
  @RtString.astrlen_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_strlen).
Hypothesis STRCASECMP : forall fx0 : YK11.FPState,
  @RtSeg.astrcasecmp_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_strcasecmp).
Hypothesis STRNCASECMP : forall fx0 : YK11.FPState,
  @RtSeg.astrncasecmp_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_strncasecmp).
Hypothesis BCMP : forall fx0 : YK11.FPState, @abcmp_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_bcmp).
(* the program callees at BASE + AF_<F> with SegInstB's numbers *)
Hypothesis REFUSE : forall fx0 : YK11.FPState, refuse_contract (fx := fx0) SEGS B (BASE + AF_refuse) STK_refuse
  RLO_A RHI_A seg_litA_rc gotwA guardA.
Hypothesis TRIM : forall fx0 : YK11.FPState, trim_contract (fx := fx0) SEGS B (BASE + AF_trim) STK_trim RLO_A RHI_A.
Hypothesis BYTOKEN : forall fx0 : YK11.FPState, reac_box_catalogue_by_token_contract (fx := fx0) SEGS B
  (BASE + AF_reac_box_catalogue_by_token) STK_reac_box_catalogue_by_token RLO_A RHI_A catA.
Hypothesis CATALOGUE : forall fx0 : YK11.FPState, reac_box_catalogue_contract (fx := fx0) SEGS B
  (BASE + AF_reac_box_catalogue) STK_reac_box_catalogue catA.
(* the listing's records and objects, the stack-protector cells, the image facts *)
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis VRO : seg_val_relro (PI := PI).
Hypothesis OBJ : seg_val_objs (PI := PI).
Hypothesis SIGP : seg_sig_prog (PI := PI).
Hypothesis SSPX : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> sa_ssp (rdW W mem) gotwA guardA.

Section w.
Context {fx : YK11.FPState}.
Theorem reac_segconf_parse_file_walk : reac_segconf_parse_file_contract SEGS B (BASE + AF_reac_segconf_parse_file)
  STK_reac_segconf_parse_file RLO_A RHI_A seg_litA_rc catA gotwA guardA.
Proof.
exact (pf_pieces_give_contract_holds B
  (pf_seg_B1.S_B1_holds B MALLOC5 MALLOCP TL TLF VRO SSPX)
  (pf_seg_B2.S_B2_holds B SHADOWF8)
  (pf_seg_B3.S_B3_holds B SNPRINTF MEMSET OBJ)
  (pf_seg_B4.pf_seg_B4_holds B FREE5)
  (pf_seg_B5.pf_seg_B5_holds B TL SIGP STRCHR STRLEN MEMCPY SHADOW00 SHADOWF8 TRIM)
  (pf_seg_B6.pf_seg_B6_holds B STRSPN REFUSE SIGP VRO TL SSPX)
  (pf_seg_B7.S_B7_holds B VRO SIGP OBJ SSPX TL REFUSE TRIM STRCHR STRNCASECMP STRLEN)
  (pf_seg_B8a.pf_seg_B8a_holds B STRCMP TL OBJ)
  (pf_seg_B8b.S_B8b_holds B SNPRINTF MEMSET REFUSE SIGP OBJ VRO SSPX)
  (pf_seg_B9.S_B9_holds B STRCHR STRLEN STRCASECMP TRIM REFUSE SIGP OBJ VRO SSPX TL)
  (pf_seg_B10a.S_B10a_holds B)
  (pf_seg_B10b.S_B10b_holds B BCMP SNPRINTF REFUSE SIGP OBJ VRO SSPX)
  (pf_seg_B11a.S_B11a_holds B BYTOKEN SNPRINTF OBJ SIGP)
  (pf_seg_B11b.S_B11b_holds B CATALOGUE SNPRINTF SIGP OBJ)
  (pf_seg_B11c.S_B11c_holds B REFUSE SIGP OBJ VRO SSPX)
  (pf_seg_B12.S_B12_holds B STRCASECMP TL OBJ)).
Qed.
End w.
End d.

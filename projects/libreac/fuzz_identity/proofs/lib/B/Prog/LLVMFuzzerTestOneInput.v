(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the contract of projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACfn.v:33-69
   (tfib_lib_pre_x, tfib_lib_post_x, tfib_lib_contract_x) restated for libreac/fuzz_identity's ASan+UBSan
   build: the module paths are this unit's lib.B, the image is the position-abstract one (pa_segs,
   BASE + AF_LLVMFuzzerTestOneInput of identb_listing), the library shape and every constant of the unit's
   relocated core are parameters of the Section, and the measured needs of this build's entry (events, live
   bytes, stack) are stated beside it. *)
(* LLVMFuzzerTestOneInput (fuzz_identity.asan-ubsan 0x80774 = BASE + AF_LLVMFuzzerTestOneInput, 0x208c bytes, 2083
   slots): the ASan+UBSan-build contract of the harness entry, and the Section the walk is proved in. No walk here.

   The text is lib/A/Prog/LLVMFuzzerTestOneInput.v's, which is cgif lib/A/ACfn.v:33-69
   (tfib_lib_pre_x, tfib_lib_post_x, tfib_lib_contract_x) over the position-abstract image (pa_segs,
   BASE + AF_LLVMFuzzerTestOneInput) at identity's library shape. What image B changes: the listing layer
   (lib/B/Prog/IdentB*.v, ibsym names), the stack the run needs (buf_of is a call on B, and every allocator call
   needs ASTACK), the image objects (the B listing numbers them differently and B reads " (" from the image),
   and the callee contracts (lib/B/Prog/<callee>.v). Besides, this file takes what the walk needs and the A text
   does not state yet: the allocator call traces in the allocator's universe (amalloc04_rule / afree04_rule and
   buf_of's call contexts), and the image constants the run reads (llvmf_img).

   The form this file must meet is tfib_lib_contract_x (lib/ReusableB/YCfn.v:58), the same shape
   as A's.

   The Section keeps `Context {SK : YI16.sink_head}` generic; the composition passes the asan-ubsan sink head
   explicitly, with `@`: SK := the relocated AE2k's tfib_sink_head, whose sk_ofl_head is the image's `ofl_head`
   (0x5f8948 on fuzz_identity.asan-ubsan, read from the unstripped ELF's .symtab with pyelftools), never
   lib/Reusable/YI5b.v's plain instance. This file does not load YI5b (lib/Prog/Seg/Agree.v requires it), so
   outside the Section no sink_head instance exists and `@YI16.sk_ofl_head _` does not resolve. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YI09 YI00 YG0s YI16 YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
PaRun PaShadow PaJournal IdentBase IdentRo YC4b YC81.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
IdentBSyms IdentBList IdentBPa IdentBPaLib IdentBFrame IdentBCJ IdentBProgSig YC1g YC1h YC45 YC85.
(* The callee contracts (lib/B/Prog/<callee>.v on the integration branch), used by their own names. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require
buf_of check_str put_dec reac_box_catalogue reac_box_catalogue_defect reac_box_family_of reac_box_family_stem
reac_box_name reac_identity_fw_str reac_identity_init reac_identity_ingest reac_identity_reac_ver_str.
(* The plain model of reac_box_name: the stem strings (bn_STEM). *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require disco_box_name_model.
(* The wrappers' and the shadow fill's contracts. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Rt Require Import StrlenDef StrcmpDef MemchrDef SetShadowDef.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- what the run needs, measured from the B listing --------------------------------- *)
(* Allocator events: per record (at most 64) the payload copy (malloc at 0x80c90) and the guard copy (buf_of at
   0x80d0c, EV_BUF_OF = 1), each freed (0x80da0, 0x815d4): 4; then the five output buffers (buf_of at 0x8189c,
   0x818f0, 0x81a5c, 0x81a68, 0x81a74), each freed (0x818e8, 0x81924, 0x82364, 0x8236c, 0x82374): 10. No other
   callee allocates. *)
Definition EV_LLVMF : Z := 4 * 64 + 10.
(* Live heap bytes at the peak: one record's payload copy (<= 255) and its guard copy (Z.max (n + 1) 1 <= 256). *)
Definition LIVE_LLVMF : Z := 255 + 256.
(* Machine stack below sp0: the code itself touches 336 + 16 + REAC_BOX_NAME_STK = 336 + 16 + 336 + 2 * ESTACK
   = 8880 bytes (the 320-byte frame aligned down to 32, then reac_box_name's two stack-argument words at
   0x81a78 / 0x81abc and its own window), but the allocator rules ask for more: afree04_rule asks
   ASTACK - o <= STK with o = mf - sp0 >= -336 (the seven free calls), and buf_of is called at sp = mf with
   BUF_OF_STK = 16 + ASTACK (buf_of.v:49), which is the deepest. So the window the walk needs is
   336 + 16 + ASTACK. (A has 336 + ASTACK: there buf_of is inlined, so only its own malloc asks ASTACK - o.)
   8880 <= 336 + 16 + ASTACK, so the stack-argument words are inside the window on both builds. *)
Definition STK_LLVMF : Z := 336 + 16 + ASTACK.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg identb_listing}.
#[local] Notation SEGS := (@pa_segs _ identb_listing PI).
#[local] Notation VAL := (@pa_val _ identb_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ identb_listing PI).
#[local] Notation BASE := (@pa_val _ identb_listing PI A_TEXT).
Definition A_LLVMFuzzerTestOneInputP : Z := BASE + AF_LLVMFuzzerTestOneInput.
Section c.
#[local] Notation rd W mem := (mrestrict (w_H W) mem).

(* ---- the image's symbols, the meter, the read-only range ------------------------------------------------ *)
(* All four are parameters, as in the A text; the composition fixes them (grant's form at
   lib/A/AGrantT.v:28-40). For image B it instantiates B := identity's B
   record, MT := ameter_triv, XM_LIB = XN_LIB := XL0 = fun _ => 0, and RLO, RHI := 0x9b080, 0x9d388 (the
   .data.rel.ro start and the .got end, i.e. exactly IdentBImg.v's pa_relro_lo / pa_relro_hi), at which HRO
   below is the identity. The top it then proves is
   `forall rc, tfib_lib_contract_x_all rc identity_shape <B record> ameter_triv XL0 XL0 RLO RHI`. *)
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.

(* ---- the library shape (cgif lib/YO09.v:17; identity's is lib/Prog/Seg/Agree.v:32 checksum_shape_ag) ----- *)
Variable LS : lib_shape.
Hypothesis HLIBK : forall pl fs K, @LIBK LS pl fs K = K (LL 0 fs []).

(* ---- identity's relocated ACfn constants, image B (cgif ACfn.v:21-25; fuzz_identity.asan-ubsan: A_LLVMF
       0x80774, RA_LLVMF 0x80670, A_EMPTY 0x5d7920, LLVMF_STK 32768, EV_LIB 2000, LIVE_LIB 2^33) ------------- *)
Variables RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB : Z.
(* What the walk needs of them, measured above. *)
Hypothesis HSTK : STK_LLVMF <= LLVMF_STK.
Hypothesis HEV : EV_LLVMF <= EV_LIB.
Hypothesis HLIVE : LIVE_LLVMF <= LIVE_LIB.

(* ---- identity's relocated lib/Reusable/YE00.v and YE01.v ------------------------------------------------- *)
(* cgif YE00.v:30 Record asink_syms; the walk only carries a value of it through the two kept-lemmas below. *)
Variable asink_syms_T : Type.
Variable KS : asink_syms_T.
(* cgif YE00.v:121 (Section with segs and K). *)
Variable asink_none : list Segment -> asink_syms_T -> (word -> option byte) -> Model -> Prop.
(* cgif YE01.v:139 (Section with segs and K). *)
Variable ameta_inv : list Segment -> asink_syms_T -> alayout -> (word -> option byte) -> Z -> Prop.
(* cgif YE01.v:188 (Section with segs and B). *)
Variable arodata_okS : list Segment -> asyms -> Z -> Z -> reader -> Prop.

(* ---- the contract (cgif lib/A/ACfn.v:33-46) -------------------------------------------------------------- *)
Definition tLLVMFuzzerTestOneInput_pre (regs : bvmap 5 word) (ly : alayout) (S : astate) (W : world SEGS)
(mem : word -> option byte) (md : Model) (p n : Z) (pl : list byte) (M : Z) : Prop :=
afn_pre SEGS B LLVMF_STK ly S W regs mem md [] /\
raZ regs = RA_LLVMF /\
getr regs 10 = w64 p /\ getr regs 11 = w64 n /\
((n = 0 /\ p = A_EMPTY) \/ (0 < n < 2 ^ 26 /\ In (p, n) (ablocks B ly S))) /\
n = Z.of_nat (length pl) /\ garr8 SEGS (rd W mem) p (map (fun b : byte => bv_unsigned b) pl) /\
frames S = [] /\ st_nev S + EV_LIB <= EV_MAX /\ blocks_bytes S + LIVE_LIB <= LIVE_MAX /\
arodata_okS SEGS B RLO RHI (aview SEGS (w_H W) mem) /\
asink_none SEGS KS (rd W mem) md /\
fd_lookup (m_fds md) (alloc_fd (m_fds md)) = None /\
Fs.fs_sorted (m_fs md) = true /\
ameta_inv SEGS KS ly (rd W mem) M /\
mo_ok MT S (XM_LIB n).

(* cgif lib/A/ACfn.v:47-58 *)
Definition tLLVMFuzzerTestOneInput_post (regs : bvmap 5 word) (ly : alayout) (S : astate) (W : world SEGS)
(mem : word -> option byte) (md : Model) (p n M : Z) (l : lleaf)
(ly' : alayout) (S' : astate) (W' : world SEGS) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model)
(k : Z) : Prop :=
ajournal SEGS B LLVMF_STK (spZ regs) [sink_token] ly S W mem md [] ly' S' W' mem' md' k /\ k <= EV_LIB /\
aregs_preserved regs regs' /\ getr regs' 10 = w64 0 /\
Permutation (ablocks B ly' S') (ablocks B ly S) /\
(forall fd, fd_lookup (m_fds md') fd = fd_lookup (m_fds md) fd) /\
m_fs md' = ll_fs l /\ ll_ret l = 0 /\ ll_out l = [] /\ Fs.fs_sorted (ll_fs l) = true /\
asink_none SEGS KS (rd W' mem') md' /\
ameta_inv SEGS KS ly' (rd W' mem') M /\
mo_le MT S S' (XN_LIB n) /\
(forall i, 0 <= i < n -> aview SEGS (w_H W') mem' (p + i) = aview SEGS (w_H W) mem (p + i)).

(* cgif lib/A/ACfn.v:59-69, at LS *)
Definition tLLVMFuzzerTestOneInput_spec : Prop :=
forall ly S (W : world SEGS) (regs : bvmap 5 word) mem md p n pl M (K : lleaf -> TSet),
AI SEGS (w_H W) (w_A W) md ->
tLLVMFuzzerTestOneInput_pre regs ly S W mem md p n pl M ->
(forall (l : lleaf) (W' : world SEGS) (c' : config),
wle W W' -> AI SEGS (w_H W') (w_A W') (cfg_model c') ->
(exists ly' S' regs' mem' md' k,
c' = cfg_at SEGS RA_LLVMF regs' mem' md' /\
tLLVMFuzzerTestOneInput_post regs ly S W mem md p n M l ly' S' W' regs' mem' md' k) ->
srealizes SEGS c' (K l)) ->
srealizes SEGS (cfg_at SEGS A_LLVMFuzzerTestOneInputP regs mem md) (@LIBK LS pl (m_fs md) K).

(* ---- the hypotheses the walk takes ------------------------------------------------------------------------ *)
(* the image, the allocator, the side stack *)
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis PSIG : identb_prog_sig_ok (PI := PI).
Hypothesis ML : model_laws (as_universe B).
Hypothesis MTL : ameter_laws MT.
Hypothesis MTF : ameter_fs_laws MT.
(* A program call leaves the meter where it was. Identity's program-callee posts carry no meter fact (cgif's
   do: ACa3.v:310-320, `mo_le MT Sc S' 0`), so the walk takes this once instead of refitting the proved callees.
   It holds of the closer's meter: at MT := ameter_triv (fuzz_grant's YCbp.v:17, mo_le := fun _ _ _ => True) it is
   fun _ _ => I. With MTL's mo_le_trans and mo_ok_step it re-establishes acut's two meter clauses after a call. *)
Hypothesis HMT0 : forall s s' : astate, mo_le MT s s' 0.
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
(* arodata_okS over [RLO, RHI) gives the callees' arodata_okP over the relro range; at
   RLO, RHI := pa_relro_lo, pa_relro_hi the two bodies are the same text and this is fun _ H => H. *)
Hypothesis HRO : forall rdr, arodata_okS SEGS B RLO RHI rdr -> arodata_okP SEGS pa_relro_lo pa_relro_hi B rdr.
(* the registered globals this walk and its callees read (IdentRo.v:117) *)
Variable G : list (Z * Z).
Hypothesis GM : globs_marked SEGS B G.
Hypothesis IV : img_shadow_vis SEGS B.
(* The entry's own tables, from fuzz_identity.asan-ubsan's registered globals (objects of identb_listing,
   IdentBAddr.v): HW_TABLE 0x21000 (36), switch.table.LLVMFuzzerTestOneInput 0x9b460 (24), BOX_CATALOGUE
   0x9b520 (3256 = 11 rows of 296), and the literals "x" 0x20f80 (2), " (" 0x20fa0 (3), " in / " 0x20fc0 (7),
   " out)" 0x20fe0 (6), "REAC" 0x210c0 (5). *)
Hypothesis G_HW : In (VAL (A_OBJ 6), 36) G.
Hypothesis G_SW : In (VAL (A_OBJ 7), 24) G.
Hypothesis G_CAT : In (VAL (A_OBJ 28), 3256) G.
Hypothesis G_X : In (VAL (A_OBJ 4), 2) G.
Hypothesis G_PAREN : In (VAL (A_OBJ 9), 3) G.
Hypothesis G_IN : In (VAL (A_OBJ 10), 7) G.
Hypothesis G_OUT : In (VAL (A_OBJ 11), 6) G.
Hypothesis G_REAC : In (VAL (A_OBJ 8), 5) G.

(* Meter room for the run's allocator events: each is a malloc of at most 256 bytes or a free, and the walk
   counts EV_LLVMF of them (A LLVMFuzzerTestOneInput.v:180-184: the room must be left event by event, so a
   boundary carries mo_ok MT S2 ((EV_LLVMF - k) * MEV) with MEV = mo_malloc MT 256 + mo_free MT). *)
Hypothesis HXM : forall n, EV_LLVMF * (mo_malloc MT 256 + mo_free MT) <= XM_LIB n.
Hypothesis HXN : forall n, EV_LLVMF * (mo_malloc MT 256 + mo_free MT) <= XN_LIB n.

(* The call traces of the run's allocator calls are in the allocator's universe: amalloc04_rule and
   afree04_rule ask `In (call_trace0 pc0 regsT ch) (as_universe B)` of every call (YC5d.v:66, :86), and PALib
   does not fix the universe. The form is cgif's (ACeb.v:39, ACee.v:106-110; buf_of.v:111): the context is
   `raZ regs :: spine ch` at the call, and `call_trace_of_spine` rewrites call_trace0 into it. The entry is
   entered with an empty frame chain (afn_pre ... []) and its own record is the only one the chain can hold,
   so each context is [the call's return address; RA_LLVMF] when chain_pre gives the entry's frame record
   (fp, RA_LLVMF, v), and [the call's return address] when it gives no record (bad_next at sp0: afn_pre bounds
   sp0 by ly_top only), so each site has both. The direct calls: malloc at 0x80c90 (fuzz_dup); free at 0x80da0,
   0x815d4, 0x818e8, 0x81924, 0x82364, 0x8236c, 0x82374. B has no inlined malloc: the other seven allocations go
   through buf_of, whose own walk takes the universe fact for CTX_BUF_OF (buf_of.v:111). A segment's file states
   HUMM / HUMF as its own Hypotheses, with this text; _inv.v's llvmf_univ_call / llvmf_univ_call0 turn them into
   amalloc04_rule's and afree04_rule's premise. (A states the same thing.)
    *)
Definition LLVMF_MALLOC_RAS : list Z := [0x520].
Definition LLVMF_FREE_RAS : list Z := [0x630; 0xe64; 0x1178; 0x11b4; 0x1bf4; 0x1bfc; 0x1c04].
Definition LLVMF_MALLOC_CTX : list (list Z) :=
map (fun o => [BASE + o; RA_LLVMF]) LLVMF_MALLOC_RAS ++ map (fun o => [BASE + o]) LLVMF_MALLOC_RAS.
Definition LLVMF_FREE_CTX : list (list Z) :=
map (fun o => [BASE + o; RA_LLVMF]) LLVMF_FREE_RAS ++ map (fun o => [BASE + o]) LLVMF_FREE_RAS.
Hypothesis HUMM : forall c, In c LLVMF_MALLOC_CTX ->
In (firstn kUnwindMax (pc_malloc_ra0 (as_code B)
:: flat_map (fun r => if r =? pc_malloc_ra0 (as_code B) then [] else [r]) c)) (as_universe B).
Hypothesis HUMF : forall c, In c LLVMF_FREE_CTX ->
In (firstn kUnwindMax (pc_free_ra0 (as_code B)
:: flat_map (fun r => if r =? pc_free_ra0 (as_code B) then [] else [r]) c)) (as_universe B).
(* buf_of's call contexts (raZ :: spine ch at its entry, buf_of.v:57), with and without the entry's record: the
   calls at 0x80d0c, 0x8189c, 0x818f0, 0x81a5c, 0x81a68, 0x81a74. *)
Definition BUF_OF_RAS : list Z := [0x59c; 0x112c; 0x1180; 0x12ec; 0x12f8; 0x1304].
Definition CTX_BUF_OF : list (list Z) :=
map (fun o => [BASE + o; RA_LLVMF]) BUF_OF_RAS ++ map (fun o => [BASE + o]) BUF_OF_RAS.

(* The image constants the run reads, in any state whose read-only image is intact. The position-abstract
   image fixes the code (pi_check) but not the data, so the walk takes these; the composition proves them on
   fuzz_identity.asan-ubsan from its segments (all are read-only data: .rodata or the relro range).
   - object 5 (0x10370): the reciprocal 0x03f03f03f03f03f1 that computes input[0] mod 65 (0x80b30 .. 0x80b48);
   - HW_TABLE (object 6, 0x21000) and the library's HW_FAMILY (object 17, reac_box_family_of's table): the same
     three rows (family, eight hw bytes) of fuzz_identity.c:131-135 / reac_box_facts.h:29-35; the family check at
     0x817f0 compares the two; HW_TABLE lies 64 bytes inside the image range, which IdentRo.ro_hull asks for the
     shadow hull of the bcmp at 0x817a4 (as in A);
   - switch.table.LLVMFuzzerTestOneInput (object 7, stem_of): three pointers to "S-0808", "S-1608", "S-4000S",
     and "REAC" (object 8) for any other family (0x81bd0 .. 0x81c38);
   - the display literals " (", " in / ", " out)" (objects 9, 10, 11) (0x81ec8, 0x81f68, 0x8200c);
   - switch.table.reac_box_family_stem (object 18): reac_box_family_stem's premises (its table in a usable
     range, reac_box_family_stem.v:100) and three non-null entries (0x81a34 aborts on a null stem);
   - reac_box_name's image premise (reac_box_name.v:117 rbn_img);
   - BOX_CATALOGUE (object 28): 8-aligned (the UBSan alignment check at 0x822b4) and each row's fields as
     reac_box_catalogue_defect.v:137-144 asks them for e = the row (the call at 0x822a8). *)
Definition HW_ROWS : list Z :=
[1; 0; 0; 0; 0; 0; 0; 1; 0; 0; 0; 0;
 2; 0; 0; 0; 0; 0; 0; 2; 0; 3; 0; 2;
 3; 0; 0; 0; 0; 0; 0; 2; 0; 1; 0; 2].
Definition llvmf_img (W : world SEGS) (mem : word -> option byte) : Prop :=
val_mem SEGS (rd W mem) (VAL (A_OBJ 5)) 8 0x03f03f03f03f03f1 /\
garr8 SEGS (rd W mem) (VAL (A_OBJ 6)) HW_ROWS /\
IMG_LO + 64 <= VAL (A_OBJ 6) /\ VAL (A_OBJ 6) + 100 <= IMG_TOP /\
garr8 SEGS (rd W mem) (VAL (A_OBJ 17)) HW_ROWS /\
VAL (A_OBJ 7) mod 8 = 0 /\
(exists s1 s2 s3,
val_mem SEGS (rd W mem) (VAL (A_OBJ 7)) 8 s1 /\
val_mem SEGS (rd W mem) (VAL (A_OBJ 7) + 8) 8 s2 /\
val_mem SEGS (rd W mem) (VAL (A_OBJ 7) + 16) 8 s3 /\
reac_box_name.rbn_imgstr B G W mem s1 (disco_box_name_model.bn_STEM 1) /\
reac_box_name.rbn_imgstr B G W mem s2 (disco_box_name_model.bn_STEM 2) /\
reac_box_name.rbn_imgstr B G W mem s3 (disco_box_name_model.bn_STEM 3)) /\
garr8 SEGS (rd W mem) (VAL (A_OBJ 8)) (disco_box_name_model.bn_STEM 0 ++ [0]) /\
garr8 SEGS (rd W mem) (VAL (A_OBJ 9)) [32; 40; 0] /\
garr8 SEGS (rd W mem) (VAL (A_OBJ 10)) [32; 105; 110; 32; 47; 32; 0] /\
garr8 SEGS (rd W mem) (VAL (A_OBJ 11)) [32; 111; 117; 116; 41; 0] /\
in_zs B (VAL (A_OBJ 18)) 24 /\
(exists t1 t2 t3,
val_mem SEGS (rd W mem) (VAL (A_OBJ 18)) 8 t1 /\
val_mem SEGS (rd W mem) (VAL (A_OBJ 18) + 8) 8 t2 /\
val_mem SEGS (rd W mem) (VAL (A_OBJ 18) + 16) 8 t3 /\
(0 < t1 < 2 ^ 64) /\ (0 < t2 < 2 ^ 64) /\ (0 < t3 < 2 ^ 64)) /\
reac_box_name.rbn_img B G W mem /\
VAL (A_OBJ 28) mod 8 = 0 /\
(forall r, 0 <= r < reac_box_catalogue.BOX_COUNT ->
IMG_LO <= VAL (A_OBJ 28) + 296 * r + 8 /\ VAL (A_OBJ 28) + 296 * r + 24 <= IMG_TOP /\
(VAL (A_OBJ 28) + 296 * r + 24 <= VAL (A_OBJ 1) \/ VAL (A_OBJ 1) + 8 <= VAL (A_OBJ 28) + 296 * r + 8) /\
(VAL (A_OBJ 28) + 296 * r + 24 <= VAL (A_OBJ 31) \/ VAL (A_OBJ 31) + 8 <= VAL (A_OBJ 28) + 296 * r + 8) /\
exists I O P sP,
-2 ^ 31 <= I < 2 ^ 31 /\ -2 ^ 31 <= O < 2 ^ 31 /\ 0 <= P < 2 ^ 64 /\
val_mem SEGS (rd W mem) (VAL (A_OBJ 28) + 296 * r + 8) 8 P /\
val_mem SEGS (rd W mem) (VAL (A_OBJ 28) + 296 * r + 16) 4 I /\
val_mem SEGS (rd W mem) (VAL (A_OBJ 28) + 296 * r + 20) 4 O /\
(P <> 0 -> reac_box_catalogue_defect.catd_rostr G W mem P sP)).
Hypothesis HIMG : forall (W : world SEGS) mem,
arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) -> llvmf_img W mem.

(* the runtime entries the reachable code calls (CONVENTIONS section 4; cgif lib/A/ACfj.v:96-111) *)
Hypothesis AMALLOC4 : amalloc04_rule SEGS B MT.
Hypothesis AFREE4 : afree04_rule SEGS B MT.
Hypothesis ASM4 : astack_malloc_realizes SEGS B 4.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis AMEMSET : aintrin_realizes SEGS B OSet (SIGMA IB___asan_memset).
Hypothesis AMEMCPY : aintrin_realizes SEGS B OCpy (SIGMA IB___asan_memcpy).
Hypothesis ABCMP : abcmp_realizes SEGS B (SIGMA IB___interceptor_trampoline_bcmp).
Hypothesis AMEMCHR : amemchr_realizes SEGS B (SIGMA IB___interceptor_trampoline_memchr).
Hypothesis ASTRLEN : astrlen_realizes SEGS B (SIGMA IB___interceptor_trampoline_strlen).
Hypothesis ASTRCMP : astrcmp_realizes SEGS B (SIGMA IB___interceptor_trampoline_strcmp).
(* The shadow-fill entry the frame release calls (0x823e8; lib/B/Rt/SetShadowDef.v:21). *)
Hypothesis ASSF5 : aset_shadow_realizes SEGS B (SIGMA IB___asan_set_shadow_f5) 0xf5.

(* The two lemmas of identity's relocated lib/A/ACfh.v the walk uses, with cgif's statements. *)
(* cgif ACfh.v:29-31 *)
Hypothesis AJ_FP_NIL : forall STK sp0 FP ly S W mem md own ly' S' W' mem' md' k,
ajournal SEGS B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
ajournal SEGS B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k.
(* cgif ACfh.v:162-164 *)
Hypothesis AJ_NIL_IO : forall STK sp0 ly S (W : world SEGS) mem md own ly' S' W' mem' md' k,
ajournal SEGS B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
m_fds md' = m_fds md /\ m_fs md' = m_fs md.
(* cgif ACfh.v:47-49: a run that keeps the allocator's invariant realizes the trace set it ends in. *)
Hypothesis SRZ_ENTER : forall (W : world SEGS) (c : config) (T : TSet),
AI SEGS (w_H W) (w_A W) (cfg_model c) ->
SRr SEGS W c (fun W' c' => AI SEGS (w_H W') (w_A W') (cfg_model c') -> srealizes SEGS c' T) ->
srealizes SEGS c T.
(* The two kept-lemmas of identity's relocated YE01, with cgif's statements (YE01.v:82-85, :153-155). *)
Hypothesis ASINK_NONE_KEPT : forall STK sp0 FP ly S W mem md own ly' S' W' mem' md' k,
ajournal SEGS B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
~ YI16.sink_open_fp FP ->
asink_none SEGS KS (rd W mem) md -> asink_none SEGS KS (rd W' mem') md'.
Hypothesis AMETA_INV_KEPT : forall STK sp0 FP ly S W mem md own ly' S' W' mem' md' k M,
ajournal SEGS B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
ameta_inv SEGS KS ly (rd W mem) M -> ameta_inv SEGS KS ly' (rd W' mem') M.

(* ---- the program callees -------------------------------------------------------------------------------- *)
(* Each at BASE + AF_<callee> inside its own file (reac_identity_init takes its address, reac_identity_init.v:73);
   PSIG relates the call slots' pa_sigma IB_<callee> to those addresses. *)
Hypothesis HCHK : check_str.tcheck_str_spec B.
Hypothesis HCAT : reac_box_catalogue.tcat_spec B.
Hypothesis HCATD : reac_box_catalogue_defect.treac_box_catalogue_defect_spec B G.
Hypothesis HSTEM : reac_box_family_stem.treac_box_family_stem_spec B.
Hypothesis HFWS : reac_identity_fw_str.treac_identity_fw_str_spec B.
Hypothesis HINIT : reac_identity_init.treac_identity_init_spec B (BASE + AF_reac_identity_init).
Hypothesis HING : reac_identity_ingest.treac_identity_ingest_spec B.
Hypothesis HFAM : reac_box_family_of.treac_box_family_of_spec B.
Hypothesis HVS : reac_identity_reac_ver_str.treac_identity_reac_ver_str_spec B.
Hypothesis HPD : put_dec.tput_dec_spec B.
Hypothesis HBN : reac_box_name.treac_box_name_spec B G.
(* buf_of is a call on B (inlined on A): its contract at the six call contexts above. *)
Hypothesis HBUF : buf_of.tbuf_of_spec B MT CTX_BUF_OF.

End c.
End b.
End a.

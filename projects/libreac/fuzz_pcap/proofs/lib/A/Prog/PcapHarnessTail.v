(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: lib/B twin of lib/A/Prog/PcapSourceClose.v: pcap_source_close (fuzz_pcap.asan-ubsan
   0x81d4c, listing offset AF_pcap_source_close = 0x15c4, 31 instructions) on libreac v1.9.0's ASan+UBSan build, walked
   against lib/A's contract.

   The code is lib/A's ASan code (fuzz_pcap.asan 0x81e90, 27 instructions) with two UBSan guards and a register swap
   (measured: pcap-ubsan-inventory.md (sha256 5b607b62e337; internal record), row G6 and the pcap_source_close row of (c)). After
   the 32-byte frame and the saves of ra, s0 and s1, 0x81d5c `beqz a0` branches to the `unimp` at 0x81db4 when ps is
   null, 0x81d60 `mv s0,a0` (above the GOT load here), and 0x81d64 `andi a0,a0,7` / 0x81d68 `bnez a0` branch to the same
   `unimp` when ps is not 8-aligned. The shadow base is then loaded through the GOT word 0x996f8 (object 1; through a0,
   where the ASan code uses a1) from the cell 0xa17b8 (object 15). The rest is the ASan code at other pcs: the shadow
   check of ps's 8 bytes (0x81d80 `lbu`, 0x81d84 `bnez` to the error path at 0x81db8), f = ps->f (0x81d88), the test of
   f (0x81d8c `beqz` to 0x81da0), the call of the fclose wrapper's 4-byte jump (0x81d90 `jal
   __interceptor_trampoline_fclose`, 0x4161c), the second shadow check (0x81d94, 0x81d98 `bnez` to the error path at
   0x81dc0), ps->f = NULL (0x81d9c `sd zero,0(s0)`), the restores and the return (0x81db0).

   THE GUARDS. The walk's first symbolic run decides both, from the facts on a0 = ps that cl_entry proves (atom 10: ps
   >= 4096 and ps mod 2^3 = 0; ps >= 4096 because ps lies in a frame of the caller (frames_bounds), which gives the
   statement's ps <> 0; the alignment is the statement's ps mod 8 = 0):
     0x81d5c: decide_cond2 (Reusable/YP0e.v:932) through decide_eq (Reusable/YP0m.v:658-672), whose SOff / SLit arm
              (:665-666) tests ranges_disjoint (:653): ps's range [4096, ...] is disjoint from 0, so the branch is not
              taken;
     0x81d68: s_and_ptr (Reusable/YP0m.v:969-980) rewrites ps & 7 to 0 from the alignment fact, so `bnez` sees 0 and is
              not taken.
   These are the decisions of the released UBSan proof for the v1.8 image (proofs/libreac/fuzz_pcap/lib/U/Prog/
   pcap_source_close.v on origin/ossv/recipes c8557374ad2e): close_closed :43 (if_false, premise bv_unsigned a0 <> 0 at
   :23) and :45-46 (ub_align A8, premise bv_unsigned a0 mod 8 = 0 at :23), close_pro :82 and :84-85 (premises :58).

   The contract is lib/A's, not a copy (the shared-text rule): pb_pcap_source_closeX proves lib/A's image-generic
   AC.tpcap_source_close_specX (with AC.tpcap_source_close_post and AC.tclose_kept) at this image's segments SEGS and
   relro window pa_relro_lo / pa_relro_hi of the lib/B PAImg instance (on the pin PcapRelro.PCAP_RLO /
   PcapRelro.PCAP_RHI, lib/B/Prog/PcapRelro.v), at a = BASE + AF_pcap_source_close of the lib/B listing. The image-free constants
   (TPCAP_SOURCE_CLOSE_STK, EV_CLOSE, tclose_fblk) and lemmas are lib/A's too, through AC. The fclose wrapper's contract
   is the Section hypothesis AFCLOSE, of lib/A/Stdio/PFclose.v's image-generic afclose_source_spec type at this image.
   There is no lib/B/Stdio/PFclose.v (that statement takes the image as parameters). AFCLOSE is discharged by the
   asan-ubsan instance of a Theorem Labs lane's fclose walk lib/A/Stdio/WFclose.v, whose lib/B walk twin is
   lib/B/Stdio/WFclose.v (lib/B/Stdio/PFcloseInstB.v's inst_AFCLOSE_U composes it with lib/B/Stdio/WFcloseI.v).
   getr / mkst / seg_rom come from YK11; nothing from lib/Lib is imported. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/B/Prog/PcapSourceClose.v, with its module names changed; 3497 of its 3557 lines of code are new or changed and 570 lines of the source are left out. *)
(* The tail of fuzz_pcap's entry walk (LLVMFuzzerTestOneInput, 0x807c8, ASan build of libreac v1.9.0): the phase
   lemmas from PcapEntryPhases.GI_K5 to the `ret`, each in PcapEntryDefs.pe_from's shape
   `pe_from SK B MT KS POST GI_next -> pe_from SK B MT KS POST GI_self` (pe_from_ret for the frame given back).
   Every number is read from the original v1.9.0 pin fuzz_pcap.asan (sha256 b7a91d9b1fb0017d...;
   symbols from fuzz_pcap.asan (sha256 36da3052c383); capstone disassembly); the comment beside a number names its
   instruction.

   The walks (PcapEntryDefs.v's stage list):
     W   tail_W    PP_K5 0x8107c: the reader's answer and g_file_len (tail_W5); at <> |F|: the end-of-walk check
                   loop PP_KW 0x81224 (tail_KW, by induction on |F| - e over segH / segB / segD / segC); both end at
                   0x810a0 with want = the reader's answer and close the reader (tail_close6, 0x810a8) -> PP_K6
     R1  tail_R1   PP_K6 0x810ac: ld s2,0x58(s1); ld a0,0(s2); bnez a0 (abort); a1 = the path literal;
                   jal pcap_source_open (0x810c4)                                        -> PP_K7 0x810c8
     R2  tail_R2   PP_K7 0x810c8: bnez a0 (abort); a0..a3 = ps, buf, cap, 0; jal pcap_source_next (0x810dc) -> PP_K8
     R3  tail_R3   PP_K8 0x810e0: bne a0,s10 (abort); mv a0,s2; jal pcap_source_close (0x810e8) -> PP_K9 0x810ec
     R4  tail_R4   PP_K9 0x810ec: a0..a3 = ps, buf, cap, 0; jal pcap_source_next (0x810fc, ps->f = 0) -> PP_K10 0x81100
     R5  tail_R5   PP_K10 0x81100: bne a0,-1 (abort); mv a0,s6; jal free (0x8110c, buf)    -> PP_K11 0x81110
     R6  tail_R6   PP_K11 0x81110: mv a0,s3; jal free (0x81114, the copy b)               -> PP_K12 0x81118
     R7  tail_R7   PP_K12 0x81118: ld s9,8(s1); sb 0xf8,0xc(s9) (ts out of scope)         -> PP_K12r 0x81124
     BT  tail_K12r PP_K12r 0x81124: sb 0xf8,4/5/6(s9) (ps out of scope)                    -> PP_leave 0x81134
         tail_leave PP_leave 0x81134: the frame given back (flag store 0x8118c), restores -> PP_ret (pe_from_ret)
     ret tail_ret  PP_ret 0x81214: ret, to PcapEntryDefs.pe_post (pe_from_ret form)
   Every branch to the abort (0x81340) is refuted from the cut's facts. The machine-stack arm of the epilogue
   (beqz s4 0x81140 -> 0x81194) is refuted too: s4 = F >= 4096, the side-stack frame pe_from states, which the
   prologue gets from AR_const_law (use-after-return cell = 1) and the stack_malloc rule at 0x80838.
   W's four shadow checks (bnez 0x81244 / 0x8125c / 0x81274 / 0x8128c; their slow-block edges bge 0x81304 /
   0x81310 / 0x8131c and the fall-through jal at 0x8132c into __asan_report_load1) are decided at the bnez by the
   token engine from segB's shent (18, 8, 12): range_addressable over b+e+8 .. b+e+11, which lies in the copy
   (b, |F|) because 0x81228 left e + 16 <= |F| (range_addressable_of_block).

   The journal of pe_from is W_journal.v's ajournal_gx over pe_G (the two harness globals); each walk opens it
   (gx_open: the inner donor journal from a start memory memS that agrees with c_mem outside pe_G), runs the engine,
   the allocator rule and the callee contracts (which are in cgif's caller-journal form and need the harness's frame
   in their `own`) on the inner journal, and repacks it (gx_pack0) for the next phase.

   Section hypotheses, each of the exact type of the fact it stands for, discharged by the composer:
     LAWS, TL, MLAWS     the allocator laws, the listing's runtime symbols, the meter laws (the kit's own);
     ASIL                asource_img_laws SK SEGS B KS (PSourceMeta.v; discharged with the stream symbols);
     AFREE               afree04_rule SEGS B MT (YC5d.v), lifted by PaJournalFs.afree04_sub_fs;
     CLOSE               tpcap_source_close_specX SK SEGS pa_relro_lo pa_relro_hi B KS MT
                         (BASE + AF_pcap_source_close) (PcapSourceClose.pb_pcap_source_closeX);
     NEXTS               tpcap_source_next_specX SK SEGS pa_relro_lo pa_relro_hi NX_STK B MT KS
                         (BASE + AF_pcap_source_next) (PcapSourceNextDefs.v of the next lane, cf12207f2a1);
     HRO                 ro_below_ofl SEGS pa_relro_lo pa_relro_hi (PcapBase.v's class: the read-only bytes lie below
                         the open-file list head, 0x5f4f88 on the pin), for PcapBase.arodata_ok_journalP;
     ML, ASF, FFL        model_laws (as_universe B), astack_free_law SEGS B, frame_flag_lawP SEGS B: the frame
                         give-back (PcapFrame.aj_flag_store_pi; AsanAPI's aa_model / aa_stack_free, as cgif);
     MFSL                ameter_fs_laws MT: the meter ignores the frame state (mo_le_set_fs_r at the give-back);
     OPENS               tpcap_source_open_specX (PcapSourceOpenDefs.v) at the second open, with FM_RA, CTX, ROI and
                         HROI (the read-only image predicate from arodata_okP), HPATH (the path literal's shadow, from
                         AR), HCTX (the two call spines), HFMU (fmemopen's malloc traces);
     HGLEN               pa_val (A_HI 8) + 0x618 = pa_val (A_OBJ 4) (g_file_len through the auipc base, as PcapHarnessA). *)
From OSSVerify.libreac.fuzz_pcap Require Symbols.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
(* The phase data first: PcapEntry pulls in modules whose short names (YI16, YK11, ...) also exist under lib/U, so
   the lib/Reusable imports below must come after it for those short names to mean lib/Reusable's. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require PcapEntry PcapEntryDefs PcapEntryPhases PcapSourceClose
  PcapSourceNextDefs.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog Require pcap_source_struct pcap_source_struct_next.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog.Slot Require PWalkDef.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0s YI16 YG0s.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YM05 PcapImgEnd YImgTop YE00 YE01 YG0p YC5d.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PaTable PaSym PaShadow.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PaRun.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PaJournal PcapSyms PcapList PcapAddr PcapPa PcapPaLib PcapBase YC4b YC81 YC1g YC1h YC85 PcapFrame PaJournalFs.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PSource PSourceMeta.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A Require Import W_journal.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapSourceNextDefs PcapFuzzFopenDefs
  PcapSourceOpenDefs.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapEntry PcapEntryA PcapEntryDefs
  PcapEntryPhases.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapSourceClose.
Module PST := OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog.pcap_source_struct.
Module PWD := OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog.Slot.PWalkDef.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- generic facts ---------------------------------------------------------------------------------------- *)

Lemma ms_eta `{fx : YK11.FPState} : forall ms : machine_state,
  ms_fregs ms = fp_regs -> ms_svc_pending ms = None -> ms_resv ms = None -> ms_fcsr ms = fp_csr ->
  ms = mkst (ms_regs ms) (ms_pc_val ms) (ms_mem ms) (ms_rom ms).
Proof. intros [] H1 H2 H3 H4; cbn in *; subst; reflexivity. Qed.

Lemma nodup_of_split : forall {A} (l : list A),
  (forall l1 x l2 l3, l = l1 ++ x :: l2 ++ x :: l3 -> False) -> List.NoDup l.
Proof.
  intros A l. induction l as [|a t IH]; intros H; [apply List.NoDup_nil|]. apply List.NoDup_cons.
  - intros Hin. apply List.in_split in Hin as (t1 & t2 & ->). apply (H [] a t1 t2). reflexivity.
  - apply IH. intros l1 x l2 l3 E. apply (H (a :: l1) x l2 l3). rewrite E. reflexivity.
Qed.

Lemma notin_of_perm_nodup : forall {A} (l L : list A) x,
  List.NoDup l -> Permutation l (L ++ [x]) -> ~ List.In x L.
Proof.
  intros A l L x Hnd Hp Hin. apply (Permutation_NoDup Hp) in Hnd.
  apply List.NoDup_remove_2 in Hnd. rewrite app_nil_r in Hnd. exact (Hnd Hin).
Qed.

Lemma frame_of_nil : forall E (m m' : word -> option byte), frame_of E [] m m' -> m' = m.
Proof. intros E m m' H. apply functional_extensionality. intros x. apply H. intros (r & Hr & _). destruct Hr. Qed.

(* A run over read-only regions (every window empty) changes no byte. *)
Lemma frame_of_ro : forall E rs (m m' : word -> option byte),
  (forall r, In r rs -> YP09.r_whi r <= YP09.r_wlo r) -> frame_of E rs m m' -> m' = m.
Proof.
  intros E rs m m' Hro H. apply functional_extensionality. intros x. apply H.
  intros (r & Hin & Hr). pose proof (Hro r Hin). lia.
Qed.

Lemma rdword_ext : forall (rd rd' : reader) a,
  (forall i, 0 <= i < 8 -> rd' (a + i) = rd (a + i)) -> rdword rd' a = rdword rd a.
Proof.
  intros rd rd' a H. unfold rdword.
  assert (H0 : rd' a = rd a) by (specialize (H 0 ltac:(lia)); rewrite Z.add_0_r in H; exact H).
  rewrite H0, (H 1), (H 2), (H 3), (H 4), (H 5), (H 6), (H 7) by lia. reflexivity.
Qed.

Lemma pe_sp1_bounds : forall sp0, sp0 mod 16 = 0 ->
  pe_sp1 sp0 mod 32 = 0 /\ sp0 - 240 <= pe_sp1 sp0 <= sp0 - 224.
Proof.
  intros sp0 H. unfold pe_sp1, PE_MFRAME.
  pose proof (Z.div_mod (sp0 - 224) 32 ltac:(lia)) as D. pose proof (Z.mod_pos_bound (sp0 - 224) 32 ltac:(lia)) as M.
  pose proof (Z.div_mod sp0 16 ltac:(lia)) as D2. rewrite H in D2.
  split; [rewrite Z.mul_comm; apply Z_mod_mult|]. lia.
Qed.

Lemma lay_eqs : forall n ly ly', layout_le n ly ly' ->
  ly_F ly' = ly_F ly /\ ly_top ly' = ly_top ly /\ ly_stk_lo ly' = ly_stk_lo ly /\ ly_stk_hi ly' = ly_stk_hi ly.
Proof. intros n ly ly' (_ & _ & _ & _ & _ & EF & _ & _ & Etop & Eslo & Eshi & _). auto. Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg pcap_listing}.
#[local] Notation SEGS := (@pa_segs _ pcap_listing PI).
#[local] Notation VAL := (@pa_val _ pcap_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ pcap_listing PI).
#[local] Notation BASE := (@pa_val _ pcap_listing PI A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Variable KS : asource_syms.
Variable POST : ecx -> world SEGS -> config -> Prop.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis MLAWS : ameter_laws MT.
Hypothesis ASIL : asource_img_laws SK SEGS B KS.
Hypothesis AFREE : afree04_rule SEGS B MT.
Hypothesis CLOSE : tpcap_source_close_specX SK SEGS pa_relro_lo pa_relro_hi B KS MT (BASE + AF_pcap_source_close).
Hypothesis NEXTS : tpcap_source_next_specX SK SEGS pa_relro_lo pa_relro_hi NX_STK B MT KS (BASE + AF_pcap_source_next).
Variable FM_RA : Z.
Variable CTX : list (list Z).
Variable ROI : (word -> option byte) -> Prop.
Hypothesis OPENS : tpcap_source_open_specX SK SEGS pa_relro_lo pa_relro_hi (pa_val (A_OBJ 3)) (pa_val (A_OBJ 4))
  (pa_val (A_OBJ 2)) ROI B KS MT FM_RA CTX (BASE + AF_pcap_source_open).
Hypothesis HROI : forall (W : world SEGS) mem,
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) -> ROI (mrestrict (w_H W) mem).
Hypothesis HPATH : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF (pa_val (A_OBJ 3)) 13 /\
  shadow_hull_vis (aview SEGS (w_H W) mem) (pa_val (A_OBJ 3)) 13.
Hypothesis HCTX : In [BASE + PP_K7; RA_LLVMF] CTX /\ In [BASE + PP_K7] CTX.
Hypothesis HFMU : In [pc_malloc_ra0 (as_code B)] (as_universe B) /\
  (forall c, In c CTX -> In (firstn kUnwindMax (pc_malloc_ra0 (as_code B) ::
     flat_map (fun r => if r =? pc_malloc_ra0 (as_code B) then [] else [r]) (FM_RA :: c))) (as_universe B)).
Hypothesis HGLEN : pa_val (A_HI 8) + PE_GLEN_LO = pa_val (A_OBJ 4).
Context {HRO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Hypothesis ML : model_laws (as_universe B).
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis MFSL : ameter_fs_laws MT.
Let RUN := paj_run (SK := SK) B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_pcap) (PI := PI).
Let RUNTOP := SRr_run_to_pi_AJ B LAWS.
Let RUNF := aj_flag_store_pi B LAWS ML ASF FFL.
Let RUNTO := paj_run_to (SK := SK) B LAWS.

Definition SB_T : Z := 0x7fff8000.
Definition TBx : sv := SLit SB_T.
Definition TBspan : Z * Z := (SB_T, SB_T + 2 ^ 44 - 1).
Definition nofacts : facts := mkFacts [] [] [].

Lemma ablocks_nodup : forall ly S W mem md, AR SEGS B ly S W mem md -> List.NoDup (ablocks B ly S).
Proof.
  intros ly S W mem md HAR. apply nodup_of_split. intros l1 x l2 l3 E.
  pose proof (sep_blocks_pos SEGS B LAWS ly S W mem md x x l1 l2 l3 HAR E) as D.
  assert (Hin : In x (ablocks B ly S)) by (rewrite E; apply in_or_app; right; left; reflexivity).
  destruct x as [p n].
  destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (_ & _ & _ & _ & _ & _ & Hn).
  pose proof (req_size_pos n ltac:(lia)) as [R _].
  unfold zdisjoint, block_rng in D. cbn [fst snd] in D. lia.
Qed.

(* The stack facts every walk of the tail uses: the caller's sp0, the realigned s1, and the window. *)
Lemma tail_geo : forall cx, pe_base SK B MT KS cx ->
  spZ (c_regs cx) mod 16 = 0 /\ c_sp1 cx mod 32 = 0 /\
  spZ (c_regs cx) - 240 <= c_sp1 cx <= spZ (c_regs cx) - 224 /\
  alloc_ceiling <= ly_stk_lo (c_ly cx) /\ ly_stk_lo (c_ly cx) + LLVMF_STK <= spZ (c_regs cx) /\
  spZ (c_regs cx) <= ly_stk_hi (c_ly cx) /\ ly_stk_hi (c_ly cx) <= 2 ^ 47 /\
  ly_bot (c_ly cx) + LLVMF_STK < spZ (c_regs cx) + ASTACK /\
  spZ (c_regs cx) <= ly_top (c_ly cx) /\ ly_top (c_ly cx) <= ly_stk_hi (c_ly cx).
Proof.
  intros cx HB.
  destruct HB as ((_ & _ & _ & _ & _ & Hstk & _) & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hsp1 & _).
  destruct Hstk as (Hal & Hs0 & Hceil & Hlo & Hhi & H47 & Hbot & Htop & Htop2).
  destruct (pe_sp1_bounds _ Hal) as [M1 M2]. rewrite Hsp1.
  repeat split; assumption || lia.
Qed.

(* The harness's journal is W_journal.v's ajournal_gx over pe_G: a donor journal from a start memory memS that agrees
   with c_mem outside g_file / g_file_len. Those two globals are image bytes, so above the allocator's ceiling memS
   and c_mem agree. *)
Lemma gagree_high : forall cx memS a, pe_base SK B MT KS cx ->
  gagree pe_G (w_H (c_W cx)) (c_mem cx) memS -> alloc_ceiling <= a < 2 ^ 64 ->
  aview SEGS (w_H (c_W cx)) memS a = aview SEGS (w_H (c_W cx)) (c_mem cx) a.
Proof.
  intros cx memS a HB Hag Ha. pose proof asan_consts as (C1 & _). apply (aview_gagree SEGS pe_G _ _ _ a Hag).
  apply inGb_false. rewrite unsigned_lit_small by lia. intros HG.
  pose proof (pa_obj_img 4 ltac:(lia)) as O4. pose proof (pa_obj_img 2 ltac:(lia)) as O2.
  unfold pcap_img_end, IMG_TOP in O4, O2.
  unfold pe_G in HG. apply inG_cons in HG as [HG|HG]; [|apply inG_cons in HG as [HG|HG]; [|exact (inG_nil a HG)]];
    unfold in_zr in HG; cbn [fst snd] in HG; lia.
Qed.

(* The chain the harness hands to a callee: its own frame record, when it lies below the stack top. *)
Lemma pch_achain : forall cx own memS ly3 S3 W3 mem3 md3 k,
  pe_base SK B MT KS cx ->
  ajournal SEGS B LLVMF_STK (spZ (c_regs cx)) [sink_token] (c_ly cx) (c_S cx) (c_W cx) memS (c_md cx)
    own ly3 S3 W3 mem3 md3 k ->
  gagree pe_G (w_H (c_W cx)) (c_mem cx) memS ->
  rdword (aview SEGS (w_H W3) mem3) (spZ (c_regs cx) - 8) = Some (raZ (c_regs cx)) ->
  rdword (aview SEGS (w_H W3) mem3) (spZ (c_regs cx) - 16) = Some (s0Z (c_regs cx)) ->
  achain ly3 (aview SEGS (w_H W3) mem3) (c_sp1 cx) (spZ (c_regs cx)) (pch cx).
Proof.
  intros cx own memS ly3 S3 W3 mem3 md3 k HB HJ Hag R8 R16.
  pose proof (tail_geo cx HB) as (Hal & Hs1 & Hs1b & Hceil & Hlo & Hhi & H47 & Hbot & Htop & Htop2).
  unfold LLVMF_STK in Hlo, Hbot.
  pose proof HB as ((_ & _ & Hra4 & _ & _ & _ & _ & Hch & _) & _).
  pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & F1 & _).
  destruct (lay_eqs _ _ _ Hly) as (_ & Etop & _ & _).
  apply (achain_ly_top (c_ly cx)); [exact Etop|].
  assert (H8 : spZ (c_regs cx) mod 8 = 0).
  { pose proof (Z.div_mod (spZ (c_regs cx)) 16 ltac:(lia)) as D. rewrite Hal, Z.add_0_r in D.
    apply Z.mod_divide; [lia|]. exists (2 * (spZ (c_regs cx) / 16)). lia. }
  assert (Hc0 : alloc_ceiling <= spZ (c_regs cx)) by lia.
  assert (Ht64 : ly_top (c_ly cx) <= 2 ^ 64) by lia.
  unfold pch. destruct (Z.ltb_spec (spZ (c_regs cx) + 16) (ly_top (c_ly cx))) as [Ht|Ht].
  - assert (HK : forall a, spZ (c_regs cx) <= a < 2 ^ 64 ->
      aview SEGS (w_H W3) mem3 a = aview SEGS (w_H (c_W cx)) (c_mem cx) a)
      by (intros a Ha; rewrite <- (gagree_high cx memS a HB Hag) by lia; apply F1; lia).
    assert (Ht2 : spZ (c_regs cx) < ly_top (c_ly cx) - 16) by lia.
    assert (Hs2 : c_sp1 cx + 16 <= spZ (c_regs cx)) by lia.
    exact (achain_push _ _ _ _ _ _ _ _ Hch Ht64 HK R8 R16 Hra4 Hc0 H8 Ht2 Hs2).
  - left. split; [right; left; lia | reflexivity].
Qed.

(* The harness's journal opened (its inner donor journal, from a start memory that agrees with c_mem outside pe_G)
   and closed again: every walk below works on the inner journal and repacks it before the next phase. *)
Lemma gx_open : forall cx own ly' S' W' mem' md' k,
  ajournal_gx SEGS B pe_G 0 [] LLVMF_STK (spZ (c_regs cx)) [sink_token] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx)
    (c_md cx) own ly' S' W' mem' md' k ->
  exists memS, ajournal SEGS B LLVMF_STK (spZ (c_regs cx)) [sink_token] (c_ly cx) (c_S cx) (c_W cx) memS (c_md cx)
    own ly' S' W' mem' md' k /\ gagree pe_G (w_H (c_W cx)) (c_mem cx) memS.
Proof.
  intros cx own ly' S' W' mem' md' k (_ & _ & (memS & HJ & Hag) & _). exists memS.
  rewrite !Z.add_0_r in HJ. split; assumption.
Qed.

Lemma gx_pack0 : forall cx own memS ly' S' W' mem' md' k,
  ajournal SEGS B LLVMF_STK (spZ (c_regs cx)) [sink_token] (c_ly cx) (c_S cx) (c_W cx) memS (c_md cx)
    own ly' S' W' mem' md' k ->
  gagree pe_G (w_H (c_W cx)) (c_mem cx) memS ->
  ajournal_gx SEGS B pe_G 0 [] LLVMF_STK (spZ (c_regs cx)) [sink_token] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx)
    (c_md cx) own ly' S' W' mem' md' k.
Proof.
  intros cx own memS ly' S' W' mem' md' k HJ Hag.
  apply (ajournal_gx_pack SEGS B pe_G 0 [] LLVMF_STK (spZ (c_regs cx)) [sink_token] (c_ly cx) (c_S cx) (c_W cx)
    (c_mem cx) (c_md cx) own ly' S' W' mem' md' k memS); [unfold LLVMF_STK; lia | lia | | exact Hag | intros a Ha; lia].
  rewrite !Z.add_0_r. exact HJ.
Qed.

(* ---- what a callee keeps of the harness's bytes ---------------------------------------------------------- *)

(* The bytes of the body that every cut states and no callee may change: the saved registers, the spill slots
   s1+8 .. s1+120, the frame header and the frame's shadow, and the input. *)
Definition hfoot (cx : ecx) (fp a : Z) : Prop :=
  (spZ (c_regs cx) - 104 <= a < spZ (c_regs cx)) \/ (c_sp1 cx + 8 <= a < c_sp1 cx + 120) \/
  (pF cx fp <= a < pF cx fp + 24 \/ pF cx fp + 120 <= a < pF cx fp + 128) \/ (pSH cx fp <= a < pSH cx fp + 16) \/
  (c_p cx <= a < c_p cx + c_n cx).

Lemma tail_kept : forall (cx : ecx) fp W ms W' ms' sh,
  (forall a, hfoot cx fp a -> aview SEGS (w_H W') (ms_mem ms') a = aview SEGS (w_H W) (ms_mem ms) a) ->
  psaved cx W ms -> pheader cx fp W ms -> pshadow cx fp W ms sh -> length sh = PE_NSH ->
  garr8 SEGS (rdW W (ms_mem ms)) (c_p cx) (map (fun b : byte => bv_unsigned b) (c_pl cx)) ->
  pslots cx fp W ms ->
  psaved cx W' ms' /\ pheader cx fp W' ms' /\ pshadow cx fp W' ms' sh /\
  garr8 SEGS (rdW W' (ms_mem ms')) (c_p cx) (map (fun b : byte => bv_unsigned b) (c_pl cx)) /\
  pslots cx fp W' ms'.
Proof.
  intros cx fp W ms W' ms' sh HK (Hs8 & Hsj) (Hh0 & Hh8 & Hh16 & Hh120) Hsh Hlen Hin (P2 & P3 & P4 & P5 & P6 & P7 & P8).
  assert (RW : forall a, (forall i, 0 <= i < 8 -> hfoot cx fp (a + i)) ->
    rdword (aview SEGS (w_H W') (ms_mem ms')) a = rdword (aview SEGS (w_H W) (ms_mem ms)) a)
    by (intros a Ha; apply rdword_ext; intros i Hi; apply HK, Ha, Hi).
  split; [|split; [|split; [|split]]].
  - split.
    + rewrite RW; [exact Hs8|]. intros i Hi. unfold hfoot. left. lia.
    + intros j Hj. rewrite RW; [exact (Hsj j Hj)|]. intros i Hi. unfold hfoot. left. lia.
  - unfold pheader, PE_FLAGPTR in *.
    split; [|split; [|split]]; (rewrite RW; [assumption|]); intros i Hi; unfold hfoot; right; right; left;
    first [left; lia | right; lia].
  - intros i Hi. rewrite HK; [exact (Hsh i Hi)|]. unfold hfoot. right; right; right; left.
    rewrite Hlen in Hi. unfold PE_NSH in Hi. lia.
  - apply (garr8_frame SEGS _ _ _ _ Hin). intros a Ha. apply (mbyte_of_aview SEGS). apply HK.
    unfold hfoot. right; right; right; right. rewrite length_map in Ha. unfold c_n. lia.
  - unfold pslots, pslot, PS_PSP, PS_GLEN, PS_D, PS_SH, PS_F, PS_FK, PS_TSP in *.
    repeat split; (rewrite RW; [assumption|]); intros i Hi; unfold hfoot; right; left; lia.
Qed.

(* The body bytes the epilogue keeps: hfoot without the spill slots and the frame's shadow, which it rewrites. *)
Definition hfoot_ns (cx : ecx) (fp a : Z) : Prop :=
  (spZ (c_regs cx) - 104 <= a < spZ (c_regs cx)) \/
  (pF cx fp <= a < pF cx fp + 24 \/ pF cx fp + 120 <= a < pF cx fp + 128) \/
  (c_p cx <= a < c_p cx + c_n cx).

Lemma tail_kept_ns : forall (cx : ecx) fp W ms W' ms',
  (forall a, hfoot_ns cx fp a -> aview SEGS (w_H W') (ms_mem ms') a = aview SEGS (w_H W) (ms_mem ms) a) ->
  psaved cx W ms -> pheader cx fp W ms ->
  garr8 SEGS (rdW W (ms_mem ms)) (c_p cx) (map (fun b : byte => bv_unsigned b) (c_pl cx)) ->
  psaved cx W' ms' /\ pheader cx fp W' ms' /\
  garr8 SEGS (rdW W' (ms_mem ms')) (c_p cx) (map (fun b : byte => bv_unsigned b) (c_pl cx)).
Proof.
  intros cx fp W ms W' ms' HK (Hs8 & Hsj) (Hh0 & Hh8 & Hh16 & Hh120) Hin.
  assert (RW : forall a, (forall i, 0 <= i < 8 -> hfoot_ns cx fp (a + i)) ->
    rdword (aview SEGS (w_H W') (ms_mem ms')) a = rdword (aview SEGS (w_H W) (ms_mem ms)) a)
    by (intros a Ha; apply rdword_ext; intros i Hi; apply HK, Ha, Hi).
  split; [|split].
  - split.
    + rewrite RW; [exact Hs8|]. intros i Hi. unfold hfoot_ns. left. lia.
    + intros j Hj. rewrite RW; [exact (Hsj j Hj)|]. intros i Hi. unfold hfoot_ns. left. lia.
  - unfold pheader, PE_FLAGPTR in *.
    split; [|split; [|split]]; (rewrite RW; [assumption|]); intros i Hi; unfold hfoot_ns; right; left;
    first [left; lia | right; lia].
  - apply (garr8_frame SEGS _ _ _ _ Hin). intros a Ha. apply (mbyte_of_aview SEGS). apply HK.
    unfold hfoot_ns. right; right. rewrite length_map in Ha. unfold c_n. lia.
Qed.

(* The clauses a callee's post keeps (acall_kept / tclose_kept / topen_kept / nx_kept, clauses 1, 2 and 4), for the
   harness's body bytes, when its write set E misses them. *)
Lemma foot_kept : forall (cx : ecx) fp lyc Sc (W : world SEGS) (memc : word -> option byte) (W2 : world SEGS)
  (mem2 : word -> option byte) slo shi (E : Z -> Prop),
  pe_base SK B MT KS cx ->
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (slo <= a < shi) -> ~ E a ->
     aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a) ->
  (forall b m i, In (b, m) (ablocks B lyc Sc) -> 0 <= i < req_size m -> ~ E (b + i) ->
     aview SEGS (w_H W2) mem2 (b + i) = aview SEGS (w_H W) memc (b + i)) ->
  (forall cid pos a, In (cid, pos) (frames Sc) ->
     (in_zr a (frame_rng lyc (cid, pos)) \/ in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8)) ->
     ~ E a -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a) ->
  shi <= c_sp1 cx + 8 ->
  In (PE_CID, fp) (frames Sc) -> frame_addr lyc PE_CID fp = pF cx fp ->
  (0 < c_n cx -> In (c_p cx, c_n cx) (ablocks B lyc Sc)) ->
  (forall a, hfoot cx fp a -> ~ E a) ->
  forall a, hfoot cx fp a -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a.
Proof.
  intros cx fp lyc Sc W memc W2 mem2 slo shi E HB K1 K2 K4 Hshi Hfr Efa Hinb HE a Ha.
  pose proof (tail_geo cx HB) as (Hal & Hs1 & Hs1b & Hceil & Hlo & Hhi & H47 & Hbot & Htop & Htop2).
  unfold LLVMF_STK in Hlo.
  pose proof (HE a Ha) as HnE.
  destruct Ha as [Ha|[Ha|[Ha|[Ha|Ha]]]].
  - apply K1; [lia | lia | exact HnE].
  - apply K1; [lia | lia | exact HnE].
  - apply (K4 PE_CID fp a Hfr); [|exact HnE]. left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite Efa.
    change (fs_frame_bytes PE_CID) with 128. lia.
  - apply (K4 PE_CID fp a Hfr); [|exact HnE]. right. unfold in_zr. cbn [fst snd]. rewrite Efa.
    change (fs_frame_bytes PE_CID / 8) with 16. unfold pSH, shadow_of_addr in Ha. unfold shadow_addr. lia.
  - destruct (Z_lt_le_dec 0 (c_n cx)) as [Hn|Hn]; [|lia].
    replace a with (c_p cx + (a - c_p cx)) by lia. apply (K2 (c_p cx) (c_n cx) (a - c_p cx) (Hinb Hn)).
    + pose proof (req_size_pos (c_n cx) ltac:(lia)). lia.
    + replace (c_p cx + (a - c_p cx)) with a by lia. exact HnE.
Qed.

Lemma fs_wvb : forall md mat, m_fds (with_vm_backing (m_vm_lazy md) mat md) = m_fds md /\
  m_fs (with_vm_backing (m_vm_lazy md) mat md) = m_fs md.
Proof. intros [fd [maps lazy mt] io fs proc lim tm] mat. split; reflexivity. Qed.

(* The input block, when there is one, is one of the caller's blocks and stays a block at every cut. *)
Lemma input_block : forall cx ly3 S3 L,
  pe_base SK B MT KS cx -> Permutation (ablocks B ly3 S3) (ablocks B (c_ly cx) (c_S cx) ++ L) ->
  0 < c_n cx -> In (c_p cx, c_n cx) (ablocks B ly3 S3).
Proof.
  intros cx ly3 S3 L HB HP Hn. pose proof HB as (_ & _ & _ & _ & Hinp & _).
  destruct Hinp as [[H0 _] | [_ Hin]]; [lia|].
  apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. left. exact Hin.
Qed.

(* The frame's shadow misses every byte of hfoot_ns. *)
Lemma shadow_off_hfoot_ns : forall cx fp ly3 S3 (W3 : world SEGS) mem3 md3 L,
  pe_base SK B MT KS cx -> AR SEGS B ly3 S3 W3 mem3 md3 ->
  Permutation (ablocks B ly3 S3) (ablocks B (c_ly cx) (c_S cx) ++ L) ->
  In (PE_CID, fp) (frames S3) -> frame_addr ly3 PE_CID fp = pF cx fp ->
  forall a, hfoot_ns cx fp a -> ~ (pSH cx fp <= a < pSH cx fp + 16).
Proof.
  intros cx fp ly3 S3 W3 mem3 md3 L HB HAR HP Hfin Efa x Hx Hex.
  pose proof (tail_geo cx HB) as (Hal & Hs1m & Hs1b & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  unfold LLVMF_STK in Hslo.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct (frames_bounds SEGS B LAWS ly3 S3 W3 mem3 md3 PE_CID fp HAR Hfin) as (Hf4096 & Hfceil & Hfapp).
  rewrite Efa in Hf4096, Hfceil, Hfapp. change (fs_frame_bytes PE_CID) with 128 in Hfceil, Hfapp.
  unfold pSH, shadow_of_addr, SHADOW_OFF in Hex. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hfapp.
  unfold hfoot_ns in Hx. destruct Hx as [Hx|[Hx|Hx]].
  - Z.div_mod_to_equations. lia.
  - Z.div_mod_to_equations. lia.
  - assert (Hcn : 0 < c_n cx) by lia.
    pose proof (input_block cx ly3 S3 _ HB HP Hcn) as Hpin.
    destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hpin) as (_ & _ & _ & Hpapp & _).
    pose proof (req_size_pos (c_n cx) ltac:(lia)).
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hpapp. Z.div_mod_to_equations. lia.
Qed.

Lemma present_rdW : forall (H : word -> bool) mem a, apresent H mem a -> YO0d.present (mrestrict H mem) a.
Proof. intros H mem a (Hh & b & Hb). exists b. unfold mrestrict. rewrite Hh. exact Hb. Qed.

(* The reader statement's view of the file (bytes from its Z list) is the harness's p_F. *)
Lemma nxF_pC : forall cx, nxF (p_C cx) = p_F cx.
Proof.
  intros cx. unfold nxF, bytesZ, p_C. rewrite map_map.
  rewrite (map_ext (fun x : byte => Z_to_bv 8 (bv_unsigned x)) (fun x => x)) by (intros x; apply Z_to_bv_bv_unsigned).
  apply map_id.
Qed.

Lemma p_swz01 : forall cx, p_swz cx = 0 \/ p_swz cx = 1.
Proof. intros cx. unfold p_swz, PST.pcap_sw. destruct (_ =? _); [right | left]; reflexivity. Qed.

Lemma p_good_len : forall cx, p_good cx = true -> 24 <= p_nF cx.
Proof.
  intros cx H. unfold p_good, PST.pcap_good in H. apply andb_true_iff in H as [H _]. apply Z.leb_le in H. exact H.
Qed.

Lemma notin_prefix : forall {A} (l L M : list A) x,
  List.NoDup l -> Permutation l (L ++ M) -> List.In x M -> ~ List.In x L.
Proof.
  intros A l L M x Hnd Hp HxM. apply (Permutation_NoDup Hp) in Hnd. clear Hp l.
  induction L as [|a L IH]; intros Hin; [destruct Hin|].
  cbn [app] in Hnd. apply List.NoDup_cons_iff in Hnd as [Hna Hnd].
  destruct Hin as [-> | Hin]; [apply Hna; apply in_or_app; right; exact HxM | exact (IH Hnd Hin)].
Qed.

(* A byte that is not in pe_G reads the same in the inner journal's start memory and in c_mem. *)
Lemma aview_memS : forall cx memS a, gagree pe_G (w_H (c_W cx)) (c_mem cx) memS -> 0 <= a < 2 ^ 64 ->
  ~ inG pe_G a -> aview SEGS (w_H (c_W cx)) memS a = aview SEGS (w_H (c_W cx)) (c_mem cx) a.
Proof.
  intros cx memS a Hag Ha HnG. apply (aview_gagree SEGS pe_G _ _ _ a Hag).
  apply inGb_false. rewrite unsigned_lit_small by lia. exact HnG.
Qed.

(* The source's meta invariant at a state of the walk: the asrc_meta_inv_kept argument (PSourceMeta.v), from
   pe_base's invariant at c_mem through the inner journal; pe_base keeps the meta cell out of pe_G, and every byte of
   pe_G is an image byte, below the meta region. *)
Lemma meta_now : forall cx memS own ly3 S3 W3 mem3 md3 k,
  pe_base SK B MT KS cx ->
  ajournal SEGS B LLVMF_STK (spZ (c_regs cx)) [sink_token] (c_ly cx) (c_S cx) (c_W cx) memS (c_md cx)
    own ly3 S3 W3 mem3 md3 k ->
  gagree pe_G (w_H (c_W cx)) (c_mem cx) memS ->
  asrc_meta_inv SEGS KS ly3 (rdW W3 mem3) (c_M cx).
Proof.
  intros cx memS own ly3 S3 W3 mem3 md3 k HB HJ Hag.
  pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (HX & Himg & Hp & Hm & H0 & H47 & Hal & HZ) & _ & _ & _ &
    _ & _ & HGX & HGD & _).
  pose proof HJ as (HAR' & Hly & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _ & _ & _ & _ & F5 & _).
  pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Eextra & _).
  split; [rewrite Eextra; exact HX|]. split; [exact Himg|].
  split; [exact (asrc_meta_ptr_of_AR SK SEGS B KS ASIL _ _ _ _ _ HAR')|]. split.
  - eapply val_mem_frame; [|exact Hm]. intros x Hx. cbn in Hx. apply (mbyte_kept_of_aview SEGS).
    destruct (asil_meta _ _ _ _ ASIL x ltac:(lia)) as (Hi & Hns & He & Hlt).
    pose proof (pa_img_range x Hi) as Hxr. unfold pcap_img_end, IMG_TOP in Hxr.
    rewrite <- (aview_memS cx memS x Hag ltac:(lia)).
    + apply (F3 x Hi Hns He). apply fp_spares_below. exact Hlt.
    + intros HxG. destruct (HGD x HxG) as (_ & Hnm & _). apply Hnm. lia.
  - split; [exact H0|]. split; [exact H47|]. split; [exact Hal|].
    intros a Ha. rewrite <- (HZ a Ha). apply (mbyte_kept_of_aview SEGS).
    rewrite <- (aview_memS cx memS a Hag ltac:(lia)).
    + apply F5.
      * apply Exists_exists. exists (c_M cx, AMETA_SIZE). split; [exact HX | unfold in_zr; cbn [fst snd]; lia].
      * intros He. pose proof (asil_errno_img _ _ _ _ ASIL a He) as Hi. pose proof (Himg a Hi). lia.
    + intros HaG. pose proof (proj1 (HGX a HaG)) as Hi. pose proof (Himg a Hi). lia.
Qed.

(* The read-only data at a state of the walk: pe_base's arodata_okP at c_mem, moved to the inner journal's start
   memory (pe_base keeps the read-only bytes out of pe_G) and along the journal (PcapBase.arodata_ok_journalP). *)
Lemma aro_now : forall cx memS own ly3 S3 W3 mem3 md3 k,
  pe_base SK B MT KS cx ->
  ajournal SEGS B LLVMF_STK (spZ (c_regs cx)) [sink_token] (c_ly cx) (c_S cx) (c_W cx) memS (c_md cx)
    own ly3 S3 W3 mem3 md3 k ->
  gagree pe_G (w_H (c_W cx)) (c_mem cx) memS ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W3) mem3).
Proof.
  intros cx memS own ly3 S3 W3 mem3 md3 k HB HJ Hag.
  pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hrod & _ & _ & _ & _ & _ & _ & _ & _ & HGX & HGD & _).
  eapply (arodata_ok_journalP SEGS pa_relro_lo pa_relro_hi pa_relro_img); [exact HJ|].
  intros a Hro Ho He.
  assert (Hi : in_img SEGS a)
    by (destruct Hro as [(sg & Hsg & _ & Hr) | Hr]; [exists sg; split; [exact Hsg | exact Hr] | exact (pa_relro_img a Hr)]).
  pose proof (pa_img_range a Hi) as Hxr. unfold pcap_img_end, IMG_TOP in Hxr.
  rewrite (aview_memS cx memS a Hag ltac:(lia)); [exact (Hrod a Hro Ho He)|].
  intros HaG. exact (proj1 (HGD a HaG) Hro).
Qed.

(* A heap block the call allocated since its start (not one of its caller's) misses every body byte. *)
Lemma block_off_hfoot : forall cx fp ly3 S3 W3 mem3 md3 L p n,
  pe_base SK B MT KS cx -> AR SEGS B ly3 S3 W3 mem3 md3 ->
  Permutation (ablocks B ly3 S3) (ablocks B (c_ly cx) (c_S cx) ++ L) ->
  In (p, n) (ablocks B ly3 S3) -> ~ In (p, n) (ablocks B (c_ly cx) (c_S cx)) ->
  In (PE_CID, fp) (frames S3) -> frame_addr ly3 PE_CID fp = pF cx fp ->
  forall a, hfoot cx fp a -> ~ (p <= a < p + req_size n).
Proof.
  intros cx fp ly3 S3 W3 mem3 md3 L p n HB HAR HP Hin Hout Hfin Efa x Hx Hex.
  pose proof (tail_geo cx HB) as (Hal & Hs1m & Hs1b & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  unfold LLVMF_STK in Hslo.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct (frames_bounds SEGS B LAWS ly3 S3 W3 mem3 md3 PE_CID fp HAR Hfin) as (Hf4096 & Hfceil & Hfapp).
  rewrite Efa in Hf4096, Hfceil, Hfapp. change (fs_frame_bytes PE_CID) with 128 in Hfceil, Hfapp.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR Hin) as (_ & Hb4096 & Hbceil & Hbapp & _ & _ & Hbn).
  pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ p n PE_CID fp HAR Hin Hfin) as Dbf.
  unfold zdisjoint in Dbf. cbn [fst snd] in Dbf. rewrite Efa in Dbf. change (fs_frame_bytes PE_CID) with 128 in Dbf.
  pose proof (req_size_pos n ltac:(lia)) as [Hrq1 Hrq2].
  unfold hfoot, pSH, shadow_of_addr, SHADOW_OFF in Hx. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hbapp.
  destruct Hx as [Hx|[Hx|[Hx|[Hx|Hx]]]]; try lia.
  - Z.div_mod_to_equations. lia.
  - assert (Hcn : 0 < c_n cx) by lia.
    pose proof (input_block cx ly3 S3 _ HB HP Hcn) as Hpin.
    assert (Hne : (c_p cx, c_n cx) <> (p, n)).
    { intros Heq. apply Hout. rewrite <- Heq. pose proof HB as (_ & _ & _ & _ & [[H0 _] | [_ Hin0]] & _); [lia | exact Hin0]. }
    pose proof (sep_blocks SEGS B LAWS _ _ _ _ _ _ _ _ _ HAR Hpin Hin Hne) as D. unfold zdisjoint in D. cbn [fst snd] in D.
    pose proof (req_size_pos (c_n cx) ltac:(lia)). lia.
Qed.

(* Bytes of the call's own frame past its 24-byte header (ps, ts) miss every body byte. *)
Lemma frame_off_hfoot : forall cx fp ly3 S3 W3 mem3 md3 L q m,
  pe_base SK B MT KS cx -> AR SEGS B ly3 S3 W3 mem3 md3 ->
  Permutation (ablocks B ly3 S3) (ablocks B (c_ly cx) (c_S cx) ++ L) ->
  In (PE_CID, fp) (frames S3) -> frame_addr ly3 PE_CID fp = pF cx fp ->
  pF cx fp + 24 <= q -> q + m <= pF cx fp + 120 ->
  forall a, hfoot cx fp a -> ~ (q <= a < q + m).
Proof.
  intros cx fp ly3 S3 W3 mem3 md3 L q m HB HAR HP Hfin Efa Hq1 Hq2 x Hx Hex.
  pose proof (tail_geo cx HB) as (Hal & Hs1m & Hs1b & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  unfold LLVMF_STK in Hslo.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct (frames_bounds SEGS B LAWS ly3 S3 W3 mem3 md3 PE_CID fp HAR Hfin) as (Hf4096 & Hfceil & Hfapp).
  rewrite Efa in Hf4096, Hfceil, Hfapp. change (fs_frame_bytes PE_CID) with 128 in Hfceil, Hfapp.
  unfold hfoot, pSH, shadow_of_addr, SHADOW_OFF in Hx. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hfapp.
  destruct Hx as [Hx|[Hx|[Hx|[Hx|Hx]]]]; try lia.
  - Z.div_mod_to_equations. lia.
  - assert (Hcn : 0 < c_n cx) by lia.
    pose proof (input_block cx ly3 S3 _ HB HP Hcn) as Hpin.
    pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ _ _ PE_CID fp HAR Hpin Hfin) as D.
    unfold zdisjoint in D. cbn [fst snd] in D. rewrite Efa in D. change (fs_frame_bytes PE_CID) with 128 in D.
    pose proof (req_size_pos (c_n cx) ltac:(lia)). lia.
Qed.

(* ---- the symbolic state at a cut, without memory regions ---------------------------------------------------- *)

Lemma entry0 : forall pc (ms : machine_state) (W : world SEGS),
  ms_pc_val ms = w64 (BASE + pc) -> ms_resv ms = None -> ms_svc_pending ms = None -> ms_rom ms = seg_rom SEGS ->
  ms_fregs ms = fp_regs -> ms_fcsr ms = fp_csr ->
  st_ok_pi SEGS VAL (Eimg (Ereg (ms_regs ms) [])) (mkSS pc sr_atoms [] None (mkFacts [] [] [])) (restrict (w_H W) ms).
Proof.
  intros pc ms W Hpc Hresv Hsvc Hrom Hfrg Hfcsr.
  pose proof (ms_eta ms Hfrg Hsvc Hresv Hfcsr) as Hms. rewrite Hpc, Hrom in Hms.
  assert (Hms' : restrict (w_H W) ms =
    mkst (ms_regs ms) (Z_to_bv 64 (BASE + pc)) (mrestrict (w_H W) (ms_mem ms)) (seg_rom SEGS))
    by (rewrite Hms at 1; reflexivity).
  rewrite Hms'.
  apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - constructor.
  - cbn. exact I.
  - split; [exact I | split; exact I].
Qed.

(* The symbolic state at a cut over memory regions, its extra atoms 32.. given by ext. *)
Lemma entryR : forall pc (ms : machine_state) (W : world SEGS) ext rs G,
  ms_pc_val ms = w64 (BASE + pc) -> ms_resv ms = None -> ms_svc_pending ms = None -> ms_rom ms = seg_rom SEGS ->
  ms_fregs ms = fp_regs -> ms_fcsr ms = fp_csr ->
  regions_wf rs = true ->
  Forall (region_ok SEGS (Eimg (Ereg (ms_regs ms) ext)) (mrestrict (w_H W) (ms_mem ms))) rs ->
  pairwise_disjoint (Eimg (Ereg (ms_regs ms) ext)) rs ->
  facts_ok (Eimg (Ereg (ms_regs ms) ext)) G ->
  st_ok_pi SEGS VAL (Eimg (Ereg (ms_regs ms) ext)) (mkSS pc sr_atoms rs None G) (restrict (w_H W) ms).
Proof.
  intros pc ms W ext rs G Hpc Hresv Hsvc Hrom Hfrg Hfcsr Hwf Hrs Hd Hf.
  pose proof (ms_eta ms Hfrg Hsvc Hresv Hfcsr) as Hms. rewrite Hpc, Hrom in Hms.
  assert (Hms' : restrict (w_H W) ms =
    mkst (ms_regs ms) (Z_to_bv 64 (BASE + pc)) (mrestrict (w_H W) (ms_mem ms)) (seg_rom SEGS))
    by (rewrite Hms at 1; reflexivity).
  rewrite Hms'. apply pa_entry_st_ok_full; [apply regs_ok_Eimg_Ereg | exact Hwf | exact Hrs | exact Hd | exact Hf].
Qed.

(* A byte of the harness's own frame or of its shadow is one the journal lets it write. *)
Lemma awr_ownframe : forall STK sp0 FP bl0 blc ly3 cx fp a,
  frame_addr ly3 PE_CID fp = pF cx fp ->
  (pF cx fp <= a < pF cx fp + 128) \/ (pSH cx fp <= a < pSH cx fp + 16) ->
  awr_byte STK sp0 FP bl0 blc ly3 [(PE_CID, fp)] a.
Proof.
  intros STK sp0 FP bl0 blc ly3 cx fp a Efa Ha. right; right; right. exists PE_CID, fp. split; [left; reflexivity|].
  unfold in_zr. cbn [fst snd]. rewrite Efa. change (fs_frame_bytes PE_CID / 8) with 16.
  change (fs_frame_bytes PE_CID) with 128.
  unfold pSH, shadow_of_addr in Ha. unfold shadow_addr. destruct Ha as [Ha|Ha]; [left | right]; lia.
Qed.

(* A byte the plain engine wrote as the literal c reads back as c's low byte. *)
Lemma aview_lit_byte : forall (H : word -> bool) mem a (E : env) c v,
  val_mem SEGS (mrestrict H mem) a (N.to_nat 1) (bv_unsigned (sv_denot E (SLit c)) mod 2 ^ (8 * Z.of_N 1)) ->
  v = bv_unsigned (Z_to_bv 8 (le_byte (bv_unsigned (Z_to_bv 64 c) mod 2 ^ (8 * Z.of_N 1)) (N.to_nat 1) 0)) ->
  aview SEGS H mem a = Some v.
Proof.
  intros H mem a E c v Hv ->. unfold aview. specialize (Hv 0%nat ltac:(cbv; lia)).
  cbn [Z.of_nat] in Hv. rewrite Z.add_0_r in Hv. rewrite Hv. reflexivity.
Qed.

Lemma psh_tsout_eq : forall i, i <> 12%nat -> nth i PSH_tsout 0 = nth i PSH_ts 0.
Proof. intros i Hi. do 13 (destruct i as [|i]; [reflexivity || (exfalso; lia) |]). reflexivity. Qed.

Lemma psh_out_eq : forall sh i, (sh = PSH_tsout \/ sh = PSH_ps) -> ~ (4 <= i <= 6)%nat ->
  nth i PSH_entry 0 = nth i sh 0.
Proof.
  intros sh i Hsh Hi. destruct Hsh as [->| ->];
  (do 7 (destruct i as [|i]; [reflexivity || (exfalso; lia) |]); reflexivity).
Qed.

Lemma o_mod16 : forall cx, pe_base SK B MT KS cx -> (c_sp1 cx - spZ (c_regs cx)) mod 16 = 0.
Proof.
  intros cx HB. pose proof (tail_geo cx HB) as (Hal & Hs1 & _).
  pose proof (Z.div_mod (spZ (c_regs cx)) 16 ltac:(lia)) as D1. pose proof (Z.div_mod (c_sp1 cx) 32 ltac:(lia)) as D2.
  rewrite Hal, Z.add_0_r in D1. rewrite Hs1, Z.add_0_r in D2.
  apply Z.mod_divide; [lia|]. exists (2 * (c_sp1 cx / 32) - spZ (c_regs cx) / 16). lia.
Qed.

(* ---- R6: PP_K11 0x81110 -> free 0x81114 -> PP_K12 0x81118 ------------------------------------------------- *)

Lemma tail_R6 : pe_from SK B MT KS POST (GI_K12 B MT KS) -> pe_from SK B MT KS POST (GI_K11 B MT KS).
Proof.
intros NEXT cx fp k acc ly3 S3 W3 ms3 md3 HB HJ Hfrs Hmo HG.
destruct HG as (bb & (Hbody & Hk & Hacc & Hperm & Hfds & Hfs) & Hn26 & R19 & R20 & R23 & Hslots & Hsrc).
destruct Hbody as (Hpc & Hresv & Hsvc & Hrom & Hfrg & Hfcsr & Hregs & Hsaved & Hhdr & Hsh & Hlen & Hin).
pose proof (tail_geo cx HB) as (Hal & Hs1m & Hs1b & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
unfold LLVMF_STK in Hslo, Hbot.
pose proof HB as ((HAR0 & Hrok & Hra4 & Hgp0 & Htp0 & _) & HraL & _ & _ & _ & _ & _ & Hev & _ & _ & _ & _ & _ & _ &
  _ & _ & Hmok & Hneed & HGX & HGD & _ & _ & Hftr).
destruct (gx_open _ _ _ _ _ _ _ _ HJ) as (memS & HJi & Hag). clear HJ. rename HJi into HJ.
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & Hnev & Hk0 & _).
destruct Hregs as (Rsp & Rs0 & Rs1 & Rs11 & Rgp & Rtp).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as (HB0 & HB1 & HB2). pose proof (pa_base_lo (PL := PL_pcap) (PI := PI)) as HBLO.
assert (Hbin : In (bb, p_nF cx) (ablocks B ly3 S3))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; right; left; reflexivity).
assert (Hbout : ~ In (bb, p_nF cx) (ablocks B (c_ly cx) (c_S cx)))
  by exact (notin_of_perm_nodup _ _ _ (ablocks_nodup _ _ _ _ _ HAR) Hperm).
destruct (lay_eqs _ _ _ Hly) as (EF & Etop & Eslo & Eshi).
assert (Efa : frame_addr ly3 PE_CID fp = pF cx fp) by (unfold pF, frame_addr; rewrite EF; reflexivity).
assert (Hfin : In (PE_CID, fp) (frames S3)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 PE_CID fp HAR Hfin) as (Hf4096 & Hfceil & Hfapp).
rewrite Efa in Hf4096, Hfceil, Hfapp. change (fs_frame_bytes PE_CID) with 128 in Hfceil, Hfapp.
destruct (al_blocks _ _ LAWS _ _ _ _ _ bb (p_nF cx) HAR Hbin) as (_ & Hb4096 & Hbceil & Hbapp & _ & _ & Hbn).
pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ bb (p_nF cx) PE_CID fp HAR Hbin Hfin) as Dbf.
unfold zdisjoint in Dbf. cbn [fst snd] in Dbf. rewrite Efa in Dbf. change (fs_frame_bytes PE_CID) with 128 in Dbf.
pose proof (req_size_pos (p_nF cx) ltac:(lia)) as [Hrq1 Hrq2].
(* the symbolic state at 0x81110 *)
pose proof (entry0 PP_K11 ms3 W3 Hpc Hresv Hsvc Hrom Hfrg Hfcsr) as HS.
remember (Eimg (Ereg (ms_regs ms3) [])) as E eqn:HEdef.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg (ms_regs ms3) []) n)
  by (intros n Hn; subst E; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr (ms_regs ms3) 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr (ms_regs ms3) 3) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr (ms_regs ms3) 4) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 4 4%bv eq_refl)).
assert (E8 : ew E 8 = getr (ms_regs ms3) 8) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 8 8%bv eq_refl)).
assert (E9 : ew E 9 = getr (ms_regs ms3) 9) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 9 9%bv eq_refl)).
assert (E19 : ew E 19 = getr (ms_regs ms3) 19) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 19 19%bv eq_refl)).
assert (E20 : ew E 20 = getr (ms_regs ms3) 20) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 20 20%bv eq_refl)).
assert (E23 : ew E 23 = getr (ms_regs ms3) 23) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 23 23%bv eq_refl)).
assert (E27 : ew E 27 = getr (ms_regs ms3) 27) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 27 27%bv eq_refl)).
assert (SHOK : sh_ok SEGS TBx [] E (mrestrict (w_H W3) (ms_mem ms3))) by constructor.
clear HEdef EL.
(* 0x81110 mv a0,s3; 0x81114 jal free *)
paj_run_tok RUN HS HJ SHOK TBspan; [apply awr_ok_nil |].
assert (HFm : ms_mem ms = ms_mem ms3) by exact (frame_of_nil _ _ _ HF).
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (10%bv : bv 5) Q10. prreg HS (20%bv : bv 5) Q20.
prreg HS (23%bv : bv 5) Q23. prreg HS (27%bv : bv 5) Q27.
rewrite (pal_free B TL).
assert (Hs8 : rdword (aview SEGS (w_H W3) (ms_mem ms3)) (spZ (c_regs cx) - 8) = Some (raZ (c_regs cx)))
  by exact (proj1 Hsaved).
assert (Hs16 : rdword (aview SEGS (w_H W3) (ms_mem ms3)) (spZ (c_regs cx) - 16) = Some (s0Z (c_regs cx))).
{ pose proof (proj2 Hsaved 0 ltac:(lia)) as H0. replace (spZ (c_regs cx) - 16 - 8 * 0) with (spZ (c_regs cx) - 16) in H0 by lia.
  exact H0. }
eapply SRr_bind.
{ eapply (afree04_sub_fs SK SEGS B LAWS pa_segs_low MT AFREE W3 (ms_regs ms) (ms_mem ms) LLVMF_STK (spZ (c_regs cx))
    [sink_token] (c_ly cx) (c_S cx) (c_W cx) memS (c_md cx) [(PE_CID, fp)] ly3 S3 _ k bb (p_nF cx)
    (c_sp1 cx - spZ (c_regs cx)) (Z_to_bv 64 (BASE + PP_K12)) (pch cx) HJ Hbin).
  - rewrite Q10, E19, R19. reflexivity.
  - unfold spZ at 1. rewrite Q2, E2, Rsp. unfold w64. rewrite unsigned_lit_small by lia. lia.
  - exact (o_mod16 cx HB).
  - lia.
  - unfold ASTACK, LLVMF_STK. lia.
  - rewrite Q3, E3, Rgp. exact Hgp0.
  - rewrite Q4, E4, Rtp. exact Htp0.
  - rewrite Q1. reflexivity.
  - apply ret_ok_codeptr_v; [unfold PP_K12; lia | reflexivity].
  - unfold EV_LIB in Hev. lia.
  - apply (achain_chain_pre ly3 _ (c_sp1 cx) (spZ (c_regs cx)) (pch cx) (ms_regs ms)).
    + rewrite <- HFm in Hs8, Hs16. exact (pch_achain cx _ memS ly3 S3 W3 (ms_mem ms) _ k HB HJ Hag Hs8 Hs16).
    + unfold spZ at 1 2. rewrite Q2, E2, Rsp. unfold w64. rewrite unsigned_lit_small by lia. lia.
    + unfold s0Z at 1. rewrite Q8, E8, Rs0. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
    + unfold raZ. rewrite Q1, unsigned_lit_small by lia. lia.
  - apply Hftr. unfold raZ. rewrite Q1, unsigned_lit_small by lia. unfold PE_FREE_SITES.
    replace (BASE + 2528 - BASE) with 2528 by lia. cbn. right; right; left; reflexivity.
  - intros Hc. exfalso. exact (Hbout Hc).
  - apply (mok_station MT (c_S cx) S3 (c_T cx) acc (mo_free MT) MLAWS Hmok Hmo (mo_free_nonneg MT MLAWS)).
    pose proof (PA_K12_need MT MLAWS cx) as Hn. unfold PA_K12 in Hn. lia. }
cbv beta. intros W2 c2 Hwle (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & (l1 & l2 & El1 & El2) & Hfr2 & HK & Hmle & Hfd2 & Hfs2).
destruct HK as (K1 & K2 & K3 & K4 & K5 & K6).
assert (Hfoot : forall a, hfoot cx fp a -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W3) (ms_mem ms3) a).
{ intros a Ha. rewrite <- HFm.
  refine (foot_kept cx fp ly3 S3 W3 (ms_mem ms) W2 mem2 _ _ (fun a => bb <= a < bb + req_size (p_nF cx)) HB
    (fun a Ha Hn _ => K1 a Ha Hn) K2 K4 _ Hfin Efa (input_block cx ly3 S3 _ HB Hperm) _ a Ha); [lia|].
  intros x Hx Hex. unfold hfoot, pSH, shadow_of_addr, SHADOW_OFF in Hx. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hbapp.
  destruct Hx as [Hx|[Hx|[Hx|[Hx|Hx]]]]; try lia.
  - Z.div_mod_to_equations. lia.
  - assert (Hcn : 0 < c_n cx) by lia.
    pose proof (input_block cx ly3 S3 _ HB Hperm Hcn) as Hpin.
    assert (Hne : (c_p cx, c_n cx) <> (bb, p_nF cx)).
    { intros Heq. apply Hbout. rewrite <- Heq. pose proof HB as (_ & _ & _ & _ & [[H0 _] | [_ Hin0]] & _); [lia | exact Hin0]. }
    pose proof (sep_blocks SEGS B LAWS _ _ _ _ _ _ _ _ _ HAR Hpin Hbin Hne) as D. unfold zdisjoint in D. cbn [fst snd] in D.
    pose proof (req_size_pos (c_n cx) ltac:(lia)). lia. }
destruct (tail_kept cx fp W3 ms3 W2 (mkst regs2 (Z_to_bv 64 (BASE + PP_K12)) mem2 (seg_rom SEGS)) PSH_ts Hfoot
  Hsaved Hhdr Hsh Hlen Hin Hslots) as (T1 & T2 & T3 & T4 & T5).
assert (P : forall r : Z, acallee_saved r -> getr regs2 (Z_to_bv 5 r) = getr (ms_regs ms) (Z_to_bv 5 r)) by exact HP2.
eapply (NEXT cx fp (k + 1) (acc + mo_free MT) ly2 S2 W2 (mkst regs2 (Z_to_bv 64 (BASE + PP_K12)) mem2 (seg_rom SEGS)) md2 HB).
- exact (gx_pack0 cx _ memS _ _ _ _ _ _ HJ2 Hag).
- rewrite Hfr2. exact Hfrs.
- exact (mle_station MT _ _ _ _ _ MLAWS Hmo Hmle).
- unfold GI_K12, p_cut. split; [|split; [exact Hn26 | split; [|split; [|split]]]].
  + split; [|split; [lia | split; [unfold PA_K12; lia | split; [|split]]]].
    * unfold pe_body. cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr mkst ms_regs].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|]. split; [reflexivity|].
      split; [|split; [exact T1 | split; [exact T2 | split; [exact T3 | split; [exact Hlen | exact T4]]]]].
      unfold pregs. cbn [ms_regs mkst].
      split; [transitivity (getr (ms_regs ms) 2); [exact (P 2 ltac:(unfold acallee_saved; lia)) | rewrite Q2, E2; exact Rsp]|].
      split; [transitivity (getr (ms_regs ms) 8); [exact (P 8 ltac:(unfold acallee_saved; lia)) | rewrite Q8, E8; exact Rs0]|].
      split; [transitivity (getr (ms_regs ms) 9); [exact (P 9 ltac:(unfold acallee_saved; lia)) | rewrite Q9, E9; exact Rs1]|].
      split; [transitivity (getr (ms_regs ms) 27); [exact (P 27 ltac:(unfold acallee_saved; lia)) | rewrite Q27, E27; exact Rs11]|].
      split; [transitivity (getr (ms_regs ms) 3); [exact (P 3 ltac:(unfold acallee_saved; lia)) | rewrite Q3, E3; exact Rgp]|].
      transitivity (getr (ms_regs ms) 4); [exact (P 4 ltac:(unfold acallee_saved; lia)) | rewrite Q4, E4; exact Rtp].
    * rewrite El2. rewrite El1 in Hperm. exact (Permutation_app_inv _ _ _ [] _ Hperm).
    * rewrite Hfd2. rewrite (proj1 (fs_wvb md3 mat)). exact Hfds.
    * rewrite Hfs2. rewrite (proj2 (fs_wvb md3 mat)). exact Hfs.
  + cbn [ms_regs mkst]. transitivity (getr (ms_regs ms) 20); [exact (P 20 ltac:(unfold acallee_saved; lia)) | rewrite Q20, E20; exact R20].
  + cbn [ms_regs mkst]. transitivity (getr (ms_regs ms) 23); [exact (P 23 ltac:(unfold acallee_saved; lia)) | rewrite Q23, E23; exact R23].
  + exact T5.
  + cbn [ms_mem mkst]. apply (asource_none_frame KS (rdW W3 (ms_mem ms3))); [|exact Hsrc].
    intros a Ha. apply (mbyte_of_aview SEGS). rewrite <- HFm.
    destruct (asil_env _ _ _ _ ASIL a Ha) as (Hi & Ho & He). exact (K3 a Hi Ho He).
Qed.

(* ---- R5: PP_K10 0x81100 -> the check of the closed reader's -1 -> free 0x8110c (the record buffer) -> PP_K11 -- *)

Lemma tail_R5 : pe_from SK B MT KS POST (GI_K11 B MT KS) -> pe_from SK B MT KS POST (GI_K10 B MT KS).
Proof.
intros NEXT cx fp k acc ly3 S3 W3 ms3 md3 HB HJ Hfrs Hmo HG.
destruct HG as (bb & bf & (Hbody & Hk & Hacc & Hperm & Hfds & Hfs) & Hn26 & R10 & R19 & R20 & R22 & R23 & Hslots & Hnull & Hsrc).
destruct Hbody as (Hpc & Hresv & Hsvc & Hrom & Hfrg & Hfcsr & Hregs & Hsaved & Hhdr & Hsh & Hlen & Hin).
pose proof (tail_geo cx HB) as (Hal & Hs1m & Hs1b & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
unfold LLVMF_STK in Hslo, Hbot.
pose proof HB as ((HAR0 & Hrok & Hra4 & Hgp0 & Htp0 & _) & HraL & _ & _ & _ & _ & _ & Hev & _ & _ & _ & _ & _ & _ &
  _ & _ & Hmok & Hneed & HGX & HGD & _ & _ & Hftr).
destruct (gx_open _ _ _ _ _ _ _ _ HJ) as (memS & HJi & Hag). clear HJ. rename HJi into HJ.
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & Hnev & Hk0 & _).
destruct Hregs as (Rsp & Rs0 & Rs1 & Rs11 & Rgp & Rtp).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as (HB0 & HB1 & HB2). pose proof (pa_base_lo (PL := PL_pcap) (PI := PI)) as HBLO.
pose proof (p_sizes cx) as (Hsz1 & Hsz2 & Hsz3).
assert (Hbin : In (bf, p_bn cx) (ablocks B ly3 S3))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; right; right; left; reflexivity).
assert (Hperm' : Permutation (ablocks B ly3 S3) ((ablocks B (c_ly cx) (c_S cx) ++ [(bb, p_nF cx)]) ++ [(bf, p_bn cx)]))
  by (rewrite <- app_assoc; exact Hperm).
assert (Hbout : ~ In (bf, p_bn cx) (ablocks B (c_ly cx) (c_S cx) ++ [(bb, p_nF cx)]))
  by exact (notin_of_perm_nodup _ _ _ (ablocks_nodup _ _ _ _ _ HAR) Hperm').
destruct (lay_eqs _ _ _ Hly) as (EF & Etop & Eslo & Eshi).
assert (Efa : frame_addr ly3 PE_CID fp = pF cx fp) by (unfold pF, frame_addr; rewrite EF; reflexivity).
assert (Hfin : In (PE_CID, fp) (frames S3)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 PE_CID fp HAR Hfin) as (Hf4096 & Hfceil & Hfapp).
rewrite Efa in Hf4096, Hfceil, Hfapp. change (fs_frame_bytes PE_CID) with 128 in Hfceil, Hfapp.
destruct (al_blocks _ _ LAWS _ _ _ _ _ bf (p_bn cx) HAR Hbin) as (_ & Hb4096 & Hbceil & Hbapp & _ & _ & Hbn).
pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ bf (p_bn cx) PE_CID fp HAR Hbin Hfin) as Dbf.
unfold zdisjoint in Dbf. cbn [fst snd] in Dbf. rewrite Efa in Dbf. change (fs_frame_bytes PE_CID) with 128 in Dbf.
pose proof (req_size_pos (p_bn cx) ltac:(lia)) as [Hrq1 Hrq2].
(* the symbolic state at 0x81100 *)
pose proof (entry0 PP_K10 ms3 W3 Hpc Hresv Hsvc Hrom Hfrg Hfcsr) as HS.
remember (Eimg (Ereg (ms_regs ms3) [])) as E eqn:HEdef.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg (ms_regs ms3) []) n)
  by (intros n Hn; subst E; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr (ms_regs ms3) 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr (ms_regs ms3) 3) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr (ms_regs ms3) 4) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 4 4%bv eq_refl)).
assert (E8 : ew E 8 = getr (ms_regs ms3) 8) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 8 8%bv eq_refl)).
assert (E9 : ew E 9 = getr (ms_regs ms3) 9) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 9 9%bv eq_refl)).
assert (E10 : ew E 10 = getr (ms_regs ms3) 10) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 10 10%bv eq_refl)).
assert (E19 : ew E 19 = getr (ms_regs ms3) 19) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 19 19%bv eq_refl)).
assert (E20 : ew E 20 = getr (ms_regs ms3) 20) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 20 20%bv eq_refl)).
assert (E22 : ew E 22 = getr (ms_regs ms3) 22) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 22 22%bv eq_refl)).
assert (E23 : ew E 23 = getr (ms_regs ms3) 23) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 23 23%bv eq_refl)).
assert (E27 : ew E 27 = getr (ms_regs ms3) 27) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 27 27%bv eq_refl)).
assert (SHOK : sh_ok SEGS TBx [] E (mrestrict (w_H W3) (ms_mem ms3))) by constructor.
clear HEdef EL.
(* 0x81100 addi a1,zero,-1; 0x81104 bne a0,a1 to the abort at 0x81340 *)
paj_run_tok RUN HS HJ SHOK TBspan; [apply awr_ok_nil |].
assert (HFm1 : ms_mem ms = ms_mem ms3) by exact (frame_of_nil _ _ _ HF).
clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK TBspan.
{ (* taken: the closed reader answered -1, so a0 = a1 *)
  exfalso. rewrite branch_ne_U in Hc.
  assert (U10 : U E (SOff 10 0) = 2 ^ 64 - 1).
  { apply U_atom; [|lia]. rewrite E10, R10. apply bv_eq. reflexivity. }
  rewrite U10, U_lit in Hc by lia. cbn in Hc. discriminate Hc. }
clear Hc.
(* 0x81108 mv a0,s6; 0x8110c jal free *)
paj_run_tok RUN HS HJ SHOK TBspan; [apply awr_ok_nil |].
assert (HFm : ms_mem ms0 = ms_mem ms3) by (rewrite (frame_of_nil _ _ _ HF); exact HFm1).
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (10%bv : bv 5) Q10. prreg HS (19%bv : bv 5) Q19.
prreg HS (20%bv : bv 5) Q20. prreg HS (23%bv : bv 5) Q23. prreg HS (27%bv : bv 5) Q27.
rewrite (pal_free B TL).
assert (Hs8 : rdword (aview SEGS (w_H W3) (ms_mem ms3)) (spZ (c_regs cx) - 8) = Some (raZ (c_regs cx)))
  by exact (proj1 Hsaved).
assert (Hs16 : rdword (aview SEGS (w_H W3) (ms_mem ms3)) (spZ (c_regs cx) - 16) = Some (s0Z (c_regs cx))).
{ pose proof (proj2 Hsaved 0 ltac:(lia)) as H0. replace (spZ (c_regs cx) - 16 - 8 * 0) with (spZ (c_regs cx) - 16) in H0 by lia.
  exact H0. }
eapply SRr_bind.
{ eapply (afree04_sub_fs SK SEGS B LAWS pa_segs_low MT AFREE W3 (ms_regs ms0) (ms_mem ms0) LLVMF_STK (spZ (c_regs cx))
    [sink_token] (c_ly cx) (c_S cx) (c_W cx) memS (c_md cx) [(PE_CID, fp)] ly3 S3 _ k bf (p_bn cx)
    (c_sp1 cx - spZ (c_regs cx)) (Z_to_bv 64 (BASE + PP_K11)) (pch cx) HJ Hbin).
  - rewrite Q10, E22, R22. reflexivity.
  - unfold spZ at 1. rewrite Q2, E2, Rsp. unfold w64. rewrite unsigned_lit_small by lia. lia.
  - exact (o_mod16 cx HB).
  - lia.
  - unfold ASTACK, LLVMF_STK. lia.
  - rewrite Q3, E3, Rgp. exact Hgp0.
  - rewrite Q4, E4, Rtp. exact Htp0.
  - rewrite Q1. reflexivity.
  - apply ret_ok_codeptr_v; [unfold PP_K11; lia | reflexivity].
  - unfold EV_LIB in Hev. lia.
  - apply (achain_chain_pre ly3 _ (c_sp1 cx) (spZ (c_regs cx)) (pch cx) (ms_regs ms0)).
    + rewrite <- HFm in Hs8, Hs16. exact (pch_achain cx _ memS ly3 S3 W3 (ms_mem ms0) _ k HB HJ Hag Hs8 Hs16).
    + unfold spZ at 1 2. rewrite Q2, E2, Rsp. unfold w64. rewrite unsigned_lit_small by lia. lia.
    + unfold s0Z at 1. rewrite Q8, E8, Rs0. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
    + unfold raZ. rewrite Q1, unsigned_lit_small by lia. lia.
  - apply Hftr. unfold raZ. rewrite Q1, unsigned_lit_small by lia. unfold PE_FREE_SITES.
    replace (BASE + 2520 - BASE) with 2520 by lia. cbn. right; left; reflexivity.
  - intros Hc. exfalso. apply Hbout. apply in_or_app. left. exact Hc.
  - apply (mok_station MT (c_S cx) S3 (c_T cx) acc (mo_free MT) MLAWS Hmok Hmo (mo_free_nonneg MT MLAWS)).
    pose proof (PA_K12_need MT MLAWS cx) as Hn. pose proof (mo_free_nonneg MT MLAWS).
    unfold PA_K12, PA_K11 in Hn. lia. }
cbv beta. intros W2 c2 Hwle (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & (l1 & l2 & El1 & El2) & Hfr2 & HK & Hmle & Hfd2 & Hfs2).
destruct HK as (K1 & K2 & K3 & K4 & K5 & K6).
assert (Hfoot : forall a, hfoot cx fp a -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W3) (ms_mem ms3) a).
{ intros a Ha. rewrite <- HFm.
  refine (foot_kept cx fp ly3 S3 W3 (ms_mem ms0) W2 mem2 _ _ (fun a => bf <= a < bf + req_size (p_bn cx)) HB
    (fun a Ha Hn _ => K1 a Ha Hn) K2 K4 _ Hfin Efa (input_block cx ly3 S3 _ HB Hperm) _ a Ha); [lia|].
  intros x Hx Hex. unfold hfoot, pSH, shadow_of_addr, SHADOW_OFF in Hx. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hbapp.
  destruct Hx as [Hx|[Hx|[Hx|[Hx|Hx]]]]; try lia.
  - Z.div_mod_to_equations. lia.
  - assert (Hcn : 0 < c_n cx) by lia.
    pose proof (input_block cx ly3 S3 _ HB Hperm Hcn) as Hpin.
    assert (Hne : (c_p cx, c_n cx) <> (bf, p_bn cx)).
    { intros Heq. apply Hbout. rewrite <- Heq. apply in_or_app. left.
      pose proof HB as (_ & _ & _ & _ & [[H0 _] | [_ Hin0]] & _); [lia | exact Hin0]. }
    pose proof (sep_blocks SEGS B LAWS _ _ _ _ _ _ _ _ _ HAR Hpin Hbin Hne) as D. unfold zdisjoint in D. cbn [fst snd] in D.
    pose proof (req_size_pos (c_n cx) ltac:(lia)). lia. }
destruct (tail_kept cx fp W3 ms3 W2 (mkst regs2 (Z_to_bv 64 (BASE + PP_K11)) mem2 (seg_rom SEGS)) PSH_ts Hfoot
  Hsaved Hhdr Hsh Hlen Hin Hslots) as (T1 & T2 & T3 & T4 & T5).
assert (P : forall r : Z, acallee_saved r -> getr regs2 (Z_to_bv 5 r) = getr (ms_regs ms0) (Z_to_bv 5 r)) by exact HP2.
eapply (NEXT cx fp (k + 1) (acc + mo_free MT) ly2 S2 W2 (mkst regs2 (Z_to_bv 64 (BASE + PP_K11)) mem2 (seg_rom SEGS)) md2 HB).
- exact (gx_pack0 cx _ memS _ _ _ _ _ _ HJ2 Hag).
- rewrite Hfr2. exact Hfrs.
- exact (mle_station MT _ _ _ _ _ MLAWS Hmo Hmle).
- unfold GI_K11, p_cut. exists bb. split; [|split; [exact Hn26 | split; [|split; [|split; [|split]]]]].
  + split; [|split; [lia | split; [unfold PA_K11; lia | split; [|split]]]].
    * unfold pe_body. cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr mkst ms_regs].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|]. split; [reflexivity|].
      split; [|split; [exact T1 | split; [exact T2 | split; [exact T3 | split; [exact Hlen | exact T4]]]]].
      unfold pregs. cbn [ms_regs mkst].
      split; [transitivity (getr (ms_regs ms0) 2); [exact (P 2 ltac:(unfold acallee_saved; lia)) | rewrite Q2, E2; exact Rsp]|].
      split; [transitivity (getr (ms_regs ms0) 8); [exact (P 8 ltac:(unfold acallee_saved; lia)) | rewrite Q8, E8; exact Rs0]|].
      split; [transitivity (getr (ms_regs ms0) 9); [exact (P 9 ltac:(unfold acallee_saved; lia)) | rewrite Q9, E9; exact Rs1]|].
      split; [transitivity (getr (ms_regs ms0) 27); [exact (P 27 ltac:(unfold acallee_saved; lia)) | rewrite Q27, E27; exact Rs11]|].
      split; [transitivity (getr (ms_regs ms0) 3); [exact (P 3 ltac:(unfold acallee_saved; lia)) | rewrite Q3, E3; exact Rgp]|].
      transitivity (getr (ms_regs ms0) 4); [exact (P 4 ltac:(unfold acallee_saved; lia)) | rewrite Q4, E4; exact Rtp].
    * rewrite El2. rewrite El1 in Hperm'. pose proof (Permutation_app_inv _ _ _ [] _ Hperm') as Hq.
      rewrite app_nil_r in Hq. exact Hq.
    * rewrite Hfd2. rewrite (proj1 (fs_wvb _ mat0)), (proj1 (fs_wvb md3 mat)). exact Hfds.
    * rewrite Hfs2. rewrite (proj2 (fs_wvb _ mat0)), (proj2 (fs_wvb md3 mat)). exact Hfs.
  + cbn [ms_regs mkst]. transitivity (getr (ms_regs ms0) 19); [exact (P 19 ltac:(unfold acallee_saved; lia)) | rewrite Q19, E19; exact R19].
  + cbn [ms_regs mkst]. transitivity (getr (ms_regs ms0) 20); [exact (P 20 ltac:(unfold acallee_saved; lia)) | rewrite Q20, E20; exact R20].
  + cbn [ms_regs mkst]. transitivity (getr (ms_regs ms0) 23); [exact (P 23 ltac:(unfold acallee_saved; lia)) | rewrite Q23, E23; exact R23].
  + exact T5.
  + cbn [ms_mem mkst]. apply (asource_none_frame KS (rdW W3 (ms_mem ms3))); [|exact Hsrc].
    intros a Ha. apply (mbyte_of_aview SEGS). rewrite <- HFm.
    destruct (asil_env _ _ _ _ ASIL a Ha) as (Hi & Ho & He). exact (K3 a Hi Ho He).
Qed.

Lemma chunk_saved : forall E (H : word -> bool) mem base off n (w : word) a v,
  ew E n = w -> v = bv_unsigned w -> base + off = a ->
  rdword (aview SEGS H mem) a = Some v ->
  YP09.chunk_ok SEGS E (mrestrict H mem) base (YP09.mkChunk off (CVal 8 (SOff n 0))).
Proof.
  intros E H mem base off n w a v Hn -> Ha Hrd.
  apply (chunk_ok_val SEGS E _ base off 8 (SOff n 0) (bv_unsigned w)).
  - cbn [sv_denot]. rewrite Hn, Z.add_0_r. reflexivity.
  - pose proof (bv_unsigned_in_range 64 w) as Hw. change (bv_modulus 64) with (2 ^ 64) in Hw. zside.
  - zside.
  - rewrite Ha. exact (val_mem_of_rdword SEGS H mem a _ Hrd).
Qed.

(* ---- W (first half): PP_K5 0x8107c -> PP_KW 0x81224, or -> pcap_source_close 0x810a8 -> PP_K6 ---------------
   addi a0,zero,-1; blt a2,a0 0x81080 (abort: the reader's answer is at least -1, res_ge); the four spill slots
   (g_file_len's auipc base, PS_FK, PS_F, PS_PSP) and ld a1,0x618(a0) = g_file_len = |F|; bne s2,a1 0x81098:
   at <> |F| goes to the check loop's prelude (a3 := -1, a4 := 0xff00, 0x81218..0x81220) and its head PP_KW;
   at = |F| falls through with want = 0 (0x8109c), bne a2,a3 0x810a0 (abort: the model answers 0 at |F|,
   res_at_end), mv a0,t4 and jal pcap_source_close (0x810a8). *)
Lemma res_ge : forall cx Q, p_kind cx Q <> PSN.KFit -> p_res cx Q = 0 \/ p_res cx Q = -1.
Proof.
  intros cx Q HK. unfold p_res, PSN.res_of. unfold p_kind in HK.
  destruct (PSN.kind (p_sw cx) (p_F cx) (p_cap cx) Q); first [left; reflexivity | right; reflexivity |
    exfalso; apply HK; reflexivity].
Qed.

Lemma kind_at_end : forall cx, PSN.kind (p_sw cx) (p_F cx) (p_cap cx) (p_nF cx) = PSN.KEnd.
Proof. intros cx. unfold PSN.kind, PSN.flen, p_nF. rewrite Z.sub_diag. reflexivity. Qed.

Lemma q_at_end : forall cx, p_q cx (p_nF cx) = p_nF cx.
Proof.
  intros cx. unfold p_q, PSN.psn_q, PSN.psn_chain.
  destruct (length (p_F cx)) as [|n] eqn:EL0; cbn [PSN.chain]; rewrite kind_at_end; reflexivity.
Qed.

Lemma res_at_end : forall cx, p_res cx (p_q cx (p_nF cx)) = 0.
Proof. intros cx. rewrite q_at_end. unfold p_res, PSN.res_of. rewrite kind_at_end. reflexivity. Qed.

Lemma branch_lt_U : forall E a b,
  branch_taken BC_LT (sv_denot E a) (sv_denot E b) = (bv_signed (sv_denot E a) <? bv_signed (sv_denot E b)).
Proof. intros E a b. reflexivity. Qed.

(* ---- the reader's chain against PWalkDef.skips, from pcap_source_struct_next.v alone (lib/Prog/Slot's proofs are
   not Required into lib/A) ---- *)
Lemma m_fb_range : forall F i, 0 <= PSN.fb F i < 256.
Proof.
  intros F i. unfold PSN.fb. pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat i) F (Z_to_bv 8 0))) as R.
  unfold bv_modulus in R. exact R.
Qed.

Lemma m_incl_nonneg : forall sw F q, 0 <= PSN.incl sw F q.
Proof.
  intros sw F q. unfold PSN.incl, PSN.hw, PSN.w32le.
  pose proof (m_fb_range F (q + 8)). pose proof (m_fb_range F (q + 8 + 1)).
  pose proof (m_fb_range F (q + 8 + 2)). pose proof (m_fb_range F (q + 8 + 3)). destruct sw; lia.
Qed.

Lemma m_kind_cuth : forall sw F cap q, PSN.flen F < q -> PSN.kind sw F cap q = PSN.KCutH.
Proof.
  intros sw F cap q H. unfold PSN.kind.
  destruct (Z.eqb_spec (PSN.flen F - q) 0); [exfalso; lia|].
  destruct (Z.ltb_spec (PSN.flen F - q) 16); [reflexivity | exfalso; lia].
Qed.

Lemma m_chain_skips : forall sw F cap f q lh, PSN.flen F - q < 16 * Z.of_nat f ->
  PWD.skips sw F cap q (fst (fst (PSN.chain sw F cap f q lh))).
Proof.
  intros sw F cap f. induction f as [|f IH]; intros q lh H.
  - cbn [PSN.chain fst]. apply PWD.skips_stop; rewrite m_kind_cuth by lia; discriminate.
  - cbn [PSN.chain]. destruct (PSN.kind sw F cap q) eqn:K.
    all: try (cbn [fst]; apply PWD.skips_stop; rewrite K; discriminate).
    + apply PWD.skips_empty; [exact K|]. apply IH. lia.
    + destruct (PSN.chain sw F cap f (q + 16 + PSN.incl sw F q) (Some q)) as [[Q0 o] l] eqn:EC. cbn [fst].
      apply PWD.skips_big; [exact K|]. pose proof (m_incl_nonneg sw F q).
      specialize (IH (q + 16 + PSN.incl sw F q) (Some q) ltac:(lia)). rewrite EC in IH. exact IH.
Qed.

Lemma m_psn_q_skips : forall sw F cap p, 0 <= p -> PWD.skips sw F cap p (PSN.psn_q sw F cap p).
Proof. intros sw F cap p Hp. unfold PSN.psn_q, PSN.psn_chain. apply m_chain_skips. unfold PSN.flen. lia. Qed.

Lemma m_skips_exit : forall sw F cap q Q, PWD.skips sw F cap q Q ->
  PSN.kind sw F cap q <> PSN.KEmpty -> PSN.kind sw F cap q <> PSN.KBig -> Q = q.
Proof. intros sw F cap q Q H K1 K2. inversion H; subst; first [reflexivity | congruence]. Qed.

Lemma m_skips_empty_inv : forall sw F cap q Q, PWD.skips sw F cap q Q -> PSN.kind sw F cap q = PSN.KEmpty ->
  PWD.skips sw F cap (q + 16) Q.
Proof. intros sw F cap q Q H K. inversion H; subst; first [assumption | congruence]. Qed.

Lemma m_skips_big_inv : forall sw F cap q Q, PWD.skips sw F cap q Q -> PSN.kind sw F cap q = PSN.KBig ->
  PWD.skips sw F cap (q + 16 + PSN.incl sw F q) Q.
Proof. intros sw F cap q Q H K. inversion H; subst; first [assumption | congruence]. Qed.

Lemma m_skips_le : forall sw F cap q Q, PWD.skips sw F cap q Q -> q <= Q.
Proof.
  intros sw F cap q Q H. induction H as [q _ _|q Q _ _ IH|q Q _ _ IH]; [lia | lia |].
  pose proof (m_incl_nonneg sw F q). lia.
Qed.

(* ---- the loop's record-length assembly (0x81290..0x812dc), in Z ---- *)

(* The unsigned 64-bit value of a 32-bit result sign-extended (RV64's *w instructions). *)
Definition sx32u (v : Z) : Z := if v <? 2 ^ 31 then v else v - 2 ^ 32 + 2 ^ 64.

Lemma lor_add_lo : forall a b n, 0 <= n -> 0 <= a < 2 ^ n -> 0 <= b -> b mod 2 ^ n = 0 -> Z.lor a b = a + b.
Proof.
  intros a b n Hn Ha Hb Hm.
  assert (HL : Z.land a b = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i n) as [Hlt|Hge].
    - rewrite <- (Z.mod_pow2_bits_low b n i Hlt), Hm, Z.bits_0. apply andb_false_r.
    - rewrite <- (Z.mod_small a (2 ^ n)) by lia. rewrite Z.mod_pow2_bits_high by lia. reflexivity. }
  rewrite <- Z.lxor_lor by exact HL. symmetry. apply Z.add_nocarry_lxor. exact HL.
Qed.

Lemma land_ff00 : forall x, 0 <= x -> Z.land x (Z.ones 8 * 2 ^ 8) = (x / 2 ^ 8) mod 2 ^ 8 * 2 ^ 8.
Proof.
  intros x Hx. apply Z.bits_inj'. intros i Hi.
  rewrite Z.land_spec, !Z.mul_pow2_bits by lia.
  destruct (Z.ltb_spec i 8) as [Hl|Hl].
  - rewrite (Z.testbit_neg_r (Z.ones 8) (i - 8)), (Z.testbit_neg_r (x / 2 ^ 8 mod 2 ^ 8) (i - 8)) by lia.
    apply andb_false_r.
  - destruct (Z.ltb_spec (i - 8) 8) as [Hl2|Hl2].
    + rewrite Z.ones_spec_low by lia. rewrite Z.mod_pow2_bits_low by lia. rewrite Z.div_pow2_bits by lia.
      rewrite andb_true_r. f_equal. lia.
    + rewrite Z.ones_spec_high by lia. rewrite Z.mod_pow2_bits_high by lia. apply andb_false_r.
Qed.

Lemma wrap_swrap32 : forall z, bv_wrap 64 (bv_swrap 32 z) = sx32u (z mod 2 ^ 32).
Proof.
  intros z. unfold bv_swrap, bv_wrap, sx32u.
  replace (bv_half_modulus 32) with (2 ^ 31) by reflexivity.
  replace (bv_modulus 32) with (2 ^ 32) by reflexivity. replace (bv_modulus 64) with (2 ^ 64) by reflexivity.
  rewrite <- Zplus_mod_idemp_l. set (m := z mod 2 ^ 32).
  assert (Hm : 0 <= m < 2 ^ 32) by (apply Z.mod_pos_bound; lia).
  destruct (Z.ltb_spec m (2 ^ 31)) as [Hl|Hl].
  - rewrite (Z.mod_small (m + 2 ^ 31)) by lia. replace (m + 2 ^ 31 - 2 ^ 31) with m by ring. apply Z.mod_small. lia.
  - replace (m + 2 ^ 31) with ((m + 2 ^ 31 - 2 ^ 32) + 1 * 2 ^ 32) by ring.
    rewrite Z.mod_add by lia. rewrite (Z.mod_small (m + 2 ^ 31 - 2 ^ 32)) by lia.
    replace (m + 2 ^ 31 - 2 ^ 32 - 2 ^ 31) with ((m - 2 ^ 32 + 2 ^ 64) + (-1) * 2 ^ 64) by ring.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

Lemma sx32u_mod : forall w, 0 <= w < 2 ^ 32 -> sx32u w mod 2 ^ 32 = w.
Proof.
  intros w Hw. unfold sx32u. destruct (Z.ltb_spec w (2 ^ 31)); [apply Z.mod_small; lia|].
  replace (w - 2 ^ 32 + 2 ^ 64) with (w + (2 ^ 32 - 1) * 2 ^ 32) by ring. rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

Lemma sx32u_range : forall w, 0 <= w < 2 ^ 32 -> 0 <= sx32u w < 2 ^ 64.
Proof. intros w Hw. unfold sx32u. destruct (Z.ltb_spec w (2 ^ 31)); lia. Qed.

Lemma sx32u_zero : forall w, 0 <= w < 2 ^ 32 -> (sx32u w =? 0) = (w =? 0).
Proof. intros w Hw. unfold sx32u. destruct (Z.ltb_spec w (2 ^ 31)); [reflexivity|]. rewrite !(proj2 (Z.eqb_neq _ _)) by lia. reflexivity. Qed.

(* sx32u (a * 2^24) is a multiple of 2^k for k <= 24, and adding a low part below 2^24 commutes with it. *)
Lemma sx32u_hi_mod : forall a k, 0 <= a < 256 -> 0 <= k <= 24 -> sx32u (a * 2 ^ 24) mod 2 ^ k = 0.
Proof.
  intros a k Ha Hk. unfold sx32u.
  assert (E24 : 2 ^ 24 = 2 ^ (24 - k) * 2 ^ k) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  destruct (Z.ltb_spec (a * 2 ^ 24) (2 ^ 31)).
  - rewrite E24, Z.mul_assoc. apply Z.mod_mul. lia.
  - replace (a * 2 ^ 24 - 2 ^ 32 + 2 ^ 64) with ((a - 2 ^ 8 + 2 ^ 40) * 2 ^ (24 - k) * 2 ^ k)
      by (rewrite <- Z.mul_assoc, <- E24; ring). apply Z.mod_mul. lia.
Qed.

Lemma sx32u_add_lo : forall a lo, 0 <= a < 256 -> 0 <= lo < 2 ^ 24 -> sx32u (a * 2 ^ 24) + lo = sx32u (a * 2 ^ 24 + lo).
Proof.
  intros a lo Ha Hlo. unfold sx32u.
  destruct (Z.ltb_spec (a * 2 ^ 24) (2 ^ 31)); destruct (Z.ltb_spec (a * 2 ^ 24 + lo) (2 ^ 31)); try lia.
Qed.

Lemma sx32u_hi_lt : forall a, 0 <= a < 256 -> 0 <= sx32u (a * 2 ^ 24) <= 2 ^ 64 - 2 ^ 24.
Proof. intros a Ha. unfold sx32u. destruct (Z.ltb_spec (a * 2 ^ 24) (2 ^ 31)); lia. Qed.

Section asm. Context (E : env).

Lemma U_zb : forall n c, ew E n = Z_to_bv 64 c -> 0 <= c < 256 -> U E (SExt false 8 (SOff n 0)) = c.
Proof.
  intros n c Hn Hc. rewrite U_zext, (U_atom E n c Hn) by lia. change (2 ^ Z.of_N 8) with 256. apply Z.mod_small. lia.
Qed.

Lemma U_sll_k : forall a x k, U E a = x -> 0 <= x -> 0 <= k < 64 -> x * 2 ^ k < 2 ^ 64 ->
  U E (SAlu ALU_SLL a (SLit k)) = x * 2 ^ k.
Proof.
  intros a x k Ha Hx Hk Hb. rewrite U_SAlu. cbn [zalu_raw]. rewrite Ha, U_SLit, (zcanon_id k) by (unfold M64; lia).
  change 63 with (Z.ones 6). rewrite Z.land_ones by lia. rewrite (Z.mod_small k (2 ^ 6)) by lia.
  rewrite Z.shiftl_mul_pow2 by lia. apply zcanon_id. unfold M64. lia.
Qed.

Lemma U_srl_k : forall a x k, U E a = x -> 0 <= k < 64 -> U E (SAlu ALU_SRL a (SLit k)) = x / 2 ^ k.
Proof.
  intros a x k Ha Hk. pose proof (U_range E a) as R. rewrite Ha in R. unfold M64 in R.
  rewrite U_SAlu. cbn [zalu_raw]. rewrite Ha, U_SLit, (zcanon_id k) by (unfold M64; lia).
  change 63 with (Z.ones 6). rewrite Z.land_ones by lia. rewrite (Z.mod_small k (2 ^ 6)) by lia.
  rewrite Z.shiftr_div_pow2 by lia. apply zcanon_id. unfold M64.
  pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) ltac:(lia)). split; [apply Z.div_pos; lia|].
  apply (Z.le_lt_trans _ x); [apply Z.div_le_upper_bound; nia | lia].
Qed.

Lemma U_or_l : forall a b x y n, U E a = x -> U E b = y -> 0 <= n -> 0 <= x < 2 ^ n -> 0 <= y -> y mod 2 ^ n = 0 ->
  x + y < 2 ^ 64 -> U E (SAlu ALU_OR a b) = x + y.
Proof.
  intros a b x y n Ha Hb Hn Hx Hy Hm Hs. rewrite U_SAlu. cbn [zalu_raw]. rewrite Ha, Hb.
  rewrite (lor_add_lo x y n Hn Hx Hy Hm). apply zcanon_id. unfold M64. lia.
Qed.

Lemma U_or_r : forall a b x y n, U E a = y -> U E b = x -> 0 <= n -> 0 <= x < 2 ^ n -> 0 <= y -> y mod 2 ^ n = 0 ->
  x + y < 2 ^ 64 -> U E (SAlu ALU_OR a b) = y + x.
Proof.
  intros a b x y n Ha Hb Hn Hx Hy Hm Hs. rewrite U_SAlu. cbn [zalu_raw]. rewrite Ha, Hb, Z.lor_comm.
  rewrite (lor_add_lo x y n Hn Hx Hy Hm), Z.add_comm. apply zcanon_id. unfold M64. lia.
Qed.

Lemma U_sllw_k : forall a x k, U E a = x -> 0 <= k < 32 -> U E (SAluw ALU_SLL a (SLit k)) = sx32u ((x * 2 ^ k) mod 2 ^ 32).
Proof.
  intros a x k Ha Hk. rewrite U_of_S, S_SAluw. cbn [zalu_raw]. rewrite Ha, U_SLit, (zcanon_id k) by (unfold M64; lia).
  rewrite (Z.mod_small k (2 ^ 32)) by lia. change 31 with (Z.ones 5). rewrite Z.land_ones by lia.
  rewrite (Z.mod_small k (2 ^ 5)) by lia. rewrite Z.shiftl_mul_pow2 by lia. rewrite wrap_swrap32.
  rewrite Zmult_mod_idemp_l. reflexivity.
Qed.

Lemma U_srlw_k : forall a x k, U E a = x -> 0 <= k < 32 -> U E (SAluw ALU_SRL a (SLit k)) = sx32u ((x mod 2 ^ 32) / 2 ^ k).
Proof.
  intros a x k Ha Hk. rewrite U_of_S, S_SAluw. cbn [zalu_raw]. rewrite Ha, U_SLit, (zcanon_id k) by (unfold M64; lia).
  rewrite (Z.mod_small k (2 ^ 32)) by lia. change 31 with (Z.ones 5). rewrite Z.land_ones by lia.
  rewrite (Z.mod_small k (2 ^ 5)) by lia. rewrite Z.shiftr_div_pow2 by lia. rewrite wrap_swrap32. f_equal.
  pose proof (Z.mod_pos_bound x (2 ^ 32) ltac:(lia)). pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) ltac:(lia)).
  apply Z.mod_small. split; [apply Z.div_pos; lia|].
  apply (Z.le_lt_trans _ (x mod 2 ^ 32)); [apply Z.div_le_upper_bound; nia | lia].
Qed.

Lemma U_zx32 : forall a x, U E a = x -> U E (SAlu ALU_SRL (SAlu ALU_SLL a (SLit 32)) (SLit 32)) = x mod 2 ^ 32.
Proof.
  intros a x Ha. pose proof (U_range E a) as R. rewrite Ha in R. unfold M64 in R.
  rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite Ha, !U_SLit.
  change (Z.land (zcanon 32) 63) with 32. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  assert (Hz : zcanon (x * 2 ^ 32) = (x mod 2 ^ 32) * 2 ^ 32).
  { unfold zcanon, M64. replace (2 ^ 64) with (2 ^ 32 * 2 ^ 32) by reflexivity. apply Z.mul_mod_distr_r; lia. }
  rewrite Hz, Z.div_mul by lia. apply zcanon_id. unfold M64. pose proof (Z.mod_pos_bound x (2 ^ 32) ltac:(lia)). lia.
Qed.

Variables (c0 c1 c2 c3 : Z).
Hypotheses (H34 : ew E 34 = Z_to_bv 64 c0) (H35 : ew E 35 = Z_to_bv 64 c1)
  (H36 : ew E 36 = Z_to_bv 64 c2) (H37 : ew E 37 = Z_to_bv 64 c3).
Hypotheses (R0 : 0 <= c0 < 256) (R1 : 0 <= c1 < 256) (R2 : 0 <= c2 < 256) (R3 : 0 <= c3 < 256).

Definition zb (n : nat) : sv := SExt false 8 (SOff n 0).
Definition a_expr : sv :=
  SAlu ALU_OR (SAlu ALU_OR (SAlu ALU_SLL (zb 35) (SLit 8)) (zb 34)) (SAlu ALU_SLL (zb 36) (SLit 16)).
Definition ns_expr : sv := SAlu ALU_OR a_expr (SAluw ALU_SLL (zb 37) (SLit 24)).
Definition sw_expr : sv :=
  SAlu ALU_OR
    (SAlu ALU_OR (SAluw ALU_SLL a_expr (SLit 24)) (SAlu ALU_SLL (SAlu ALU_AND ns_expr (SOff 14 0)) (SLit 8)))
    (SAlu ALU_OR (SAlu ALU_SLL (SAlu ALU_SRL a_expr (SLit 16)) (SLit 8))
       (SAluw ALU_SRL (SAluw ALU_SLL (zb 37) (SLit 24)) (SLit 24))).

Lemma U_a_expr : U E a_expr = c0 + c1 * 2 ^ 8 + c2 * 2 ^ 16.
Proof.
  unfold a_expr, zb.
  assert (U1 : U E (SAlu ALU_SLL (SExt false 8 (SOff 35 0)) (SLit 8)) = c1 * 2 ^ 8)
    by (apply U_sll_k; [apply U_zb; assumption | lia | lia | lia]).
  assert (U01 : U E (SAlu ALU_OR (SAlu ALU_SLL (SExt false 8 (SOff 35 0)) (SLit 8)) (SExt false 8 (SOff 34 0))) =
    c1 * 2 ^ 8 + c0) by (apply (U_or_r _ _ c0 (c1 * 2 ^ 8) 8); [exact U1 | apply U_zb; assumption | lia | lia | lia |
      apply Z.mod_mul; lia | lia]).
  assert (U2 : U E (SAlu ALU_SLL (SExt false 8 (SOff 36 0)) (SLit 16)) = c2 * 2 ^ 16)
    by (apply U_sll_k; [apply U_zb; assumption | lia | lia | lia]).
  rewrite (U_or_l _ _ (c1 * 2 ^ 8 + c0) (c2 * 2 ^ 16) 16 U01 U2); [lia | lia | lia | lia | apply Z.mod_mul; lia | lia].
Qed.

Lemma U_b3 : U E (SAluw ALU_SLL (zb 37) (SLit 24)) = sx32u (c3 * 2 ^ 24).
Proof. unfold zb. rewrite (U_sllw_k _ c3 24) by (first [apply U_zb; assumption | lia]). f_equal. apply Z.mod_small. lia. Qed.

Lemma U_ns_expr : U E ns_expr = sx32u (PSN.w32le c0 c1 c2 c3).
Proof.
  unfold ns_expr. pose proof (sx32u_hi_lt c3 R3).
  rewrite (U_or_l _ _ (c0 + c1 * 2 ^ 8 + c2 * 2 ^ 16) (sx32u (c3 * 2 ^ 24)) 24 U_a_expr U_b3);
    [| lia | lia | lia | apply sx32u_hi_mod; lia | lia].
  rewrite Z.add_comm, sx32u_add_lo by lia. unfold PSN.w32le. f_equal. lia.
Qed.

Lemma U_sw_expr : U E (SOff 14 0) = 65280 -> U E sw_expr = sx32u (PSN.w32le c3 c2 c1 c0).
Proof.
  intros H14. unfold sw_expr.
  assert (UA24 : U E (SAluw ALU_SLL a_expr (SLit 24)) = sx32u (c0 * 2 ^ 24)).
  { rewrite (U_sllw_k _ _ 24 U_a_expr) by lia. f_equal.
    replace ((c0 + c1 * 2 ^ 8 + c2 * 2 ^ 16) * 2 ^ 24) with (c0 * 2 ^ 24 + (c1 + c2 * 2 ^ 8) * 2 ^ 32) by ring.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
  assert (UAND : U E (SAlu ALU_AND ns_expr (SOff 14 0)) = c1 * 2 ^ 8).
  { rewrite U_SAlu. cbn [zalu_raw]. rewrite U_ns_expr, H14. change 65280 with (Z.ones 8 * 2 ^ 8).
    assert (HW : 0 <= PSN.w32le c0 c1 c2 c3 < 2 ^ 32) by (unfold PSN.w32le; lia).
    rewrite land_ff00 by (pose proof (sx32u_range _ HW); lia).
    assert (Hq : (sx32u (PSN.w32le c0 c1 c2 c3) / 2 ^ 8) mod 2 ^ 8 = c1).
    { unfold sx32u, PSN.w32le.
      destruct (Z.ltb_spec (c0 + 256 * c1 + 65536 * c2 + 16777216 * c3) (2 ^ 31)).
      - replace (c0 + 256 * c1 + 65536 * c2 + 16777216 * c3) with (c0 + (c1 + (c2 + c3 * 2 ^ 8) * 2 ^ 8) * 2 ^ 8) by ring.
        rewrite Z.div_add by lia. rewrite (Z.div_small c0) by lia. rewrite Z.add_0_l, Z.mod_add by lia.
        apply Z.mod_small. lia.
      - replace (c0 + 256 * c1 + 65536 * c2 + 16777216 * c3 - 2 ^ 32 + 2 ^ 64)
          with (c0 + (c1 + (c2 + (c3 - 2 ^ 8 + 2 ^ 40) * 2 ^ 8) * 2 ^ 8) * 2 ^ 8) by ring.
        rewrite Z.div_add by lia. rewrite (Z.div_small c0) by lia. rewrite Z.add_0_l, Z.mod_add by lia.
        apply Z.mod_small. lia. }
    rewrite Hq. apply zcanon_id. unfold M64. lia. }
  assert (UL1 : U E (SAlu ALU_SLL (SAlu ALU_AND ns_expr (SOff 14 0)) (SLit 8)) = c1 * 2 ^ 16).
  { rewrite (U_sll_k _ _ 8 UAND) by lia. lia. }
  assert (UL : U E (SAlu ALU_OR (SAluw ALU_SLL a_expr (SLit 24))
                     (SAlu ALU_SLL (SAlu ALU_AND ns_expr (SOff 14 0)) (SLit 8))) = sx32u (c0 * 2 ^ 24) + c1 * 2 ^ 16).
  { pose proof (sx32u_hi_lt c0 R0).
    apply (U_or_r _ _ (c1 * 2 ^ 16) (sx32u (c0 * 2 ^ 24)) 24 UA24 UL1); [lia | lia | lia | apply sx32u_hi_mod; lia | lia]. }
  assert (UC2 : U E (SAlu ALU_SLL (SAlu ALU_SRL a_expr (SLit 16)) (SLit 8)) = c2 * 2 ^ 8).
  { assert (Hd : U E (SAlu ALU_SRL a_expr (SLit 16)) = c2).
    { rewrite (U_srl_k _ _ 16 U_a_expr) by lia.
      replace (c0 + c1 * 2 ^ 8 + c2 * 2 ^ 16) with ((c0 + c1 * 2 ^ 8) + c2 * 2 ^ 16) by ring.
      rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia. }
    rewrite (U_sll_k _ _ 8 Hd) by lia. reflexivity. }
  assert (UC3 : U E (SAluw ALU_SRL (SAluw ALU_SLL (zb 37) (SLit 24)) (SLit 24)) = c3).
  { rewrite (U_srlw_k _ _ 24 U_b3) by lia. rewrite sx32u_mod by lia.
    rewrite Z.div_mul by lia. unfold sx32u. destruct (Z.ltb_spec c3 (2 ^ 31)); lia. }
  assert (UR : U E (SAlu ALU_OR (SAlu ALU_SLL (SAlu ALU_SRL a_expr (SLit 16)) (SLit 8))
                     (SAluw ALU_SRL (SAluw ALU_SLL (zb 37) (SLit 24)) (SLit 24))) = c2 * 2 ^ 8 + c3).
  { apply (U_or_r _ _ c3 (c2 * 2 ^ 8) 8 UC2 UC3); [lia | lia | lia | apply Z.mod_mul; lia | lia]. }
  pose proof (sx32u_hi_lt c0 R0).
  rewrite (U_or_r _ _ (c2 * 2 ^ 8 + c3) (sx32u (c0 * 2 ^ 24) + c1 * 2 ^ 16) 16 UL UR); [| lia | lia | lia | | lia].
  - rewrite <- Z.add_assoc, sx32u_add_lo by lia. unfold PSN.w32le. f_equal. lia.
  - replace (sx32u (c0 * 2 ^ 24) + c1 * 2 ^ 16) with (sx32u (c0 * 2 ^ 24) + c1 * 2 ^ 16) by reflexivity.
    rewrite Zplus_mod. rewrite sx32u_hi_mod by lia. rewrite Z.mod_mul by lia. reflexivity.
Qed.

End asm.

Definition w5_rs : smem :=
  [ YP09.mkRegion (Some 9%nat) 16 96 0 0
      [YP09.mkChunk 16 (CVal 8 (SOff 33 0)); YP09.mkChunk 24 (CVal 8 (SOff 33 0));
       YP09.mkChunk 64 (CVal 8 (SOff 32 0)); YP09.mkChunk 88 (CVal 8 (SOff 34 0))];
    YP09.mkRegion (Some 32%nat) PE_GLEN_LO PE_GLEN_LO8 0 0 [YP09.mkChunk PE_GLEN_LO (CVal 8 (SOff 35 0))] ].

(* 0x810a0, where both halves of W end: the harness compares the reader's answer n with the `want` its own walk
   computed, then closes the reader. Every exit of the check loop and the at = |F| arm of PP_K5 reach it with
   want = n, so the abort is never taken. *)
Definition PP_W0 : Z := 0x968.

Lemma inG_obj2 : forall x, pa_val (A_OBJ 2) <= x < pa_val (A_OBJ 2) + 8 -> inG pe_G x.
Proof.
  intros x Hx. unfold inG, pe_G. apply Exists_exists. exists (pa_val (A_OBJ 2), 8).
  split; [cbn [In]; right; left; reflexivity | unfold in_zr; cbn [fst snd]; lia].
Qed.

Lemma inG_obj4 : forall x, pa_val (A_OBJ 4) <= x < pa_val (A_OBJ 4) + 8 -> inG pe_G x.
Proof.
  intros x Hx. unfold inG, pe_G. apply Exists_exists. exists (pa_val (A_OBJ 4), 8).
  split; [cbn [In]; left; reflexivity | unfold in_zr; cbn [fst snd]; lia].
Qed.

Lemma tail_close6 : pe_from SK B MT KS POST (GI_K6 B MT KS) ->
  forall cx fp k acc ly3 S3 W3 ms3 md3 (b h buf p : Z),
  pe_base SK B MT KS cx ->
  ajournal_gx SEGS B pe_G 0 [] LLVMF_STK (spZ (c_regs cx)) [sink_token] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx)
    (c_md cx) [(PE_CID, fp)] ly3 S3 W3 (ms_mem ms3) md3 k ->
  frames S3 = [(PE_CID, fp)] -> mo_le MT (c_S cx) S3 acc ->
  p_cut B cx fp PP_W0 PSH_ts k 3 acc (PA_K3 MT cx) [(b, p_nF cx); (h, SRC_FILE_BLOCK); (buf, p_bn cx)] ly3 S3 W3 ms3 md3 ->
  p_pspad cx fp W3 ms3 -> c_n cx < 2 ^ 26 -> p_good cx = true ->
  getr (ms_regs ms3) 12 = w64 (p_res cx (p_q cx p)) -> getr (ms_regs ms3) 13 = w64 (p_res cx (p_q cx p)) ->
  getr (ms_regs ms3) 19 = w64 b -> getr (ms_regs ms3) 20 = w64 (pF cx fp) ->
  getr (ms_regs ms3) 21 = w64 (p_cap cx) -> getr (ms_regs ms3) 22 = w64 buf ->
  getr (ms_regs ms3) 23 = w64 (pF cx fp) -> getr (ms_regs ms3) 26 = w64 (p_first cx) ->
  getr (ms_regs ms3) 29 = w64 (pPS cx fp) ->
  pslots cx fp W3 ms3 -> p_glob cx W3 ms3 b -> p_reader KS cx fp W3 ms3 b h buf p ->
  SRr SEGS W3 (mkCfg ms3 md3) (POST cx).
Proof.
intros NEXT cx fp k acc ly3 S3 W3 ms3 md3 bb hh bf p HB HJ Hfrs Hmo
  (Hbody & Hk & Hacc & Hperm & Hfds & Hfs) Hpad Hn26 Hgood R12 R13 R19 R20 R21 R22 R23 R26 R29 Hslots Hglob Hreader.
destruct Hbody as (Hpc & Hresv & Hsvc & Hrom & Hfrg & Hfcsr & Hregs & Hsaved & Hhdr & Hsh & Hlen & Hin).
destruct Hreader as (Hsrc & (Hpsf & Hpsw) & Hfit).
pose proof (tail_geo cx HB) as (Hal & Hs1m & Hs1b & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
unfold LLVMF_STK in Hslo, Hbot.
pose proof HB as ((HAR0 & Hrok & Hra4 & Hgp0 & Htp0 & _) & HraL & _ & _ & _ & _ & _ & Hev & Hlive & _ & _ & _ & _ & _ &
  _ & _ & Hmok & Hneed & HGX & HGD & _ & _ & Hftr).
destruct (gx_open _ _ _ _ _ _ _ _ HJ) as (memS & HJi & Hag). clear HJ. rename HJi into HJ.
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & Hnev & Hk0 & _).
destruct Hregs as (Rsp & Rs0 & Rs1 & Rs11 & Rgp & Rtp).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as (HB0 & HB1 & HB2). pose proof (pa_base_lo (PL := PL_pcap) (PI := PI)) as HBLO.
pose proof (p_sizes cx) as (Hsz1 & Hsz2 & Hsz3).
destruct (lay_eqs _ _ _ Hly) as (EF & Etop & Eslo & Eshi).
assert (Efa : frame_addr ly3 PE_CID fp = pF cx fp) by (unfold pF, frame_addr; rewrite EF; reflexivity).
assert (Hfin : In (PE_CID, fp) (frames S3)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 PE_CID fp HAR Hfin) as (Hf4096 & Hfceil & Hfapp).
rewrite Efa in Hf4096, Hfceil, Hfapp. change (fs_frame_bytes PE_CID) with 128 in Hfceil, Hfapp.
destruct (frame_al64 SEGS B ly3 S3 W3 (ms_mem ms3) md3 PE_CID fp HAR Hfin) as (Hfa64 & _ & _). rewrite Efa in Hfa64.
assert (Hbin : In (bb, p_nF cx) (ablocks B ly3 S3))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; right; left; reflexivity).
assert (Hhin : In (hh, SRC_FILE_BLOCK) (ablocks B ly3 S3))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; right; right; left; reflexivity).
assert (Hhout : ~ In (hh, SRC_FILE_BLOCK) (ablocks B (c_ly cx) (c_S cx)))
  by (refine (notin_prefix _ _ _ _ (ablocks_nodup _ _ _ _ _ HAR) Hperm _); right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ hh SRC_FILE_BLOCK HAR Hhin) as (_ & Hh4096 & Hhceil & _ & _ & _ & _).
change (req_size SRC_FILE_BLOCK) with 1304 in Hhceil.
assert (ELC : Z.of_nat (length (p_C cx)) = p_nF cx) by (unfold p_C, p_nF; rewrite length_map; reflexivity).
assert (Hps : pPS cx fp = pF cx fp + 32) by reflexivity.
assert (Hps8 : pPS cx fp mod 8 = 0).
{ rewrite Hps. apply Z.mod_divide; [lia|]. apply Z.mod_divide in Hfa64; [|lia]. destruct Hfa64 as [q Hq]. exists (8 * q + 4). lia. }
pose proof (entry0 PP_W0 ms3 W3 Hpc Hresv Hsvc Hrom Hfrg Hfcsr) as HS.
remember (Eimg (Ereg (ms_regs ms3) [])) as E eqn:HEdef.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg (ms_regs ms3) []) n)
  by (intros n Hn; subst E; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr (ms_regs ms3) 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr (ms_regs ms3) 3) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr (ms_regs ms3) 4) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 4 4%bv eq_refl)).
assert (E8 : ew E 8 = getr (ms_regs ms3) 8) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 8 8%bv eq_refl)).
assert (E9 : ew E 9 = getr (ms_regs ms3) 9) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 9 9%bv eq_refl)).
assert (E12 : ew E 12 = getr (ms_regs ms3) 12) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 12 12%bv eq_refl)).
assert (E13 : ew E 13 = getr (ms_regs ms3) 13) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 13 13%bv eq_refl)).
assert (E19 : ew E 19 = getr (ms_regs ms3) 19) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 19 19%bv eq_refl)).
assert (E20 : ew E 20 = getr (ms_regs ms3) 20) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 20 20%bv eq_refl)).
assert (E21 : ew E 21 = getr (ms_regs ms3) 21) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 21 21%bv eq_refl)).
assert (E22 : ew E 22 = getr (ms_regs ms3) 22) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 22 22%bv eq_refl)).
assert (E23 : ew E 23 = getr (ms_regs ms3) 23) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 23 23%bv eq_refl)).
assert (E26 : ew E 26 = getr (ms_regs ms3) 26) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 26 26%bv eq_refl)).
assert (E27 : ew E 27 = getr (ms_regs ms3) 27) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 27 27%bv eq_refl)).
assert (E29 : ew E 29 = getr (ms_regs ms3) 29) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 29 29%bv eq_refl)).
assert (SHOK : sh_ok SEGS TBx [] E (mrestrict (w_H W3) (ms_mem ms3))) by constructor.
clear HEdef EL.
(* 0x810a0 bne a2,a3 to the abort: both hold the reader's answer *)
psrr_branch_tok RUN BR HS SHOK TBspan.
{ exfalso. rewrite branch_ne_U in Hc. unfold U in Hc. cbn [sv_denot] in Hc.
  rewrite E12, E13, R12, R13, Z.eqb_refl in Hc. discriminate Hc. }
clear Hc.
(* 0x810a4 mv a0,t4; 0x810a8 jal pcap_source_close *)
paj_run_tok RUN HS HJ SHOK TBspan; [apply awr_ok_nil |].
assert (HFm : ms_mem ms = ms_mem ms3) by exact (frame_of_nil _ _ _ HF).
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (10%bv : bv 5) Q10. prreg HS (19%bv : bv 5) Q19.
prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21. prreg HS (22%bv : bv 5) Q22. prreg HS (23%bv : bv 5) Q23.
prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
rewrite pa_sigma_pcap_source_close.
assert (Hsp : spZ (ms_regs ms) = c_sp1 cx) by (unfold spZ at 1; rewrite Q2, E2, Rsp; unfold w64; apply unsigned_lit_small; lia).
eapply SRr_bind.
{ eapply (CLOSE LLVMF_STK (spZ (c_regs cx)) [sink_token] (c_ly cx) (c_S cx) (c_W cx) memS (c_md cx) [(PE_CID, fp)]
    ly3 S3 W3 (ms_mem ms) _ k (ms_regs ms) (pPS cx fp) hh bb (c_M cx) (p_pos cx (p_q cx p)) (p_C cx) PE_CID fp HJ).
  - exact (aro_now cx memS _ ly3 S3 W3 (ms_mem ms) _ k HB HJ Hag).
  - rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - unfold raZ. rewrite Q1, unsigned_lit_small by lia. lia.
  - rewrite Q3, E3, Rgp. exact Hgp0.
  - rewrite Q4, E4, Rtp. exact Htp0.
  - rewrite Q10, E29, R29. reflexivity.
  - rewrite Hsp. apply Z.mod_divide; [lia|]. apply Z.mod_divide in Hs1m; [|lia]. destruct Hs1m as [q Hq]. exists (2 * q). lia.
  - rewrite Hsp. assert (HTS : TPCAP_SOURCE_CLOSE_STK = 16560) by reflexivity. rewrite HTS. unfold LLVMF_STK. lia.
  - rewrite Hsp. lia.
  - left. reflexivity.
  - rewrite Efa, Hps. lia.
  - rewrite Efa, Hps. change (fs_frame_bytes PE_CID) with 128. lia.
  - rewrite Hps. split; [lia|]. rewrite <- Hps. exact Hps8.
  - rewrite HFm. exact Hpsf.
  - lia.
  - rewrite HFm. apply zero_shadow_range; [exact Hps8 | reflexivity |].
    intros i Hi. change (8 / 8) with 1 in Hi. replace i with 0 by lia. rewrite Z.add_0_r.
    rewrite Hps, shadow_of_addr_aligned_off by (apply Z.mod_divide; [lia|]; apply Z.mod_divide in Hfa64; [|lia];
      destruct Hfa64 as [q Hq]; exists (8 * q); lia).
    change (32 / 8) with 4. exact (Hsh 4%nat ltac:(rewrite Hlen; unfold PE_NSH; lia)).
  - intros _. split; [exact Hhin|]. split.
    { rewrite ELC. exact Hbin. }
    split; [rewrite HFm; exact Hsrc|]. split; [exact (meta_now cx memS _ ly3 S3 W3 (ms_mem ms) _ k HB HJ Hag)|].
    intros x Hx. unfold asource_fp in Hx. apply inFP_cons in Hx as [Hx|Hx]; [|left; exact Hx].
    right. exists hh, SRC_FILE_BLOCK. split; [exact Hhin|]. split; [exact Hhout|]. change (req_size SRC_FILE_BLOCK) with 1304.
    unfold SRC_FILE_BLOCK in Hx. lia.
  - unfold EV_CLOSE, EV_LIB in *. lia. }
cbv beta. intros W2 c2 Hwle (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hfr2 & Hmle & Hfd2 & Hfs2 & HPm & Hnull & HK & Hsrc2).
rewrite Q1.
assert (Hh0 : hh <> 0) by lia.
unfold tclose_fblk in HPm. destruct (Z.eqb_spec hh 0) as [|_]; [lia|]. cbn [app] in HPm.
destruct (Z.eqb_spec hh 0) as [|_]; [lia|].
destruct (Hsrc2 Hh0) as [Hnone2 Hcopy2].
destruct HK as (K1 & K2 & K3 & K4 & K5 & K6).
assert (Hfoot : forall a, hfoot cx fp a -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W3) (ms_mem ms3) a).
{ intros a Ha. rewrite <- HFm.
  refine (foot_kept cx fp ly3 S3 W3 (ms_mem ms) W2 mem2 _ _
    (fun a => (pPS cx fp <= a < pPS cx fp + 8) \/ (hh <> 0 /\ hh <= a < hh + req_size SRC_FILE_BLOCK)) HB
    (fun a Ha1 Hn1 _ => K1 a Ha1 Hn1) K2 K4 _ Hfin Efa (input_block cx ly3 S3 _ HB Hperm) _ a Ha); [rewrite Hsp; lia|].
  intros x Hx [Hx1 | [_ Hx2]].
  - exact (frame_off_hfoot cx fp ly3 S3 W3 (ms_mem ms3) md3 _ (pPS cx fp) 8 HB HAR Hperm Hfin Efa ltac:(rewrite Hps; lia)
      ltac:(rewrite Hps; lia) x Hx Hx1).
  - exact (block_off_hfoot cx fp ly3 S3 W3 (ms_mem ms3) md3 _ hh SRC_FILE_BLOCK HB HAR Hperm Hhin Hhout Hfin Efa x Hx Hx2). }
assert (HGkeep : forall a, inG pe_G a -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W3) (ms_mem ms3) a).
{ intros a Ha. rewrite <- HFm. pose proof (HGD a Ha) as (Hro1 & Hme1 & Her1 & Hof1 & _).
  apply K3; [exact (proj1 (HGX a Ha)) | exact (proj2 (HGX a Ha)) | exact Her1 | exact Hof1]. }
destruct (tail_kept cx fp W3 ms3 W2 (mkst regs2 (Z_to_bv 64 (BASE + PP_K6)) mem2 (seg_rom SEGS)) PSH_ts Hfoot
  Hsaved Hhdr Hsh Hlen Hin Hslots) as (T1 & T2 & T3 & T4 & T5).
assert (P : forall r : Z, acallee_saved r -> getr regs2 (Z_to_bv 5 r) = getr (ms_regs ms) (Z_to_bv 5 r)) by exact HP2.
eapply (NEXT cx fp (k + EV_CLOSE) (acc + (mo_free MT + mo_free MT)) ly2 S2 W2
  (mkst regs2 (Z_to_bv 64 (BASE + PP_K6)) mem2 (seg_rom SEGS)) md2 HB).
- exact (gx_pack0 cx _ memS _ _ _ _ _ _ HJ2 Hag).
- rewrite Hfr2. exact Hfrs.
- exact (mle_station MT _ _ _ _ _ MLAWS Hmo Hmle).
- unfold GI_K6. exists bb, bf.
  split.
  { unfold p_cut. split.
    { unfold pe_body. cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr mkst ms_regs].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|]. split; [reflexivity|].
      split; [|split; [exact T1 | split; [exact T2 | split; [exact T3 | split; [exact Hlen | exact T4]]]]].
      unfold pregs. cbn [ms_regs mkst].
      split; [transitivity (getr (ms_regs ms) 2); [exact (P 2 ltac:(unfold acallee_saved; lia)) | rewrite Q2, E2; exact Rsp]|].
      split; [transitivity (getr (ms_regs ms) 8); [exact (P 8 ltac:(unfold acallee_saved; lia)) | rewrite Q8, E8; exact Rs0]|].
      split; [transitivity (getr (ms_regs ms) 9); [exact (P 9 ltac:(unfold acallee_saved; lia)) | rewrite Q9, E9; exact Rs1]|].
      split; [transitivity (getr (ms_regs ms) 27); [exact (P 27 ltac:(unfold acallee_saved; lia)) | rewrite Q27, E27; exact Rs11]|].
      split; [transitivity (getr (ms_regs ms) 3); [exact (P 3 ltac:(unfold acallee_saved; lia)) | rewrite Q3, E3; exact Rgp]|].
      transitivity (getr (ms_regs ms) 4); [exact (P 4 ltac:(unfold acallee_saved; lia)) | rewrite Q4, E4; exact Rtp]. }
    split; [unfold EV_CLOSE; lia|]. split; [unfold PA_K6; lia|].
    split.
    { assert (HP' : Permutation ((hh, SRC_FILE_BLOCK) :: ablocks B ly2 S2)
        ((ablocks B (c_ly cx) (c_S cx) ++ [(bb, p_nF cx)]) ++ (hh, SRC_FILE_BLOCK) :: [(bf, p_bn cx)])).
      { eapply Permutation_trans; [exact (Permutation_sym HPm)|]. eapply Permutation_trans; [exact Hperm|].
        first [rewrite <- app_assoc | rewrite app_assoc]; cbn [app]; apply Permutation_refl. }
      pose proof (Permutation_app_inv [] (ablocks B ly2 S2) (ablocks B (c_ly cx) (c_S cx) ++ [(bb, p_nF cx)])
        [(bf, p_bn cx)] (hh, SRC_FILE_BLOCK) HP') as Hq.
      cbn [app] in Hq. first [rewrite <- app_assoc in Hq | rewrite app_assoc in Hq]. cbn [app] in Hq. exact Hq. }
    split; [rewrite Hfd2, (proj1 (fs_wvb md3 mat)); exact Hfds|].
    rewrite Hfs2, (proj2 (fs_wvb md3 mat)). exact Hfs. }
  split.
  { unfold p_pspad. cbn [ms_mem mkst]. apply (garr8_frame SEGS _ _ _ _ Hpad).
    intros a Ha. cbn [length Z.of_nat] in Ha. apply (mbyte_of_aview SEGS). rewrite <- HFm.
    pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ hh SRC_FILE_BLOCK PE_CID fp HAR Hhin Hfin) as Dhf.
    unfold zdisjoint in Dhf. cbn [fst snd] in Dhf. rewrite Efa in Dhf. change (fs_frame_bytes PE_CID) with 128 in Dhf.
    change (req_size SRC_FILE_BLOCK) with 1304 in Dhf.
    apply (K4 PE_CID fp a Hfin); [|cbv beta; rewrite Hps in Ha |- *; change (req_size SRC_FILE_BLOCK) with 1304; lia].
    left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite Efa. change (fs_frame_bytes PE_CID) with 128.
    rewrite Hps in Ha. lia. }
  split; [exact Hn26|]. split; [exact Hgood|].
  split; [cbn [ms_regs mkst]; transitivity (getr (ms_regs ms) 19); [exact (P 19 ltac:(unfold acallee_saved; lia)) | rewrite Q19, E19; exact R19]|].
  split; [cbn [ms_regs mkst]; transitivity (getr (ms_regs ms) 20); [exact (P 20 ltac:(unfold acallee_saved; lia)) | rewrite Q20, E20; exact R20]|].
  split; [cbn [ms_regs mkst]; transitivity (getr (ms_regs ms) 21); [exact (P 21 ltac:(unfold acallee_saved; lia)) | rewrite Q21, E21; exact R21]|].
  split; [cbn [ms_regs mkst]; transitivity (getr (ms_regs ms) 22); [exact (P 22 ltac:(unfold acallee_saved; lia)) | rewrite Q22, E22; exact R22]|].
  split; [cbn [ms_regs mkst]; transitivity (getr (ms_regs ms) 23); [exact (P 23 ltac:(unfold acallee_saved; lia)) | rewrite Q23, E23; exact R23]|].
  split; [cbn [ms_regs mkst]; transitivity (getr (ms_regs ms) 26); [exact (P 26 ltac:(unfold acallee_saved; lia)) | rewrite Q26, E26; exact R26]|].
  split; [exact T5|].
  split.
  { unfold p_glob, pval in Hglob |- *. cbn [ms_mem mkst]. destruct Hglob as (Hg2 & Hg4). split.
    - eapply vm_frame_segs; [|exact Hg2]. intros x Hx. apply (mbyte_of_aview SEGS). apply HGkeep, inG_obj2.
      cbn [Z.of_nat] in Hx. lia.
    - eapply vm_frame_segs; [|exact Hg4]. intros x Hx. apply (mbyte_of_aview SEGS). apply HGkeep, inG_obj4.
      cbn [Z.of_nat] in Hx. lia. }
  split; [exact Hcopy2|]. split; [exact Hnull|]. exact Hnone2.
Qed.

(* The head of W: PP_K5 -> PP_KW (at <> |F|) or -> 0x810a0 with want = 0 -> tail_close6 (at = |F|). *)
Lemma tail_W5 : pe_from SK B MT KS POST (GI_K6 B MT KS) -> pe_from SK B MT KS POST (GI_KW B MT KS) ->
  pe_from SK B MT KS POST (GI_K5 B MT KS).
Proof.
intros NEXT6 NEXTW cx fp k acc ly3 S3 W3 ms3 md3 HB HJ0 Hfrs Hmo HG.
destruct HG as (bb & hh & bf & p & HPC & Hpad & Hn26 & Hgood & (Hp24 & HpF) & Hkind & R12 & R18 & R19 & R21 & R22 &
  R26 & Hslots & Hglob & Hreader).
pose proof HPC as ((Hpc & Hresv & Hsvc & Hrom & Hfrg & Hfcsr & Hregs & Hsaved & Hhdr & Hsh & Hlen & Hin) & Hk & Hacc & Hperm &
  Hfds & Hfs).
pose proof (tail_geo cx HB) as (Hal & Hs1m & Hs1b & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
unfold LLVMF_STK in Hslo, Hbot.
pose proof HB as ((HAR0 & Hrok & Hra4 & Hgp0 & Htp0 & _) & HraL & _ & _ & _ & _ & _ & Hev & Hlive & _ & _ & _ & _ & _ &
  _ & _ & Hmok & Hneed & HGX & HGD & _ & _ & Hftr).
pose proof HJ0 as HJ0'. destruct (gx_open _ _ _ _ _ _ _ _ HJ0') as (memS & HJ & Hag). clear HJ0'.
pose proof HJ as (HAR & Hly & _).
destruct Hregs as (Rsp & Rs0 & Rs1 & Rs11 & Rgp & Rtp).
pose proof Hslots as (S_psp & S_glen & S_d & S_sh & S_f & S_fk & S_tsp). unfold pslot, PS_PSP, PS_GLEN, PS_F, PS_FK in *.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (p_sizes cx) as (Hsz1 & Hsz2 & Hsz3).
destruct (lay_eqs _ _ _ Hly) as (EF & Etop & Eslo & Eshi).
assert (Efa : frame_addr ly3 PE_CID fp = pF cx fp) by (unfold pF, frame_addr; rewrite EF; reflexivity).
assert (Hfin : In (PE_CID, fp) (frames S3)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 PE_CID fp HAR Hfin) as (Hf4096 & Hfceil & Hfapp).
rewrite Efa in Hf4096, Hfceil, Hfapp. change (fs_frame_bytes PE_CID) with 128 in Hfceil, Hfapp.
pose proof (pa_obj_img 4 ltac:(lia)) as O4. unfold pcap_img_end, YImgTop.IMG_TOP in O4.
assert (Hps : pPS cx fp = pF cx fp + 32) by reflexivity.
assert (HG4 : val_mem SEGS (mrestrict (w_H W3) (ms_mem ms3)) (pa_val (A_HI 8) + PE_GLEN_LO) 8 (p_nF cx))
  by (rewrite HGLEN; exact (proj2 Hglob)).
remember (Eimg (Ereg (ms_regs ms3) [Z_to_bv 64 (pa_val (A_HI 8)); Z_to_bv 64 (pF cx fp); Z_to_bv 64 (pPS cx fp);
  Z_to_bv 64 (p_nF cx)])) as E eqn:HEdef.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg (ms_regs ms3) [Z_to_bv 64 (pa_val (A_HI 8));
  Z_to_bv 64 (pF cx fp); Z_to_bv 64 (pPS cx fp); Z_to_bv 64 (p_nF cx)]) n)
  by (intros n Hn; subst E; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr (ms_regs ms3) 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr (ms_regs ms3) 3) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr (ms_regs ms3) 4) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 4 4%bv eq_refl)).
assert (E8 : ew E 8 = getr (ms_regs ms3) 8) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 8 8%bv eq_refl)).
assert (E9 : ew E 9 = getr (ms_regs ms3) 9) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 9 9%bv eq_refl)).
assert (E12 : ew E 12 = getr (ms_regs ms3) 12) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 12 12%bv eq_refl)).
assert (E18 : ew E 18 = getr (ms_regs ms3) 18) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 18 18%bv eq_refl)).
assert (E19 : ew E 19 = getr (ms_regs ms3) 19) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 19 19%bv eq_refl)).
assert (E21 : ew E 21 = getr (ms_regs ms3) 21) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 21 21%bv eq_refl)).
assert (E22 : ew E 22 = getr (ms_regs ms3) 22) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 22 22%bv eq_refl)).
assert (E26 : ew E 26 = getr (ms_regs ms3) 26) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 26 26%bv eq_refl)).
assert (E27 : ew E 27 = getr (ms_regs ms3) 27) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 27 27%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 (pa_val (A_HI 8))) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (pF cx fp)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (pPS cx fp)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 (p_nF cx)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 3)).
assert (Hhi8 : 0 <= pa_val (A_HI 8) < 2 ^ 64) by (pose proof (pa_val_range (A_HI 8)); lia).
assert (U9 : bv_unsigned (ew E 9) = c_sp1 cx) by (rewrite E9, Rs1; unfold w64; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = pa_val (A_HI 8)) by (rewrite E32; apply unsigned_lit_small; lia).
assert (HS : st_ok_pi SEGS VAL E (mkSS PP_K5 sr_atoms w5_rs None nofacts) (restrict (w_H W3) ms3)).
{ rewrite HEdef. rewrite HEdef in U9, U32, E32, E33, E34, E35.
  apply entryR; try assumption; [vm_compute; reflexivity | | | split; [exact I | split; exact I]].
  - unfold w5_rs. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      * apply (chunk_saved _ _ _ _ _ _ _ _ _ E33 (eq_sym (unsigned_lit_small (pF cx fp) ltac:(lia))) (Z.eq_refl _)). exact S_f.
      * apply (chunk_saved _ _ _ _ _ _ _ _ _ E33 (eq_sym (unsigned_lit_small (pF cx fp) ltac:(lia))) (Z.eq_refl _)). exact S_fk.
      * apply (chunk_saved _ _ _ _ _ _ _ _ _ E32 (eq_sym (unsigned_lit_small (pa_val (A_HI 8)) Hhi8)) (Z.eq_refl _)). exact S_glen.
      * apply (chunk_saved _ _ _ _ _ _ _ _ _ E34 (eq_sym (unsigned_lit_small (pPS cx fp) ltac:(lia))) (Z.eq_refl _)). exact S_psp.
    + rewrite U32. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS _ _ (pa_val (A_HI 8)) PE_GLEN_LO 8 (SOff 35 0) (p_nF cx));
        [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact HG4].
  - apply pairwise_disjoint_of_extents. unfold w5_rs, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U32.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. rewrite HGLEN. repeat split; lia. }
clear HEdef EL.
assert (SHOK : sh_ok SEGS TBx [] E (mrestrict (w_H W3) (ms_mem ms3))) by constructor.
assert (Hro : forall r, In r w5_rs -> YP09.r_whi r <= YP09.r_wlo r)
  by (intros r Hr; unfold w5_rs in Hr; cbn [In] in Hr; destruct Hr as [<- | [<- | []]]; cbn; lia).
(* 0x8107c addi a0,zero,-1 ... up to blt a2,a0 0x81080 *)
paj_run_tok RUN HS HJ SHOK TBspan;
  [ unfold w5_rs; cbn [ss_mem]; apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_nil |].
assert (HFm1 : ms_mem ms = ms_mem ms3) by exact (frame_of_ro E w5_rs _ _ Hro HF).
clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK TBspan.
{ exfalso. rewrite branch_lt_U in Hc. cbn [sv_denot] in Hc. rewrite E12, R12 in Hc.
  destruct (res_ge cx (p_q cx p) Hkind) as [H0 | H0]; rewrite H0 in Hc; vm_compute in Hc; discriminate Hc. }
clear Hc.
(* the four slot loads, ld a1,0x618(a0) (g_file_len), up to bne s2,a1 0x81098 *)
paj_run_tok RUN HS HJ SHOK TBspan;
  [ unfold w5_rs; cbn [ss_mem]; apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_nil |].
assert (HFm2 : ms_mem ms0 = ms_mem ms3) by (rewrite (frame_of_ro E w5_rs _ _ Hro HF); exact HFm1).
clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK TBspan.
- (* at <> |F|: 0x81218 lui a0,0x10; addiw a4,a0,-0x100; addi a3,zero,-1; at PP_KW *)
  rewrite branch_ne_U in Hc.
  rewrite (U_atom E 18 p) in Hc by (first [rewrite E18, R18; reflexivity | lia]).
  rewrite (U_atom E 35 (p_nF cx)) in Hc by (first [exact E35 | lia]).
  assert (Hne : p <> p_nF cx).
  { intros Hp. rewrite Hp, Z.eqb_refl in Hc. discriminate Hc. }
  clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK TBspan PP_KW;
    [ unfold w5_rs; cbn [ss_mem]; apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_nil |].
  assert (HFm : ms_mem ms1 = ms_mem ms3) by (rewrite (frame_of_ro E w5_rs _ _ Hro HF); exact HFm2).
  pmkst HS.
  prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8.
  prreg HS (9%bv : bv 5) Q9. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12. prreg HS (13%bv : bv 5) Q13.
  prreg HS (14%bv : bv 5) Q14. prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19. prreg HS (20%bv : bv 5) Q20.
  prreg HS (21%bv : bv 5) Q21. prreg HS (22%bv : bv 5) Q22. prreg HS (23%bv : bv 5) Q23. prreg HS (26%bv : bv 5) Q26.
  prreg HS (27%bv : bv 5) Q27. prreg HS (29%bv : bv 5) Q29.
  eapply (NEXTW cx fp k acc ly3 S3 W3 (mkst (ms_regs ms1) (Z_to_bv 64 (BASE + PP_KW)) (ms_mem ms1) (seg_rom SEGS))
    _ HB).
  + exact (gx_pack0 cx _ memS _ _ _ _ _ _ HJ Hag).
  + exact Hfrs.
  + exact Hmo.
  + exists bb, hh, bf, p, p. cbn [ms_regs ms_mem mkst].
    split.
    { split.
      { unfold pe_body. cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr mkst ms_regs ms_mem].
        rewrite HFm.
        split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
        split; [reflexivity|]. split; [reflexivity|].
        split; [|split; [exact Hsaved | split; [exact Hhdr | split; [exact Hsh | split; [exact Hlen | exact Hin]]]]].
        unfold pregs. cbn [ms_regs mkst]. rewrite Q2, Q8, Q9, Q27, Q3, Q4, E2, E8, E9, E27, E3, E4.
        repeat split; assumption. }
      split; [exact Hk|]. split; [exact Hacc|]. split; [exact Hperm|].
      split; [rewrite !(proj1 (fs_wvb _ _)); exact Hfds | rewrite !(proj2 (fs_wvb _ _)); exact Hfs]. }
    split; [unfold p_pspad; rewrite HFm; exact Hpad|].
    split; [exact Hn26|]. split; [exact Hgood|]. split; [lia|]. split; [lia|]. split; [exact Hne|].
    split; [exact (m_psn_q_skips (p_sw cx) (p_F cx) (p_cap cx) p ltac:(lia))|]. split; [exact Hkind|].
    split; [rewrite Q11, E35; reflexivity|].
    split; [rewrite Q12, E12; exact R12|].
    split; [rewrite Q13; apply bv_eq; reflexivity|].
    split; [rewrite Q14; apply bv_eq; reflexivity|].
    split; [rewrite Q18, E18; exact R18|].
    split; [rewrite Q19, E19; exact R19|].
    split; [rewrite Q20, E33; reflexivity|].
    split; [rewrite Q21, E21; exact R21|].
    split; [rewrite Q22, E22; exact R22|].
    split; [rewrite Q23, E33; reflexivity|].
    split; [rewrite Q26, E26; exact R26|].
    split; [rewrite Q29, E34; reflexivity|].
    split; [unfold pslots, pslot; rewrite HFm; exact Hslots|].
    split; [unfold p_glob, pval; rewrite HFm; exact Hglob|].
    unfold p_reader, p_psopen, pval in Hreader |- *. rewrite HFm. exact Hreader.
- (* at = |F|: 0x8109c mv a3,zero; at 0x810a0 with want = 0 = the model's answer at |F| *)
  rewrite branch_ne_U in Hc.
  rewrite (U_atom E 18 p) in Hc by (first [rewrite E18, R18; reflexivity | lia]).
  rewrite (U_atom E 35 (p_nF cx)) in Hc by (first [exact E35 | lia]).
  assert (Heq : p = p_nF cx).
  { destruct (Z.eqb_spec p (p_nF cx)) as [E0|E0]; [exact E0 | discriminate Hc]. }
  clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK TBspan PP_W0;
    [ unfold w5_rs; cbn [ss_mem]; apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_nil |].
  assert (HFm : ms_mem ms1 = ms_mem ms3) by (rewrite (frame_of_ro E w5_rs _ _ Hro HF); exact HFm2).
  pmkst HS.
  prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8.
  prreg HS (9%bv : bv 5) Q9. prreg HS (12%bv : bv 5) Q12. prreg HS (13%bv : bv 5) Q13.
  prreg HS (19%bv : bv 5) Q19. prreg HS (20%bv : bv 5) Q20.
  prreg HS (21%bv : bv 5) Q21. prreg HS (22%bv : bv 5) Q22. prreg HS (23%bv : bv 5) Q23. prreg HS (26%bv : bv 5) Q26.
  prreg HS (27%bv : bv 5) Q27. prreg HS (29%bv : bv 5) Q29.
  subst p.
  apply (tail_close6 NEXT6 cx fp k acc ly3 S3 W3 (mkst (ms_regs ms1) (Z_to_bv 64 (BASE + PP_W0)) (ms_mem ms1) (seg_rom SEGS))
    _ bb hh bf (p_nF cx) HB (gx_pack0 cx _ memS _ _ _ _ _ _ HJ Hag) Hfrs Hmo); cbn [ms_regs ms_mem mkst].
  + split.
    { unfold pe_body. cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr mkst ms_regs ms_mem].
      rewrite HFm.
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|]. split; [reflexivity|].
      split; [|split; [exact Hsaved | split; [exact Hhdr | split; [exact Hsh | split; [exact Hlen | exact Hin]]]]].
      unfold pregs. cbn [ms_regs mkst]. rewrite Q2, Q8, Q9, Q27, Q3, Q4, E2, E8, E9, E27, E3, E4.
      repeat split; assumption. }
    split; [exact Hk|]. split; [exact Hacc|]. split; [exact Hperm|].
    split; [rewrite !(proj1 (fs_wvb _ _)); exact Hfds | rewrite !(proj2 (fs_wvb _ _)); exact Hfs].
  + unfold p_pspad. rewrite HFm. exact Hpad.
  + exact Hn26.
  + exact Hgood.
  + rewrite Q12, E12. exact R12.
  + rewrite Q13, res_at_end. reflexivity.
  + rewrite Q19, E19. exact R19.
  + rewrite Q20, E33. reflexivity.
  + rewrite Q21, E21. exact R21.
  + rewrite Q22, E22. exact R22.
  + rewrite Q23, E33. reflexivity.
  + rewrite Q26, E26. exact R26.
  + rewrite Q29, E34. reflexivity.
  + unfold pslots, pslot. rewrite HFm. exact Hslots.
  + unfold p_glob, pval. rewrite HFm. exact Hglob.
  + unfold p_reader, p_psopen, pval in Hreader |- *. rewrite HFm. exact Hreader.
Qed.

(* ---- W (second half): the end-of-walk check loop, PP_KW 0x81224 .. 0x812fc ----------------------------------
   One pass from e (e < |F|): 0x81228 bltu |F|, e+16 (to 0x810a0, want = -1: KCutH); s2 := b + e (0x8122c); the
   four shadow-checked byte loads of b+e+8..11 (0x81230..0x8128c; the copy holds them since e + 16 <= |F|); the
   word in the reader's byte order (0x81290..0x812d0, ps->sw); 0x812d4 beqz (length 0: e += 16, KEmpty);
   zero-extension; 0x812e4 bgeu cap, length (fits the cap: to 0x81330, want = length or -1 if it runs past |F|:
   KFit is refuted by GI_KW's kind (p_q p) <> KFit, so KCutFit and -1); else 0x812ec beqz d (cap 0: KBig0, -1),
   0x812f0 bltu |F|, e+16+length (KCutBig, -1), else e += 16 + length (KBig). The loop goes on while e <> |F|
   (0x812f8) and ends with want = 0 at |F| (0x8109c, KEnd). Every exit reaches 0x810a0 with want = the reader's
   answer, so tail_close6 ends it. The pass is cut at 0x81230 (s2 = b + e is one atom there, so the shadow checks
   are decided by one shent over the copy), at 0x812d4 (the word, sign-extended) and at 0x812e0 (the length). *)

Definition PP_LB : Z := Eval compute in ((Symbols.Asan.s_LLVMFuzzerTestOneInput + 0xa68) - Symbols.Asan.s_libreac_fuzz_fopen)%Z.   (* 0x81230 *)
Definition PP_LD : Z := Eval compute in ((Symbols.Asan.s_LLVMFuzzerTestOneInput + 0xb0c) - Symbols.Asan.s_libreac_fuzz_fopen)%Z.   (* 0x812d4 *)
Definition PP_LC : Z := Eval compute in ((Symbols.Asan.s_LLVMFuzzerTestOneInput + 0xb18) - Symbols.Asan.s_libreac_fuzz_fopen)%Z.   (* 0x812e0 *)

Definition p_incl (cx : ecx) (e : Z) : Z := PSN.incl (p_sw cx) (p_F cx) e.

(* What every point of the loop, and 0x810a0, carries (a1, a3, a0, a4, a5, s2 are stated per point). *)
Definition LW0 (pc : Z) (cx : ecx) (fp k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) (b h buf p : Z) : Prop :=
  p_cut B cx fp pc PSH_ts k 3 acc (PA_K3 MT cx) [(b, p_nF cx); (h, SRC_FILE_BLOCK); (buf, p_bn cx)] ly3 S3 W3 ms3 md3 /\
  p_pspad cx fp W3 ms3 /\ c_n cx < 2 ^ 26 /\ p_good cx = true /\
  getr (ms_regs ms3) 12 = w64 (p_res cx (p_q cx p)) /\ getr (ms_regs ms3) 19 = w64 b /\
  getr (ms_regs ms3) 20 = w64 (pF cx fp) /\ getr (ms_regs ms3) 21 = w64 (p_cap cx) /\
  getr (ms_regs ms3) 22 = w64 buf /\ getr (ms_regs ms3) 23 = w64 (pF cx fp) /\
  getr (ms_regs ms3) 26 = w64 (p_first cx) /\ getr (ms_regs ms3) 29 = w64 (pPS cx fp) /\
  pslots cx fp W3 ms3 /\ p_glob cx W3 ms3 b /\ p_reader KS cx fp W3 ms3 b h buf p.

Definition LW (pc : Z) (cx : ecx) (fp k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) (b h buf p e : Z) : Prop :=
  LW0 pc cx fp k acc ly3 S3 W3 ms3 md3 b h buf p /\
  24 <= p <= e /\ e < p_nF cx /\ p_skips cx e (p_q cx p) /\ p_kind cx (p_q cx p) <> PSN.KFit /\
  getr (ms_regs ms3) 11 = w64 (p_nF cx) /\ getr (ms_regs ms3) 14 = w64 0xff00.

Definition GI_KWn (n : nat) (cx : ecx) (fp k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists b h buf p e, LW PP_KW cx fp k acc ly3 S3 W3 ms3 md3 b h buf p e /\
  getr (ms_regs ms3) 18 = w64 e /\ getr (ms_regs ms3) 13 = w64 (-1) /\ p_nF cx - e < Z.of_nat n.

Definition GI_LB (n : nat) (cx : ecx) (fp k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists b h buf p e, LW PP_LB cx fp k acc ly3 S3 W3 ms3 md3 b h buf p e /\
  getr (ms_regs ms3) 18 = w64 (e + b) /\ getr (ms_regs ms3) 15 = w64 (e + 16) /\
  getr (ms_regs ms3) 13 = w64 (-1) /\ e + 16 <= p_nF cx /\ p_nF cx - e < Z.of_nat n.

Definition GI_LD (n : nat) (cx : ecx) (fp k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists b h buf p e, LW PP_LD cx fp k acc ly3 S3 W3 ms3 md3 b h buf p e /\
  getr (ms_regs ms3) 10 = w64 (sx32u (p_incl cx e)) /\ getr (ms_regs ms3) 15 = w64 (e + 16) /\
  getr (ms_regs ms3) 13 = w64 (-1) /\ e + 16 <= p_nF cx /\ p_nF cx - e < Z.of_nat n.

Definition GI_LC (n : nat) (cx : ecx) (fp k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists b h buf p e, LW PP_LC cx fp k acc ly3 S3 W3 ms3 md3 b h buf p e /\
  getr (ms_regs ms3) 10 = w64 (p_incl cx e) /\ p_incl cx e <> 0 /\ getr (ms_regs ms3) 15 = w64 (e + 16) /\
  getr (ms_regs ms3) 13 = w64 (-1) /\ e + 16 <= p_nF cx /\ p_nF cx - e < Z.of_nat n.

(* The loop writes no memory: LW0 moves to any later point with the same memory and the registers it states. *)
Lemma LW0_move : forall pc pc' cx fp k acc ly3 S3 W3 ms3 md3 ms md b h buf p,
  LW0 pc cx fp k acc ly3 S3 W3 ms3 md3 b h buf p ->
  ms_mem ms = ms_mem ms3 -> ms_pc_val ms = w64 (BASE + pc') -> ms_resv ms = None -> ms_svc_pending ms = None ->
  ms_rom ms = seg_rom SEGS -> ms_fregs ms = fp_regs -> ms_fcsr ms = fp_csr ->
  getr (ms_regs ms) 2 = getr (ms_regs ms3) 2 -> getr (ms_regs ms) 3 = getr (ms_regs ms3) 3 ->
  getr (ms_regs ms) 4 = getr (ms_regs ms3) 4 -> getr (ms_regs ms) 8 = getr (ms_regs ms3) 8 ->
  getr (ms_regs ms) 9 = getr (ms_regs ms3) 9 -> getr (ms_regs ms) 27 = getr (ms_regs ms3) 27 ->
  getr (ms_regs ms) 12 = getr (ms_regs ms3) 12 -> getr (ms_regs ms) 19 = getr (ms_regs ms3) 19 ->
  getr (ms_regs ms) 20 = getr (ms_regs ms3) 20 -> getr (ms_regs ms) 21 = getr (ms_regs ms3) 21 ->
  getr (ms_regs ms) 22 = getr (ms_regs ms3) 22 -> getr (ms_regs ms) 23 = getr (ms_regs ms3) 23 ->
  getr (ms_regs ms) 26 = getr (ms_regs ms3) 26 -> getr (ms_regs ms) 29 = getr (ms_regs ms3) 29 ->
  m_fds md = m_fds md3 -> m_fs md = m_fs md3 ->
  LW0 pc' cx fp k acc ly3 S3 W3 ms md b h buf p.
Proof.
  intros pc pc' cx fp k acc ly3 S3 W3 ms3 md3 ms md b h buf p
    (((_ & _ & _ & _ & _ & _ & Hregs & Hsaved & Hhdr & Hsh & Hlen & Hin) & Hk & Hacc & Hperm & Hfds & Hfs) & Hpad & Hn26 &
     Hgood & R12 & R19 & R20 & R21 & R22 & R23 & R26 & R29 & Hslots & Hglob & Hreader)
    HFm Hpc Hresv Hsvc Hrom Hfrg Hfcsr G2 G3 G4 G8 G9 G27 G12 G19 G20 G21 G22 G23 G26 G29 Hfd Hfs'.
  destruct Hregs as (Rsp & Rs0 & Rs1 & Rs11 & Rgp & Rtp).
  split; [|split; [|split; [exact Hn26 | split; [exact Hgood |]]]].
  - split; [|split; [exact Hk | split; [exact Hacc | split; [exact Hperm | split; [rewrite Hfd; exact Hfds |
      rewrite Hfs'; exact Hfs]]]]].
    unfold pe_body, pregs, psaved, pheader, pshadow in *. rewrite HFm.
    split; [exact Hpc|]. split; [exact Hresv|]. split; [exact Hsvc|]. split; [exact Hrom|].
    split; [exact Hfrg|]. split; [exact Hfcsr|].
    split; [rewrite G2, G8, G9, G27, G3, G4; repeat split; assumption|].
    split; [exact Hsaved|]. split; [exact Hhdr|]. split; [exact Hsh|]. split; [exact Hlen | exact Hin].
  - unfold p_pspad in *. rewrite HFm. exact Hpad.
  - rewrite G12, G19, G20, G21, G22, G23, G26, G29.
    repeat (split; [assumption|]).
    split; [unfold pslots, pslot in *; rewrite HFm; exact Hslots|].
    split; [unfold p_glob, pval in *; rewrite HFm; exact Hglob|].
    unfold p_reader, p_psopen, pval in *. rewrite HFm. exact Hreader.
Qed.

Lemma LW_move : forall pc pc' cx fp k acc ly3 S3 W3 ms3 md3 ms md b h buf p e e',
  LW pc cx fp k acc ly3 S3 W3 ms3 md3 b h buf p e ->
  ms_mem ms = ms_mem ms3 -> ms_pc_val ms = w64 (BASE + pc') -> ms_resv ms = None -> ms_svc_pending ms = None ->
  ms_rom ms = seg_rom SEGS -> ms_fregs ms = fp_regs -> ms_fcsr ms = fp_csr ->
  getr (ms_regs ms) 2 = getr (ms_regs ms3) 2 -> getr (ms_regs ms) 3 = getr (ms_regs ms3) 3 ->
  getr (ms_regs ms) 4 = getr (ms_regs ms3) 4 -> getr (ms_regs ms) 8 = getr (ms_regs ms3) 8 ->
  getr (ms_regs ms) 9 = getr (ms_regs ms3) 9 -> getr (ms_regs ms) 27 = getr (ms_regs ms3) 27 ->
  getr (ms_regs ms) 11 = getr (ms_regs ms3) 11 -> getr (ms_regs ms) 12 = getr (ms_regs ms3) 12 ->
  getr (ms_regs ms) 14 = getr (ms_regs ms3) 14 -> getr (ms_regs ms) 19 = getr (ms_regs ms3) 19 ->
  getr (ms_regs ms) 20 = getr (ms_regs ms3) 20 -> getr (ms_regs ms) 21 = getr (ms_regs ms3) 21 ->
  getr (ms_regs ms) 22 = getr (ms_regs ms3) 22 -> getr (ms_regs ms) 23 = getr (ms_regs ms3) 23 ->
  getr (ms_regs ms) 26 = getr (ms_regs ms3) 26 -> getr (ms_regs ms) 29 = getr (ms_regs ms3) 29 ->
  m_fds md = m_fds md3 -> m_fs md = m_fs md3 ->
  e <= e' -> e' < p_nF cx -> p_skips cx e' (p_q cx p) ->
  LW pc' cx fp k acc ly3 S3 W3 ms md b h buf p e'.
Proof.
  intros pc pc' cx fp k acc ly3 S3 W3 ms3 md3 ms md b h buf p e e' (H0 & Hpe & HeF & Hsk & Hkind & R11 & R14)
    HFm Hpc Hresv Hsvc Hrom Hfrg Hfcsr G2 G3 G4 G8 G9 G27 G11 G12 G14 G19 G20 G21 G22 G23 G26 G29 Hfd Hfs' He1 He2 Hsk'.
  split; [exact (LW0_move pc pc' cx fp k acc ly3 S3 W3 ms3 md3 ms md b h buf p H0 HFm Hpc Hresv Hsvc Hrom Hfrg Hfcsr
    G2 G3 G4 G8 G9 G27 G12 G19 G20 G21 G22 G23 G26 G29 Hfd Hfs')|].
  split; [lia|]. split; [exact He2|]. split; [exact Hsk'|]. split; [exact Hkind|].
  rewrite G11, G14. split; assumption.
Qed.

Lemma close_LW : pe_from SK B MT KS POST (GI_K6 B MT KS) ->
  forall cx fp k acc ly3 S3 W3 ms3 md3 b h buf p,
  pe_base SK B MT KS cx ->
  ajournal_gx SEGS B pe_G 0 [] LLVMF_STK (spZ (c_regs cx)) [sink_token] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx)
    (c_md cx) [(PE_CID, fp)] ly3 S3 W3 (ms_mem ms3) md3 k ->
  frames S3 = [(PE_CID, fp)] -> mo_le MT (c_S cx) S3 acc ->
  LW0 PP_W0 cx fp k acc ly3 S3 W3 ms3 md3 b h buf p ->
  getr (ms_regs ms3) 13 = w64 (p_res cx (p_q cx p)) ->
  SRr SEGS W3 (mkCfg ms3 md3) (POST cx).
Proof.
  intros NEXT6 cx fp k acc ly3 S3 W3 ms3 md3 b h buf p HB HJ Hfrs Hmo
    (HPC & Hpad & Hn26 & Hgood & R12 & R19 & R20 & R21 & R22 & R23 & R26 & R29 & Hslots & Hglob & Hreader) R13.
  exact (tail_close6 NEXT6 cx fp k acc ly3 S3 W3 ms3 md3 b h buf p HB HJ Hfrs Hmo HPC Hpad Hn26 Hgood R12 R13 R19 R20 R21
    R22 R23 R26 R29 Hslots Hglob Hreader).
Qed.

(* Discharges `getr (ms_regs ms) r = getr (ms_regs ms3) r` from prreg's Q-fact and the entry's E-fact for r. *)
Ltac kr := match goal with
  | |- getr (ms_regs ?m) ?r = getr (ms_regs ?m3) ?r =>
    match goal with
    | Q : getr (ms_regs m) r = ew ?E ?n |- _ =>
      match goal with En : ew E n = getr (ms_regs m3) r |- _ => rewrite Q, En; reflexivity end
    end
  end.

(* The close of a pass: from LW0 at 0x810a0, with want = the reader's answer. *)
Ltac lw0_close NEXT6 HB Hfrs Hmo HLW0 HFm ms0 HJ Hag memS :=
  eapply (close_LW NEXT6 _ _ _ _ _ _ _ (mkst (ms_regs ms0) (Z_to_bv 64 (BASE + PP_W0)) (ms_mem ms0) (seg_rom SEGS))
    _ _ _ _ _ HB (gx_pack0 _ _ memS _ _ _ _ _ _ HJ Hag) Hfrs Hmo);
  [ apply (LW0_move _ PP_W0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HLW0); cbn [ms_mem ms_pc_val ms_resv
      ms_svc_pending ms_rom ms_fregs ms_fcsr ms_regs mkst]; try reflexivity; try exact HFm; try kr;
      first [rewrite !(proj1 (fs_wvb _ _)); reflexivity | rewrite !(proj2 (fs_wvb _ _)); reflexivity]
  | cbn [ms_regs mkst] ].

(* The kinds of the record at e, once 16 bytes remain. *)
Lemma k_at : forall sw F cap q, 16 <= PSN.flen F - q -> PSN.kind sw F cap q =
  if PSN.incl sw F q =? 0 then PSN.KEmpty
  else if PSN.incl sw F q <=? cap then (if q + 16 + PSN.incl sw F q <=? PSN.flen F then PSN.KFit else PSN.KCutFit)
  else if cap =? 0 then PSN.KBig0 else if q + 16 + PSN.incl sw F q <=? PSN.flen F then PSN.KBig else PSN.KCutBig.
Proof.
  intros sw F cap q H. unfold PSN.kind. rewrite (proj2 (Z.eqb_neq _ _)) by lia. rewrite (proj2 (Z.ltb_ge _ _)) by lia.
  reflexivity.
Qed.

(* A record that stops the chain and is not a fit answers -1. *)
Lemma res_stop : forall cx e Q, p_skips cx e Q -> p_kind cx e <> PSN.KEmpty -> p_kind cx e <> PSN.KBig ->
  p_kind cx e <> PSN.KFit -> p_kind cx e <> PSN.KEnd -> Q = e /\ p_res cx Q = -1.
Proof.
  intros cx e Q Hs K1 K2 K3 K4. pose proof (m_skips_exit _ _ _ _ _ Hs K1 K2) as ->. split; [reflexivity|].
  unfold p_res, PSN.res_of. unfold p_kind in *. destruct (PSN.kind _ _ _ e); congruence.
Qed.

Lemma res_end : forall cx Q, p_skips cx (p_nF cx) Q -> p_res cx Q = 0.
Proof.
  intros cx Q Hs. assert (HK : p_kind cx (p_nF cx) = PSN.KEnd) by apply kind_at_end.
  unfold p_kind in HK. pose proof (m_skips_exit _ _ _ _ _ Hs ltac:(rewrite HK; discriminate) ltac:(rewrite HK; discriminate)) as ->.
  unfold p_res, PSN.res_of. rewrite HK. reflexivity.
Qed.

Lemma kind_KCutH : forall cx e, e < p_nF cx -> p_nF cx - e < 16 -> p_kind cx e = PSN.KCutH.
Proof.
  intros cx e H1 H2. unfold p_kind, PSN.kind. change (PSN.flen (p_F cx)) with (p_nF cx).
  rewrite (proj2 (Z.eqb_neq _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity.
Qed.

(* PP_KW 0x81224: addi a5,s2,16; bltu a1,a5 0x810a0. *)
Lemma segH : forall n, pe_from SK B MT KS POST (GI_K6 B MT KS) -> pe_from SK B MT KS POST (GI_LB n) ->
  pe_from SK B MT KS POST (GI_KWn n).
Proof.
intros n NEXT6 NEXTB cx fp k acc ly3 S3 W3 ms3 md3 HB HJ0 Hfrs Hmo HG.
destruct HG as (bb & hh & bf & p & e & HLW & R18 & R13 & Hmeas).
pose proof HLW as ((HPC & Hpad & Hn26 & Hgood & R12 & R19 & R20 & R21 & R22 & R23 & R26 & R29 & Hslots & Hglob & Hreader) &
  Hpe & HeF & Hsk & Hkind & R11 & R14).
pose proof HLW as (HLW0 & _).
pose proof HPC as ((Hpc & Hresv & Hsvc & Hrom & Hfrg & Hfcsr & Hregs & _) & _).
destruct Hregs as (Rsp & Rs0 & Rs1 & Rs11 & Rgp & Rtp).
pose proof (tail_geo cx HB) as (Hal & Hs1m & Hs1b & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HJ0 as HJ0'. destruct (gx_open _ _ _ _ _ _ _ _ HJ0') as (memS & HJ & Hag). clear HJ0'.
pose proof (p_sizes cx) as (Hsz1 & Hsz2 & Hsz3).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HPC as (_ & _ & _ & Hperm & _).
pose proof HJ as (HAR & _).
assert (Hbin : In (bb, p_nF cx) (ablocks B ly3 S3))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ bb (p_nF cx) HAR Hbin) as (_ & Hb4096 & Hbceil & _).
pose proof (req_size_pos (p_nF cx) ltac:(lia)) as [Hrq1 Hrq2].
pose proof (entry0 PP_KW ms3 W3 Hpc Hresv Hsvc Hrom Hfrg Hfcsr) as HS.
remember (Eimg (Ereg (ms_regs ms3) [])) as E eqn:HEdef.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg (ms_regs ms3) []) n)
  by (intros n0 Hn0; subst E; apply Eimg_low; exact Hn0).
assert (E2 : ew E 2 = getr (ms_regs ms3) 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr (ms_regs ms3) 3) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr (ms_regs ms3) 4) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 4 4%bv eq_refl)).
assert (E8 : ew E 8 = getr (ms_regs ms3) 8) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 8 8%bv eq_refl)).
assert (E9 : ew E 9 = getr (ms_regs ms3) 9) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 9 9%bv eq_refl)).
assert (E11 : ew E 11 = getr (ms_regs ms3) 11) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 11 11%bv eq_refl)).
assert (E12 : ew E 12 = getr (ms_regs ms3) 12) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 12 12%bv eq_refl)).
assert (E13 : ew E 13 = getr (ms_regs ms3) 13) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 13 13%bv eq_refl)).
assert (E14 : ew E 14 = getr (ms_regs ms3) 14) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 14 14%bv eq_refl)).
assert (E18 : ew E 18 = getr (ms_regs ms3) 18) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 18 18%bv eq_refl)).
assert (E19 : ew E 19 = getr (ms_regs ms3) 19) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 19 19%bv eq_refl)).
assert (E20 : ew E 20 = getr (ms_regs ms3) 20) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 20 20%bv eq_refl)).
assert (E21 : ew E 21 = getr (ms_regs ms3) 21) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 21 21%bv eq_refl)).
assert (E22 : ew E 22 = getr (ms_regs ms3) 22) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 22 22%bv eq_refl)).
assert (E23 : ew E 23 = getr (ms_regs ms3) 23) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 23 23%bv eq_refl)).
assert (E26 : ew E 26 = getr (ms_regs ms3) 26) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 26 26%bv eq_refl)).
assert (E27 : ew E 27 = getr (ms_regs ms3) 27) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 27 27%bv eq_refl)).
assert (E29 : ew E 29 = getr (ms_regs ms3) 29) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 29 29%bv eq_refl)).
assert (SHOK : sh_ok SEGS TBx [] E (mrestrict (w_H W3) (ms_mem ms3))) by constructor.
clear HEdef EL.
(* 0x81224 addi a5,s2,16, up to the bltu at 0x81228 *)
paj_run_tok RUN HS HJ SHOK TBspan; [apply awr_ok_nil |].
assert (HFm1 : ms_mem ms = ms_mem ms3) by exact (frame_of_nil _ _ _ HF).
clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK TBspan.
- (* |F| < e + 16: to 0x810a0 with want = -1 *)
  rewrite branch_ltu_U in Hc.
  rewrite (U_atom E 11 (p_nF cx)) in Hc by (first [rewrite E11, R11; reflexivity | lia]).
  rewrite (U_atom_off E 18 e 16) in Hc by (first [rewrite E18, R18; reflexivity | lia]).
  apply Z.ltb_lt in Hc.
  paj_run_to_tok RUNTO HS HJ SHOK TBspan PP_W0; [apply awr_ok_nil |].
  assert (HFm : ms_mem ms0 = ms_mem ms3) by (rewrite (frame_of_nil _ _ _ HF); exact HFm1).
  pmkst HS.
  prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8.
  prreg HS (9%bv : bv 5) Q9. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12. prreg HS (13%bv : bv 5) Q13.
  prreg HS (14%bv : bv 5) Q14. prreg HS (19%bv : bv 5) Q19. prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21.
  prreg HS (22%bv : bv 5) Q22. prreg HS (23%bv : bv 5) Q23. prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
  prreg HS (29%bv : bv 5) Q29.
  lw0_close NEXT6 HB Hfrs Hmo HLW0 HFm ms0 HJ Hag memS. rewrite Q13, E13, R13.
    pose proof (kind_KCutH cx e HeF ltac:(lia)) as HK.
    rewrite (proj2 (res_stop cx e (p_q cx p) Hsk ltac:(rewrite HK; discriminate) ltac:(rewrite HK; discriminate)
      ltac:(rewrite HK; discriminate) ltac:(rewrite HK; discriminate))). reflexivity.
- (* e + 16 <= |F|: 0x8122c add s2,s3,s2, at 0x81230 *)
  rewrite branch_ltu_U in Hc.
  rewrite (U_atom E 11 (p_nF cx)) in Hc by (first [rewrite E11, R11; reflexivity | lia]).
  rewrite (U_atom_off E 18 e 16) in Hc by (first [rewrite E18, R18; reflexivity | lia]).
  apply Z.ltb_ge in Hc.
  paj_run_to_tok RUNTO HS HJ SHOK TBspan PP_LB; [apply awr_ok_nil |].
  assert (HFm : ms_mem ms0 = ms_mem ms3) by (rewrite (frame_of_nil _ _ _ HF); exact HFm1).
  pmkst HS.
  prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8.
  prreg HS (9%bv : bv 5) Q9. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12. prreg HS (13%bv : bv 5) Q13.
  prreg HS (14%bv : bv 5) Q14. prreg HS (15%bv : bv 5) Q15. prreg HS (18%bv : bv 5) Q18.
  prreg HS (19%bv : bv 5) Q19. prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21.
  prreg HS (22%bv : bv 5) Q22. prreg HS (23%bv : bv 5) Q23. prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
  prreg HS (29%bv : bv 5) Q29.
  pose proof Hreader as (Hsrc & _). destruct Hsrc as (Wsrc & cpos & fl & mdd & _ & _ & _ & _ & Hbn & _).
  unfold p_C in Hbn. rewrite length_map in Hbn. fold (p_nF cx) in Hbn.
  apply (NEXTB cx fp k acc ly3 S3 W3 (mkst (ms_regs ms0) (Z_to_bv 64 (BASE + PP_LB)) (ms_mem ms0) (seg_rom SEGS))
    _ HB (gx_pack0 cx _ memS _ _ _ _ _ _ HJ Hag) Hfrs Hmo).
  exists bb, hh, bf, p, e. cbn [ms_regs mkst].
  split; [|split; [|split; [|split; [|split]]]].
  + apply (LW_move PP_KW PP_LB cx fp k acc ly3 S3 W3 ms3 md3 _ _ bb hh bf p e e HLW); cbn [ms_mem ms_pc_val ms_resv
      ms_svc_pending ms_rom ms_fregs ms_fcsr ms_regs mkst]; try reflexivity; try exact HFm; try kr; try lia;
      try exact Hsk; first [rewrite !(proj1 (fs_wvb _ _)); reflexivity | rewrite !(proj2 (fs_wvb _ _)); reflexivity].
  + assert (Hd : alu64 ALU_ADD (ew E 18) (ew E 19) = sv_denot E (SAlu ALU_ADD (SOff 18 0) (SOff 19 0)))
      by (cbn [sv_denot]; rewrite !Z.add_0_r, !Z_to_bv_bv_unsigned; reflexivity).
    rewrite Q18, Hd, (denot_lit_U E). unfold w64. f_equal. rewrite U_SAlu. cbn [zalu_raw].
    rewrite (U_atom E 18 e) by (first [rewrite E18, R18; reflexivity | lia]).
    rewrite (U_atom E 19 bb) by (first [rewrite E19, R19; reflexivity | lia]).
    apply zcanon_id. unfold M64. lia.
  + rewrite Q15, E18, R18. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
  + rewrite Q13, E13. exact R13.
  + lia.
  + exact Hmeas.
Qed.

Lemma m_incl_lt : forall sw F q, PSN.incl sw F q < 2 ^ 32.
Proof.
  intros sw F q. unfold PSN.incl, PSN.hw, PSN.w32le.
  pose proof (m_fb_range F (q + 8)). pose proof (m_fb_range F (q + 8 + 1)).
  pose proof (m_fb_range F (q + 8 + 2)). pose proof (m_fb_range F (q + 8 + 3)). destruct sw; lia.
Qed.

Lemma lor_ones64 : forall c, 0 <= c < 2 ^ 64 -> Z.lor (2 ^ 64 - 1) c = 2 ^ 64 - 1.
Proof.
  intros c Hc. replace (2 ^ 64 - 1) with (Z.ones 64) by reflexivity. apply Z.bits_inj'. intros i Hi.
  rewrite Z.lor_spec. destruct (Z.ltb_spec i 64).
  - rewrite Z.ones_spec_low by lia. reflexivity.
  - rewrite Z.ones_spec_high by lia. rewrite <- (Z.mod_small c (2 ^ 64)) by lia.
    rewrite Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma U_add2 : forall E n m x y, ew E n = Z_to_bv 64 x -> ew E m = Z_to_bv 64 y -> 0 <= x -> 0 <= y -> x + y < 2 ^ 64 ->
  U E (SAlu ALU_ADD (SOff n 0) (SOff m 0)) = x + y.
Proof.
  intros E n m x y Hn Hm Hx Hy Hs. rewrite U_SAlu. cbn [zalu_raw].
  rewrite (U_atom E n x Hn), (U_atom E m y Hm) by lia. apply zcanon_id. unfold M64. lia.
Qed.

Definition lc_rs : smem := [ YP09.mkRegion (Some 9%nat) 32 40 40 40 [YP09.mkChunk 32 (CVal 8 (SOff 32 0))] ].
Definition a3_fit : sv :=
  SAlu ALU_OR (SAlu ALU_SUB (SLit 0) (SAlu ALU_SLTU (SOff 11 0) (SAlu ALU_ADD (SOff 10 0) (SOff 15 0)))) (SOff 10 0).

(* 0x812e0 add a5,a5,a0; bgeu s5,a0 0x81330 (fits the cap: a3 := (|F| < e+16+len ? -1 : 0) | len; j 0x810a0);
   ld a0,0x20(s1) (d); beqz a0 0x810a0; bltu a1,a5 0x810a0; mv s2,a5; bne a5,a1 0x81224; j 0x8109c. *)
Lemma segC : forall n, pe_from SK B MT KS POST (GI_K6 B MT KS) -> pe_from SK B MT KS POST (GI_KWn n) ->
  pe_from SK B MT KS POST (GI_LC (S n)).
Proof.
intros n NEXT6 IH cx fp k acc ly3 S3 W3 ms3 md3 HB HJ0 Hfrs Hmo HG.
destruct HG as (bb & hh & bf & p & e & HLW & R10 & Hc0 & R15 & R13 & HeF16 & Hmeas).
pose proof HLW as ((HPC & Hpad & Hn26 & Hgood & R12 & R19 & R20 & R21 & R22 & R23 & R26 & R29 & Hslots & Hglob & Hreader) &
  Hpe & HeF & Hsk & Hkind & R11 & R14).
pose proof HLW as (HLW0 & _).
pose proof HPC as ((Hpc & Hresv & Hsvc & Hrom & Hfrg & Hfcsr & Hregs & _) & _).
destruct Hregs as (Rsp & Rs0 & Rs1 & Rs11 & Rgp & Rtp).
pose proof (tail_geo cx HB) as (Hal & Hs1m & Hs1b & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HJ0 as HJ0'. destruct (gx_open _ _ _ _ _ _ _ _ HJ0') as (memS & HJ & Hag). clear HJ0'.
pose proof (p_d_range cx) as Hd. pose proof (p_sizes cx) as (Hsz1 & Hsz2 & Hsz3).
unfold LLVMF_STK in Hslo, Hbot. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (m_incl_nonneg (p_sw cx) (p_F cx) e) as Hc1. pose proof (m_incl_lt (p_sw cx) (p_F cx) e) as Hc2.
fold (p_incl cx e) in Hc1, Hc2.
set (c := p_incl cx e) in *.
pose proof Hslots as (_ & _ & S_d & _). unfold pslot, PS_D in S_d. fold (p_d cx) in S_d.
assert (HK0 : p_kind cx e = PSN.kind (p_sw cx) (p_F cx) (p_cap cx) e) by reflexivity.
rewrite k_at in HK0 by (change (PSN.flen (p_F cx)) with (p_nF cx); lia).
fold (p_incl cx e) in HK0. fold c in HK0. change (PSN.flen (p_F cx)) with (p_nF cx) in HK0.
rewrite (proj2 (Z.eqb_neq c 0) Hc0) in HK0.
remember (Eimg (Ereg (ms_regs ms3) [Z_to_bv 64 (p_d cx)])) as E eqn:HEdef.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg (ms_regs ms3) [Z_to_bv 64 (p_d cx)]) n)
  by (intros n0 Hn0; subst E; apply Eimg_low; exact Hn0).
assert (E2 : ew E 2 = getr (ms_regs ms3) 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr (ms_regs ms3) 3) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr (ms_regs ms3) 4) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 4 4%bv eq_refl)).
assert (E8 : ew E 8 = getr (ms_regs ms3) 8) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 8 8%bv eq_refl)).
assert (E9 : ew E 9 = getr (ms_regs ms3) 9) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 9 9%bv eq_refl)).
assert (E10 : ew E 10 = getr (ms_regs ms3) 10) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 10 10%bv eq_refl)).
assert (E11 : ew E 11 = getr (ms_regs ms3) 11) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 11 11%bv eq_refl)).
assert (E12 : ew E 12 = getr (ms_regs ms3) 12) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 12 12%bv eq_refl)).
assert (E13 : ew E 13 = getr (ms_regs ms3) 13) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 13 13%bv eq_refl)).
assert (E14 : ew E 14 = getr (ms_regs ms3) 14) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 14 14%bv eq_refl)).
assert (E15 : ew E 15 = getr (ms_regs ms3) 15) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 15 15%bv eq_refl)).
assert (E19 : ew E 19 = getr (ms_regs ms3) 19) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 19 19%bv eq_refl)).
assert (E20 : ew E 20 = getr (ms_regs ms3) 20) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 20 20%bv eq_refl)).
assert (E21 : ew E 21 = getr (ms_regs ms3) 21) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 21 21%bv eq_refl)).
assert (E22 : ew E 22 = getr (ms_regs ms3) 22) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 22 22%bv eq_refl)).
assert (E23 : ew E 23 = getr (ms_regs ms3) 23) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 23 23%bv eq_refl)).
assert (E26 : ew E 26 = getr (ms_regs ms3) 26) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 26 26%bv eq_refl)).
assert (E27 : ew E 27 = getr (ms_regs ms3) 27) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 27 27%bv eq_refl)).
assert (E29 : ew E 29 = getr (ms_regs ms3) 29) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 29 29%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 (p_d cx)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 0)).
assert (V10 : ew E 10 = Z_to_bv 64 c) by (rewrite E10, R10; reflexivity).
assert (V11 : ew E 11 = Z_to_bv 64 (p_nF cx)) by (rewrite E11, R11; reflexivity).
assert (V15 : ew E 15 = Z_to_bv 64 (e + 16)) by (rewrite E15, R15; reflexivity).
assert (V21 : ew E 21 = Z_to_bv 64 (p_cap cx)) by (rewrite E21, R21; reflexivity).
assert (U9 : bv_unsigned (ew E 9) = c_sp1 cx) by (rewrite E9, Rs1; unfold w64; apply unsigned_lit_small; lia).
assert (HS : st_ok_pi SEGS VAL E (mkSS PP_LC sr_atoms lc_rs None nofacts) (restrict (w_H W3) ms3)).
{ rewrite HEdef. rewrite HEdef in U9, E32.
  apply entryR; try assumption; [vm_compute; reflexivity | | | split; [exact I | split; exact I]].
  - unfold lc_rs. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_saved _ _ _ _ _ _ _ _ _ E32 (eq_sym (unsigned_lit_small (p_d cx) ltac:(lia))) (Z.eq_refl _)). exact S_d.
  - apply pairwise_disjoint_of_extents. unfold lc_rs, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val zpairwise_disjoint zall_disjoint]. repeat split. }
clear HEdef EL.
assert (SHOK : sh_ok SEGS TBx [] E (mrestrict (w_H W3) (ms_mem ms3))) by constructor.
assert (Hro : forall r, In r lc_rs -> YP09.r_whi r <= YP09.r_wlo r)
  by (intros r Hr; unfold lc_rs in Hr; cbn [In] in Hr; destruct Hr as [<- | []]; cbn; lia).
assert (UA : U E (SAlu ALU_ADD (SOff 10 0) (SOff 15 0)) = c + (e + 16)) by (apply U_add2; [exact V10 | exact V15 | lia | lia | lia]).
(* 0x812e0 add a5,a5,a0, up to bgeu s5,a0 *)
paj_run_tok RUN HS HJ SHOK TBspan; [unfold lc_rs; cbn [ss_mem]; apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_nil |].
assert (HFm1 : ms_mem ms = ms_mem ms3) by exact (frame_of_ro E lc_rs _ _ Hro HF).
clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK TBspan.
- (* len <= cap: 0x81330..0x8133c, to 0x810a0 *)
  rewrite branch_geu_U, (U_atom E 21 (p_cap cx) V21), (U_atom E 10 c V10) in Hc by lia.
  apply negb_true_iff, Z.ltb_ge in Hc.
  assert (Hcut : p_nF cx < e + 16 + c).
  { destruct (Z.lt_ge_cases (p_nF cx) (e + 16 + c)) as [H|H]; [exact H | exfalso].
    rewrite (proj2 (Z.leb_le c (p_cap cx)) Hc), (proj2 (Z.leb_le (e + 16 + c) (p_nF cx)) H) in HK0.
    pose proof (m_skips_exit _ _ _ _ _ Hsk ltac:(unfold p_kind in HK0; rewrite HK0; discriminate)
      ltac:(unfold p_kind in HK0; rewrite HK0; discriminate)) as HQ.
    apply Hkind. rewrite HQ. exact HK0. }
  rewrite (proj2 (Z.leb_le c (p_cap cx)) Hc), (proj2 (Z.leb_gt (e + 16 + c) (p_nF cx)) ltac:(lia)) in HK0.
  paj_run_to_tok RUNTO HS HJ SHOK TBspan PP_W0;
    [unfold lc_rs; cbn [ss_mem]; apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_nil |].
  assert (HFm : ms_mem ms0 = ms_mem ms3) by (rewrite (frame_of_ro E lc_rs _ _ Hro HF); exact HFm1).
  pmkst HS.
  prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8.
  prreg HS (9%bv : bv 5) Q9. prreg HS (12%bv : bv 5) Q12. prreg HS (13%bv : bv 5) Q13.
  prreg HS (19%bv : bv 5) Q19. prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21.
  prreg HS (22%bv : bv 5) Q22. prreg HS (23%bv : bv 5) Q23. prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
  prreg HS (29%bv : bv 5) Q29.
  assert (Hd13 : sv_denot E a3_fit = getr (ms_regs ms0) 13)
    by (rewrite Q13; unfold a3_fit; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; reflexivity).
  lw0_close NEXT6 HB Hfrs Hmo HLW0 HFm ms0 HJ Hag memS. rewrite <- Hd13, (denot_lit_U E).
  rewrite (proj2 (res_stop cx e (p_q cx p) Hsk ltac:(rewrite HK0; discriminate) ltac:(rewrite HK0; discriminate)
    ltac:(rewrite HK0; discriminate) ltac:(rewrite HK0; discriminate))).
  unfold a3_fit. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
  rewrite UA, (U_atom E 11 (p_nF cx) V11), (U_atom E 10 c V10), U_SLit by lia.
  rewrite (proj2 (Z.ltb_lt (p_nF cx) (c + (e + 16))) ltac:(lia)).
  change (zcanon (zcanon 0 - 1)) with (2 ^ 64 - 1).
  rewrite lor_ones64 by lia. unfold w64. apply bv_eq. rewrite !Z_to_bv_unsigned. reflexivity.
- (* cap < len *)
  rewrite branch_geu_U, (U_atom E 21 (p_cap cx) V21), (U_atom E 10 c V10) in Hc by lia.
  apply negb_false_iff, Z.ltb_lt in Hc.
  rewrite (proj2 (Z.leb_gt c (p_cap cx)) Hc) in HK0. rename Hc into Hcap_lt.
  paj_run_tok RUN HS HJ SHOK TBspan; [unfold lc_rs; cbn [ss_mem]; apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_nil |].
  assert (HFm2 : ms_mem ms0 = ms_mem ms3) by (rewrite (frame_of_ro E lc_rs _ _ Hro HF); exact HFm1).
  clear HF HFr HG.
  psrr_branch_tok RUN BR HS SHOK TBspan.
  + (* d = 0, so cap = 0: KBig0, to 0x810a0 with want = -1 *)
    rewrite branch_eq_U, (U_atom E 32 (p_d cx) E32), U_lit in Hc by lia.
    apply Z.eqb_eq in Hc.
    assert (Hcap0 : p_cap cx = 0) by (unfold p_cap; lia).
    rewrite Hcap0, Z.eqb_refl in HK0.
    paj_run_to_tok RUNTO HS HJ SHOK TBspan PP_W0;
      [unfold lc_rs; cbn [ss_mem]; apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_nil |].
    assert (HFm : ms_mem ms1 = ms_mem ms3) by (rewrite (frame_of_ro E lc_rs _ _ Hro HF); exact HFm2).
    pmkst HS.
    prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8.
    prreg HS (9%bv : bv 5) Q9. prreg HS (12%bv : bv 5) Q12. prreg HS (13%bv : bv 5) Q13.
    prreg HS (19%bv : bv 5) Q19. prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21.
    prreg HS (22%bv : bv 5) Q22. prreg HS (23%bv : bv 5) Q23. prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
    prreg HS (29%bv : bv 5) Q29.
    lw0_close NEXT6 HB Hfrs Hmo HLW0 HFm ms1 HJ Hag memS. rewrite Q13, E13, R13.
    rewrite (proj2 (res_stop cx e (p_q cx p) Hsk ltac:(rewrite HK0; discriminate) ltac:(rewrite HK0; discriminate)
      ltac:(rewrite HK0; discriminate) ltac:(rewrite HK0; discriminate))). reflexivity.
  + rewrite branch_eq_U, (U_atom E 32 (p_d cx) E32), U_lit in Hc by lia.
    apply Z.eqb_neq in Hc.
    assert (Hcap0 : p_cap cx <> 0) by (unfold p_cap; lia).
    rewrite (proj2 (Z.eqb_neq _ 0) Hcap0) in HK0. rename Hc into Hd_ne.
    paj_run_tok RUN HS HJ SHOK TBspan; [unfold lc_rs; cbn [ss_mem]; apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_nil |].
    assert (HFm3 : ms_mem ms1 = ms_mem ms3) by (rewrite (frame_of_ro E lc_rs _ _ Hro HF); exact HFm2).
    clear HF HFr HG.
    psrr_branch_tok RUN BR HS SHOK TBspan.
    * (* |F| < e+16+len: KCutBig, to 0x810a0 with want = -1 *)
      rewrite branch_ltu_U, UA, (U_atom E 11 (p_nF cx) V11) in Hc by lia.
      apply Z.ltb_lt in Hc.
      rewrite (proj2 (Z.leb_gt (e + 16 + c) (p_nF cx)) ltac:(lia)) in HK0.
      paj_run_to_tok RUNTO HS HJ SHOK TBspan PP_W0;
        [unfold lc_rs; cbn [ss_mem]; apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_nil |].
      assert (HFm : ms_mem ms2 = ms_mem ms3) by (rewrite (frame_of_ro E lc_rs _ _ Hro HF); exact HFm3).
      pmkst HS.
      prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8.
      prreg HS (9%bv : bv 5) Q9. prreg HS (12%bv : bv 5) Q12. prreg HS (13%bv : bv 5) Q13.
      prreg HS (19%bv : bv 5) Q19. prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21.
      prreg HS (22%bv : bv 5) Q22. prreg HS (23%bv : bv 5) Q23. prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
      prreg HS (29%bv : bv 5) Q29.
      lw0_close NEXT6 HB Hfrs Hmo HLW0 HFm ms2 HJ Hag memS. rewrite Q13, E13, R13.
      rewrite (proj2 (res_stop cx e (p_q cx p) Hsk ltac:(rewrite HK0; discriminate) ltac:(rewrite HK0; discriminate)
        ltac:(rewrite HK0; discriminate) ltac:(rewrite HK0; discriminate))). reflexivity.
    * rewrite branch_ltu_U, UA, (U_atom E 11 (p_nF cx) V11) in Hc by lia.
      apply Z.ltb_ge in Hc.
      rewrite (proj2 (Z.leb_le (e + 16 + c) (p_nF cx)) ltac:(lia)) in HK0. rename Hc into Hfit_le.
      assert (Hsk' : p_skips cx (e + 16 + c) (p_q cx p))
        by (exact (m_skips_big_inv _ _ _ _ _ Hsk HK0)).
      paj_run_tok RUN HS HJ SHOK TBspan; [unfold lc_rs; cbn [ss_mem]; apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_nil |].
      assert (HFm4 : ms_mem ms2 = ms_mem ms3) by (rewrite (frame_of_ro E lc_rs _ _ Hro HF); exact HFm3).
      clear HF HFr HG.
      psrr_branch_tok RUN BR HS SHOK TBspan.
      -- (* e' := e+16+len <> |F|: back to PP_KW *)
        rewrite branch_ne_U, UA, (U_atom E 11 (p_nF cx) V11) in Hc by lia.
        apply negb_true_iff, Z.eqb_neq in Hc.
        paj_run_to_tok RUNTO HS HJ SHOK TBspan PP_KW;
          [unfold lc_rs; cbn [ss_mem]; apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_nil |].
        assert (HFmK : ms_mem ms4 = ms_mem ms3) by (rewrite (frame_of_ro E lc_rs _ _ Hro HF); exact HFm4).
        pmkst HS.
        prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8.
        prreg HS (9%bv : bv 5) Q9. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12. prreg HS (13%bv : bv 5) Q13.
        prreg HS (14%bv : bv 5) Q14. prreg HS (18%bv : bv 5) Q18.
        prreg HS (19%bv : bv 5) Q19. prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21.
        prreg HS (22%bv : bv 5) Q22. prreg HS (23%bv : bv 5) Q23. prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
        prreg HS (29%bv : bv 5) Q29.
        assert (Hd18 : sv_denot E (SAlu ALU_ADD (SOff 10 0) (SOff 15 0)) = getr (ms_regs ms4) 18)
          by (rewrite Q18; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; reflexivity).
        apply (IH cx fp k acc ly3 S3 W3 (mkst (ms_regs ms4) (Z_to_bv 64 (BASE + PP_KW)) (ms_mem ms4) (seg_rom SEGS))
          _ HB (gx_pack0 cx _ memS _ _ _ _ _ _ HJ Hag) Hfrs Hmo).
        exists bb, hh, bf, p, (e + 16 + c). cbn [ms_regs mkst].
        split; [|split; [|split]].
        ++ apply (LW_move PP_LC PP_KW cx fp k acc ly3 S3 W3 ms3 md3 _ _ bb hh bf p e (e + 16 + c) HLW);
             cbn [ms_mem ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr ms_regs mkst]; try reflexivity;
             try exact HFmK; try kr; try lia; try exact Hsk';
             first [rewrite !(proj1 (fs_wvb _ _)); reflexivity | rewrite !(proj2 (fs_wvb _ _)); reflexivity].
        ++ rewrite <- Hd18, (denot_lit_U E), UA. unfold w64. f_equal. lia.
        ++ rewrite Q13, E13. exact R13.
        ++ lia.
      -- (* e' = |F|: 0x812fc j 0x8109c; mv a3,zero; to 0x810a0 with want = 0 *)
        rewrite branch_ne_U, UA, (U_atom E 11 (p_nF cx) V11) in Hc by lia.
        apply negb_false_iff, Z.eqb_eq in Hc.
        paj_run_to_tok RUNTO HS HJ SHOK TBspan PP_W0;
          [unfold lc_rs; cbn [ss_mem]; apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_nil |].
        assert (HFm : ms_mem ms4 = ms_mem ms3) by (rewrite (frame_of_ro E lc_rs _ _ Hro HF); exact HFm4).
        pmkst HS.
        prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8.
        prreg HS (9%bv : bv 5) Q9. prreg HS (12%bv : bv 5) Q12. prreg HS (13%bv : bv 5) Q13.
        prreg HS (19%bv : bv 5) Q19. prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21.
        prreg HS (22%bv : bv 5) Q22. prreg HS (23%bv : bv 5) Q23. prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
        prreg HS (29%bv : bv 5) Q29.
        lw0_close NEXT6 HB Hfrs Hmo HLW0 HFm ms4 HJ Hag memS.
        rewrite Q13. rewrite (res_end cx (p_q cx p) ltac:(rewrite <- Hc; replace (c + (e + 16)) with (e + 16 + c) by lia;
          exact Hsk')). reflexivity.
Qed.

(* 0x812d4 beqz a0 (length 0: 0x812f4 mv s2,a5 = e+16; bne a5,a1 0x81224 or j 0x8109c); else 0x812d8 slli/srli 32. *)
Lemma segD : forall n, pe_from SK B MT KS POST (GI_K6 B MT KS) -> pe_from SK B MT KS POST (GI_KWn n) ->
  pe_from SK B MT KS POST (GI_LC (S n)) -> pe_from SK B MT KS POST (GI_LD (S n)).
Proof.
intros n NEXT6 IH NEXTC cx fp k acc ly3 S3 W3 ms3 md3 HB HJ0 Hfrs Hmo HG.
destruct HG as (bb & hh & bf & p & e & HLW & R10 & R15 & R13 & HeF16 & Hmeas).
pose proof HLW as ((HPC & Hpad & Hn26 & Hgood & R12 & R19 & R20 & R21 & R22 & R23 & R26 & R29 & Hslots & Hglob & Hreader) &
  Hpe & HeF & Hsk & Hkind & R11 & R14).
pose proof HLW as (HLW0 & _).
pose proof HPC as ((Hpc & Hresv & Hsvc & Hrom & Hfrg & Hfcsr & Hregs & _) & _).
destruct Hregs as (Rsp & Rs0 & Rs1 & Rs11 & Rgp & Rtp).
pose proof (tail_geo cx HB) as (Hal & Hs1m & Hs1b & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HJ0 as HJ0'. destruct (gx_open _ _ _ _ _ _ _ _ HJ0') as (memS & HJ & Hag). clear HJ0'.
pose proof (p_d_range cx) as Hd. pose proof (p_sizes cx) as (Hsz1 & Hsz2 & Hsz3).
unfold LLVMF_STK in Hslo, Hbot. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (m_incl_nonneg (p_sw cx) (p_F cx) e) as Hc1. pose proof (m_incl_lt (p_sw cx) (p_F cx) e) as Hc2.
fold (p_incl cx e) in Hc1, Hc2.
set (c := p_incl cx e) in *.
pose proof (sx32u_range c ltac:(lia)) as Hsx.
assert (HK0 : p_kind cx e = PSN.kind (p_sw cx) (p_F cx) (p_cap cx) e) by reflexivity.
rewrite k_at in HK0 by (change (PSN.flen (p_F cx)) with (p_nF cx); lia).
fold (p_incl cx e) in HK0. fold c in HK0.
pose proof (entry0 PP_LD ms3 W3 Hpc Hresv Hsvc Hrom Hfrg Hfcsr) as HS.
remember (Eimg (Ereg (ms_regs ms3) [])) as E eqn:HEdef.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg (ms_regs ms3) []) n)
  by (intros n0 Hn0; subst E; apply Eimg_low; exact Hn0).
assert (E2 : ew E 2 = getr (ms_regs ms3) 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr (ms_regs ms3) 3) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr (ms_regs ms3) 4) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 4 4%bv eq_refl)).
assert (E8 : ew E 8 = getr (ms_regs ms3) 8) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 8 8%bv eq_refl)).
assert (E9 : ew E 9 = getr (ms_regs ms3) 9) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 9 9%bv eq_refl)).
assert (E10 : ew E 10 = getr (ms_regs ms3) 10) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 10 10%bv eq_refl)).
assert (E11 : ew E 11 = getr (ms_regs ms3) 11) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 11 11%bv eq_refl)).
assert (E12 : ew E 12 = getr (ms_regs ms3) 12) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 12 12%bv eq_refl)).
assert (E13 : ew E 13 = getr (ms_regs ms3) 13) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 13 13%bv eq_refl)).
assert (E14 : ew E 14 = getr (ms_regs ms3) 14) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 14 14%bv eq_refl)).
assert (E15 : ew E 15 = getr (ms_regs ms3) 15) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 15 15%bv eq_refl)).
assert (E19 : ew E 19 = getr (ms_regs ms3) 19) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 19 19%bv eq_refl)).
assert (E20 : ew E 20 = getr (ms_regs ms3) 20) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 20 20%bv eq_refl)).
assert (E21 : ew E 21 = getr (ms_regs ms3) 21) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 21 21%bv eq_refl)).
assert (E22 : ew E 22 = getr (ms_regs ms3) 22) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 22 22%bv eq_refl)).
assert (E23 : ew E 23 = getr (ms_regs ms3) 23) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 23 23%bv eq_refl)).
assert (E26 : ew E 26 = getr (ms_regs ms3) 26) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 26 26%bv eq_refl)).
assert (E27 : ew E 27 = getr (ms_regs ms3) 27) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 27 27%bv eq_refl)).
assert (E29 : ew E 29 = getr (ms_regs ms3) 29) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 29 29%bv eq_refl)).
assert (V10 : ew E 10 = Z_to_bv 64 (sx32u c)) by (rewrite E10, R10; reflexivity).
assert (V11 : ew E 11 = Z_to_bv 64 (p_nF cx)) by (rewrite E11, R11; reflexivity).
assert (V15 : ew E 15 = Z_to_bv 64 (e + 16)) by (rewrite E15, R15; reflexivity).
assert (SHOK : sh_ok SEGS TBx [] E (mrestrict (w_H W3) (ms_mem ms3))) by constructor.
clear HEdef EL.
psrr_branch_tok RUN BR HS SHOK TBspan.
- (* length 0: KEmpty, e += 16 *)
  rewrite branch_eq_U, (U_atom E 10 (sx32u c) V10), U_lit, sx32u_zero in Hc by lia.
  apply Z.eqb_eq in Hc. rewrite Hc, Z.eqb_refl in HK0. rename Hc into Hc0.
  assert (Hsk' : p_skips cx (e + 16) (p_q cx p)) by exact (m_skips_empty_inv _ _ _ _ _ Hsk HK0).
  paj_run_tok RUN HS HJ SHOK TBspan; [apply awr_ok_nil |].
  assert (HFm1 : ms_mem ms = ms_mem ms3) by exact (frame_of_nil _ _ _ HF).
  clear HF HFr HG.
  psrr_branch_tok RUN BR HS SHOK TBspan.
  + rewrite branch_ne_U, (U_atom E 15 (e + 16) V15), (U_atom E 11 (p_nF cx) V11) in Hc by lia.
    apply negb_true_iff, Z.eqb_neq in Hc.
    paj_run_to_tok RUNTO HS HJ SHOK TBspan PP_KW; [apply awr_ok_nil |].
    assert (HFm : ms_mem ms0 = ms_mem ms3) by (rewrite (frame_of_nil _ _ _ HF); exact HFm1).
    pmkst HS.
    prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8.
    prreg HS (9%bv : bv 5) Q9. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12. prreg HS (13%bv : bv 5) Q13.
    prreg HS (14%bv : bv 5) Q14. prreg HS (18%bv : bv 5) Q18.
    prreg HS (19%bv : bv 5) Q19. prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21.
    prreg HS (22%bv : bv 5) Q22. prreg HS (23%bv : bv 5) Q23. prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
    prreg HS (29%bv : bv 5) Q29.
    apply (IH cx fp k acc ly3 S3 W3 (mkst (ms_regs ms0) (Z_to_bv 64 (BASE + PP_KW)) (ms_mem ms0) (seg_rom SEGS))
      _ HB (gx_pack0 cx _ memS _ _ _ _ _ _ HJ Hag) Hfrs Hmo).
    exists bb, hh, bf, p, (e + 16). cbn [ms_regs mkst].
    split; [|split; [|split]].
    * apply (LW_move PP_LD PP_KW cx fp k acc ly3 S3 W3 ms3 md3 _ _ bb hh bf p e (e + 16) HLW);
        cbn [ms_mem ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr ms_regs mkst]; try reflexivity;
        try exact HFm; try kr; try lia; try exact Hsk';
        first [rewrite !(proj1 (fs_wvb _ _)); reflexivity | rewrite !(proj2 (fs_wvb _ _)); reflexivity].
    * rewrite Q18, E15. exact R15.
    * rewrite Q13, E13. exact R13.
    * lia.
  + rewrite branch_ne_U, (U_atom E 15 (e + 16) V15), (U_atom E 11 (p_nF cx) V11) in Hc by lia.
    apply negb_false_iff, Z.eqb_eq in Hc.
    paj_run_to_tok RUNTO HS HJ SHOK TBspan PP_W0; [apply awr_ok_nil |].
    assert (HFm : ms_mem ms0 = ms_mem ms3) by (rewrite (frame_of_nil _ _ _ HF); exact HFm1).
    pmkst HS.
    prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8.
    prreg HS (9%bv : bv 5) Q9. prreg HS (12%bv : bv 5) Q12. prreg HS (13%bv : bv 5) Q13.
    prreg HS (19%bv : bv 5) Q19. prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21.
    prreg HS (22%bv : bv 5) Q22. prreg HS (23%bv : bv 5) Q23. prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
    prreg HS (29%bv : bv 5) Q29.
    lw0_close NEXT6 HB Hfrs Hmo HLW0 HFm ms0 HJ Hag memS.
    rewrite Q13. rewrite (res_end cx (p_q cx p) ltac:(rewrite <- Hc; exact Hsk')). reflexivity.
- (* length <> 0: the zero-extension, at 0x812e0 *)
  rewrite branch_eq_U, (U_atom E 10 (sx32u c) V10), U_lit, sx32u_zero in Hc by lia.
  apply Z.eqb_neq in Hc.
  paj_run_to_tok RUNTO HS HJ SHOK TBspan PP_LC; [apply awr_ok_nil |].
  assert (HFm : ms_mem ms = ms_mem ms3) by exact (frame_of_nil _ _ _ HF).
  pmkst HS.
  prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8.
  prreg HS (9%bv : bv 5) Q9. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
  prreg HS (13%bv : bv 5) Q13. prreg HS (14%bv : bv 5) Q14. prreg HS (15%bv : bv 5) Q15.
  prreg HS (19%bv : bv 5) Q19. prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21.
  prreg HS (22%bv : bv 5) Q22. prreg HS (23%bv : bv 5) Q23. prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
  prreg HS (29%bv : bv 5) Q29.
  assert (Hd10 : sv_denot E (SAlu ALU_SRL (SAlu ALU_SLL (SOff 10 0) (SLit 32)) (SLit 32)) = getr (ms_regs ms) 10)
    by (rewrite Q10; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; reflexivity).
  apply (NEXTC cx fp k acc ly3 S3 W3 (mkst (ms_regs ms) (Z_to_bv 64 (BASE + PP_LC)) (ms_mem ms) (seg_rom SEGS))
    _ HB (gx_pack0 cx _ memS _ _ _ _ _ _ HJ Hag) Hfrs Hmo).
  exists bb, hh, bf, p, e. cbn [ms_regs mkst].
  split; [|split; [|split; [|split; [|split; [|split]]]]].
  + apply (LW_move PP_LD PP_LC cx fp k acc ly3 S3 W3 ms3 md3 _ _ bb hh bf p e e HLW);
      cbn [ms_mem ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr ms_regs mkst]; try reflexivity;
      try exact HFm; try kr; try lia; try exact Hsk;
      first [rewrite !(proj1 (fs_wvb _ _)); reflexivity | rewrite !(proj2 (fs_wvb _ _)); reflexivity].
  + rewrite <- Hd10, (denot_lit_U E), (U_zx32 E _ (sx32u c) (U_atom E 10 (sx32u c) V10 ltac:(lia))), sx32u_mod by lia.
    reflexivity.
  + exact Hc.
  + rewrite Q15, E15. exact R15.
  + rewrite Q13, E13. exact R13.
  + exact HeF16.
  + exact Hmeas.
Qed.

(* The entry of a segment over memory regions with s11 the shadow base as a literal (so the engine sees the shadow
   address (x >> 3) + 0x7fff8000 of a shadow check). *)
Lemma pC_nth : forall cx j, nth j (p_C cx) 0 = bv_unsigned (nth j (p_F cx) (Z_to_bv 8 0)).
Proof.
  intros cx j. unfold p_C.
  rewrite <- (map_nth (fun x : byte => bv_unsigned x) (p_F cx) (Z_to_bv 8 0) j).
  reflexivity.
Qed.

Definition tregs : list sv := sr_set sr_atoms 27 (SLit 0x7fff8000).

Lemma entryRT : forall pc (ms : machine_state) (W : world SEGS) ext rs G,
  ms_pc_val ms = w64 (BASE + pc) -> ms_resv ms = None -> ms_svc_pending ms = None -> ms_rom ms = seg_rom SEGS ->
  ms_fregs ms = fp_regs -> ms_fcsr ms = fp_csr -> getr (ms_regs ms) 27 = Z_to_bv 64 0x7fff8000 ->
  regions_wf rs = true ->
  Forall (region_ok SEGS (Eimg (Ereg (ms_regs ms) ext)) (mrestrict (w_H W) (ms_mem ms))) rs ->
  pairwise_disjoint (Eimg (Ereg (ms_regs ms) ext)) rs ->
  facts_ok (Eimg (Ereg (ms_regs ms) ext)) G ->
  st_ok_pi SEGS VAL (Eimg (Ereg (ms_regs ms) ext)) (mkSS pc tregs rs None G) (restrict (w_H W) ms).
Proof.
  intros pc ms W ext rs G Hpc Hresv Hsvc Hrom Hfrg Hfcsr H27 Hwf Hrs Hd Hf.
  pose proof (ms_eta ms Hfrg Hsvc Hresv Hfcsr) as Hms. rewrite Hpc, Hrom in Hms.
  assert (Hms' : restrict (w_H W) ms =
    mkst (ms_regs ms) (Z_to_bv 64 (BASE + pc)) (mrestrict (w_H W) (ms_mem ms)) (seg_rom SEGS))
    by (rewrite Hms at 1; reflexivity).
  rewrite Hms'. apply pa_entry_st_ok_full; [| exact Hwf | exact Hrs | exact Hd | exact Hf].
  unfold tregs. apply regs_ok_pin; [apply regs_ok_Eimg_Ereg | | cbn [sv_denot]; exact H27].
  intros H0. apply (f_equal bv_unsigned) in H0. cbv in H0. discriminate H0.
Qed.

Lemma copy_byte : forall cx m bb i, garr8 SEGS m bb (p_C cx) -> 0 <= i < p_nF cx ->
  val_mem SEGS m (bb + i) 1 (PSN.fb (p_F cx) i) /\ 0 <= PSN.fb (p_F cx) i < 256.
Proof.
  intros cx m bb i H Hi. assert (HL : Z.of_nat (length (p_C cx)) = p_nF cx) by (unfold p_C, p_nF; rewrite length_map; reflexivity).
  destruct (H (Z.to_nat i) ltac:(lia)) as [V R]. rewrite Z2Nat.id in V by lia. rewrite pC_nth in V, R. split; assumption.
Qed.

Definition lb_rs : smem :=
  [ YP09.mkRegion (Some 18%nat) 8 12 12 12
      [YP09.mkChunk 8 (CVal 1 (SOff 34 0)); YP09.mkChunk 9 (CVal 1 (SOff 35 0));
       YP09.mkChunk 10 (CVal 1 (SOff 36 0)); YP09.mkChunk 11 (CVal 1 (SOff 37 0))];
    YP09.mkRegion (Some 29%nat) 8 12 12 12 [YP09.mkChunk 8 (CVal 4 (SOff 32 0))] ].
Definition lb_G : facts := mkFacts [(18%nat, mkAF 4096 0x7fffff800000 0)] [] [].
Definition lb_SH : list shent := [mkSHE 18 8 12].

(* 0x81230 .. 0x812ac: the four shadow-checked byte loads (0x8123c/0x81254/0x8126c/0x81284 lb of the shadow cell,
   0x81244/0x8125c/0x81274/0x8128c bnez to the slow blocks 0x81300/0x8130c/0x81318/0x81324, whose bge/blt edges
   0x81304/0x81310/0x8131c and fall-through 0x8132c reach __asan_report_load1): each is decided by the token engine
   from the shent (18, 8, 12), i.e. range_addressable over b+e+8 .. b+e+11, a sub-range of the copy (b, |F|)
   since e + 16 <= |F| (range_addressable_of_block); then the word of the four bytes; 0x812ac beqz ps->sw (no swap)
   or the swap 0x812b0..0x812d0; at 0x812d4. *)
Lemma segB : forall n, pe_from SK B MT KS POST (GI_LD n) -> pe_from SK B MT KS POST (GI_LB n).
Proof.
intros n NEXTD cx fp k acc ly3 S3 W3 ms3 md3 HB HJ0 Hfrs Hmo HG.
destruct HG as (bb & hh & bf & p & e & HLW & R18 & R15 & R13 & HeF16 & Hmeas).
pose proof HLW as ((HPC & Hpad & Hn26 & Hgood & R12 & R19 & R20 & R21 & R22 & R23 & R26 & R29 & Hslots & Hglob & Hreader) &
  Hpe & HeF & Hsk & Hkind & R11 & R14).
pose proof HPC as ((Hpc & Hresv & Hsvc & Hrom & Hfrg & Hfcsr & Hregs & _) & _ & _ & Hperm & _).
destruct Hregs as (Rsp & Rs0 & Rs1 & Rs11 & Rgp & Rtp).
pose proof (tail_geo cx HB) as (Hal & Hs1m & Hs1b & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HJ0 as HJ0'. destruct (gx_open _ _ _ _ _ _ _ _ HJ0') as (memS & HJ & Hag). clear HJ0'.
pose proof (p_d_range cx) as Hd. pose proof (p_sizes cx) as (Hsz1 & Hsz2 & Hsz3).
unfold LLVMF_STK in Hslo, Hbot. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (HAR & Hly & _).
destruct (lay_eqs _ _ _ Hly) as (EF & Etop & Eslo & Eshi).
assert (Efa : frame_addr ly3 PE_CID fp = pF cx fp) by (unfold pF, frame_addr; rewrite EF; reflexivity).
assert (Hfin : In (PE_CID, fp) (frames S3)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 PE_CID fp HAR Hfin) as (Hf4096 & Hfceil & Hfapp).
rewrite Efa in Hf4096, Hfceil, Hfapp. change (fs_frame_bytes PE_CID) with 128 in Hfceil, Hfapp.
assert (Hbin : In (bb, p_nF cx) (ablocks B ly3 S3))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ bb (p_nF cx) HAR Hbin) as (_ & Hb4096 & Hbceil & Hbapp & _).
pose proof (req_size_pos (p_nF cx) ltac:(lia)) as [Hrq1 Hrq2].
pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ bb (p_nF cx) PE_CID fp HAR Hbin Hfin) as Dbf.
unfold zdisjoint in Dbf. cbn [fst snd] in Dbf. rewrite Efa in Dbf. change (fs_frame_bytes PE_CID) with 128 in Dbf.
assert (Hps : pPS cx fp = pF cx fp + 32) by reflexivity.
pose proof Hreader as (Hsrc & (Hpsf & Hpsw) & _).
destruct Hsrc as (Wsrc & cpos & fl & mdd & _ & _ & _ & _ & _ & _ & _ & _ & Hgarr & _).
set (c0 := PSN.fb (p_F cx) (e + 8)). set (c1 := PSN.fb (p_F cx) (e + 9)).
set (c2 := PSN.fb (p_F cx) (e + 10)). set (c3 := PSN.fb (p_F cx) (e + 11)).
destruct (copy_byte cx _ bb (e + 8) Hgarr ltac:(lia)) as [B0 R0].
destruct (copy_byte cx _ bb (e + 9) Hgarr ltac:(lia)) as [B1 R1].
destruct (copy_byte cx _ bb (e + 10) Hgarr ltac:(lia)) as [B2 R2].
destruct (copy_byte cx _ bb (e + 11) Hgarr ltac:(lia)) as [B3 R3].
fold c0 in B0, R0. fold c1 in B1, R1. fold c2 in B2, R2. fold c3 in B3, R3.
pose proof (p_swz01 cx) as Hsw01.
remember (Eimg (Ereg (ms_regs ms3) [Z_to_bv 64 (p_swz cx); Z_to_bv 64 0; Z_to_bv 64 c0; Z_to_bv 64 c1;
  Z_to_bv 64 c2; Z_to_bv 64 c3])) as E eqn:HEdef.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg (ms_regs ms3) [Z_to_bv 64 (p_swz cx); Z_to_bv 64 0;
  Z_to_bv 64 c0; Z_to_bv 64 c1; Z_to_bv 64 c2; Z_to_bv 64 c3]) n)
  by (intros n0 Hn0; subst E; apply Eimg_low; exact Hn0).
assert (E2 : ew E 2 = getr (ms_regs ms3) 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr (ms_regs ms3) 3) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr (ms_regs ms3) 4) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 4 4%bv eq_refl)).
assert (E8 : ew E 8 = getr (ms_regs ms3) 8) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 8 8%bv eq_refl)).
assert (E9 : ew E 9 = getr (ms_regs ms3) 9) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 9 9%bv eq_refl)).
assert (E11 : ew E 11 = getr (ms_regs ms3) 11) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 11 11%bv eq_refl)).
assert (E12 : ew E 12 = getr (ms_regs ms3) 12) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 12 12%bv eq_refl)).
assert (E13 : ew E 13 = getr (ms_regs ms3) 13) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 13 13%bv eq_refl)).
assert (E14 : ew E 14 = getr (ms_regs ms3) 14) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 14 14%bv eq_refl)).
assert (E15 : ew E 15 = getr (ms_regs ms3) 15) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 15 15%bv eq_refl)).
assert (E18 : ew E 18 = getr (ms_regs ms3) 18) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 18 18%bv eq_refl)).
assert (E19 : ew E 19 = getr (ms_regs ms3) 19) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 19 19%bv eq_refl)).
assert (E20 : ew E 20 = getr (ms_regs ms3) 20) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 20 20%bv eq_refl)).
assert (E21 : ew E 21 = getr (ms_regs ms3) 21) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 21 21%bv eq_refl)).
assert (E22 : ew E 22 = getr (ms_regs ms3) 22) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 22 22%bv eq_refl)).
assert (E23 : ew E 23 = getr (ms_regs ms3) 23) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 23 23%bv eq_refl)).
assert (E26 : ew E 26 = getr (ms_regs ms3) 26) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 26 26%bv eq_refl)).
assert (E27 : ew E 27 = getr (ms_regs ms3) 27) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 27 27%bv eq_refl)).
assert (E29 : ew E 29 = getr (ms_regs ms3) 29) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 29 29%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 (p_swz cx)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 0)).
assert (E34 : ew E 34 = Z_to_bv 64 c0) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 c1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 c2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 4)).
assert (E37 : ew E 37 = Z_to_bv 64 c3) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 5)).
assert (U18 : bv_unsigned (ew E 18) = e + bb) by (rewrite E18, R18; unfold w64; apply unsigned_lit_small; lia).
assert (U29 : bv_unsigned (ew E 29) = pPS cx fp) by (rewrite E29, R29; unfold w64; apply unsigned_lit_small; lia).
assert (HS : st_ok_pi SEGS VAL E (mkSS PP_LB tregs lb_rs None lb_G) (restrict (w_H W3) ms3)).
{ rewrite HEdef. rewrite HEdef in U18, U29, E32, E34, E35, E36, E37.
  apply entryRT; try assumption; [vm_compute; reflexivity | | |].
  - unfold lb_rs. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite U18. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      * apply (chunk_ok_val SEGS _ _ (e + bb) 8 1 (SOff 34 0) c0);
          [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
        replace (e + bb + 8) with (bb + (e + 8)) by lia. exact B0.
      * apply (chunk_ok_val SEGS _ _ (e + bb) 9 1 (SOff 35 0) c1);
          [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
        replace (e + bb + 9) with (bb + (e + 9)) by lia. exact B1.
      * apply (chunk_ok_val SEGS _ _ (e + bb) 10 1 (SOff 36 0) c2);
          [cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
        replace (e + bb + 10) with (bb + (e + 10)) by lia. exact B2.
      * apply (chunk_ok_val SEGS _ _ (e + bb) 11 1 (SOff 37 0) c3);
          [cbn [sv_denot]; rewrite E37, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
        replace (e + bb + 11) with (bb + (e + 11)) by lia. exact B3.
    + rewrite U29. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS _ _ (pPS cx fp) 8 4 (SOff 32 0) (p_swz cx));
        [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      exact Hpsw.
  - apply pairwise_disjoint_of_extents. unfold lb_rs, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U18, U29.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. rewrite Hps. repeat split; lia.
  - split; [|split; exact I]. cbn [lb_G f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U18. change (2 ^ 0) with 1. rewrite Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; first [exact I | lia]. }
clear HEdef EL.
assert (SHOK : sh_ok SEGS TBx lb_SH E (mrestrict (w_H W3) (ms_mem ms3))).
{ constructor; [|constructor]. split.
  - cbn [she_m she_lo she_hi]. unfold TBx, SB_T. rewrite U_lit by lia.
    rewrite (U_atom E 18 (e + bb)) by (first [rewrite E18, R18; reflexivity | lia]).
    exact (range_addressable_of_block SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 bb (p_nF cx) (e + bb + 8) (12 - 8) HAR Hbin
      ltac:(lia) ltac:(lia)).
  - intros a Ha. cbn [she_m she_lo she_hi] in Ha. unfold TBx, SB_T. rewrite U_lit by lia.
    rewrite U_SOff, U18, Z.add_0_r, zcanon_id in Ha by (unfold M64; lia).
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hbapp. lia. }
assert (Hro : forall r, In r lb_rs -> YP09.r_whi r <= YP09.r_wlo r)
  by (intros r Hr; unfold lb_rs in Hr; cbn [In] in Hr; destruct Hr as [<- | [<- | []]]; cbn; lia).
paj_run_tok RUN HS HJ SHOK TBspan;
  [ unfold lb_rs; cbn [ss_mem]; apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_nil |].
assert (HFm1 : ms_mem ms = ms_mem ms3) by exact (frame_of_ro E lb_rs _ _ Hro HF).
clear HF HFr HG.
(* The run took four shadow tokens, which extend E above every atom below 38. *)
lazymatch type of HS with st_ok_pi _ _ ?E1 _ _ =>
  assert (HE1 : forall n, (n < 38)%nat -> ew E1 n = ew E n)
    by (intros n0 Hn0; rewrite ?ew_ewset_other by lia; reflexivity);
  assert (USW : U E1 (SExt true 32 (SOff 32 0)) = p_swz cx)
    by (rewrite U_SExt, (U_atom E1 32 (p_swz cx)) by (first [rewrite HE1 by lia; exact E32 | lia]);
        destruct Hsw01 as [Hz|Hz]; rewrite Hz; reflexivity)
end.
psrr_branch_tok RUN BR HS SHOK TBspan.
- (* ps->sw = 0: the bytes in file order *)
  rewrite branch_eq_U, USW, U_lit in Hc by lia. apply Z.eqb_eq in Hc.
  assert (Hswf : p_sw cx = false) by (unfold p_sw; rewrite Hc; reflexivity).
  paj_run_to_tok RUNTO HS HJ SHOK TBspan PP_LD;
    [ unfold lb_rs; cbn [ss_mem]; apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_nil |].
  assert (HFm : ms_mem ms0 = ms_mem ms3) by (rewrite (frame_of_ro _ lb_rs _ _ Hro HF); exact HFm1).
  pmkst HS.
  prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8.
  prreg HS (9%bv : bv 5) Q9. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
  prreg HS (13%bv : bv 5) Q13. prreg HS (14%bv : bv 5) Q14. prreg HS (15%bv : bv 5) Q15.
  prreg HS (19%bv : bv 5) Q19. prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21.
  prreg HS (22%bv : bv 5) Q22. prreg HS (23%bv : bv 5) Q23. prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
  prreg HS (29%bv : bv 5) Q29.
  lazymatch type of HS with st_ok_pi _ _ ?E2 _ _ =>
    assert (HE2 : forall n, (n < 38)%nat -> ew E2 n = ew E n)
      by (intros n0 Hn0; rewrite ?ew_ewset_other by lia; reflexivity);
    assert (Hd10 : sv_denot E2 ns_expr = getr (ms_regs ms0) 10)
      by (rewrite Q10; unfold ns_expr, a_expr, zb; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; reflexivity);
    rewrite (denot_lit_U E2) in Hd10;
    rewrite (U_ns_expr E2 c0 c1 c2 c3 ltac:(rewrite HE2 by lia; exact E34) ltac:(rewrite HE2 by lia; exact E35)
      ltac:(rewrite HE2 by lia; exact E36) ltac:(rewrite HE2 by lia; exact E37) R0 R1 R2 R3) in Hd10;
    repeat match goal with Q : getr _ _ = ew E2 ?n |- _ => rewrite (HE2 n ltac:(lia)) in Q end
  end.
  apply (NEXTD cx fp k acc ly3 S3 W3 (mkst (ms_regs ms0) (Z_to_bv 64 (BASE + PP_LD)) (ms_mem ms0) (seg_rom SEGS))
    _ HB (gx_pack0 cx _ memS _ _ _ _ _ _ HJ Hag) Hfrs Hmo).
  exists bb, hh, bf, p, e. cbn [ms_regs mkst].
  split; [|split; [|split; [|split; [|split]]]].
  + apply (LW_move PP_LB PP_LD cx fp k acc ly3 S3 W3 ms3 md3 _ _ bb hh bf p e e HLW);
      cbn [ms_mem ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr ms_regs mkst]; try reflexivity;
      try exact HFm; try kr; try (rewrite Q27, Rs11; reflexivity); try lia; try exact Hsk;
      first [rewrite !(proj1 (fs_wvb _ _)); reflexivity | rewrite !(proj2 (fs_wvb _ _)); reflexivity].
  + rewrite <- Hd10. unfold p_incl, PSN.incl, PSN.hw. rewrite Hswf. unfold c0, c1, c2, c3.
    replace (e + 8 + 1) with (e + 9) by lia. replace (e + 8 + 2) with (e + 10) by lia.
    replace (e + 8 + 3) with (e + 11) by lia. reflexivity.
  + rewrite Q15, E15. exact R15.
  + rewrite Q13, E13. exact R13.
  + exact HeF16.
  + exact Hmeas.
- (* ps->sw = 1: the bytes swapped *)
  rewrite branch_eq_U, USW, U_lit in Hc by lia. apply Z.eqb_neq in Hc.
  assert (Hswt : p_sw cx = true) by (unfold p_sw; destruct Hsw01 as [Hz|Hz]; [lia | rewrite Hz; reflexivity]).
  paj_run_to_tok RUNTO HS HJ SHOK TBspan PP_LD;
    [ unfold lb_rs; cbn [ss_mem]; apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_nil |].
  assert (HFm : ms_mem ms0 = ms_mem ms3) by (rewrite (frame_of_ro _ lb_rs _ _ Hro HF); exact HFm1).
  pmkst HS.
  prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8.
  prreg HS (9%bv : bv 5) Q9. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
  prreg HS (13%bv : bv 5) Q13. prreg HS (14%bv : bv 5) Q14. prreg HS (15%bv : bv 5) Q15.
  prreg HS (19%bv : bv 5) Q19. prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21.
  prreg HS (22%bv : bv 5) Q22. prreg HS (23%bv : bv 5) Q23. prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
  prreg HS (29%bv : bv 5) Q29.
  lazymatch type of HS with st_ok_pi _ _ ?E2 _ _ =>
    assert (HE2 : forall n, (n < 38)%nat -> ew E2 n = ew E n)
      by (intros n0 Hn0; rewrite ?ew_ewset_other by lia; reflexivity);
    assert (Hd10 : sv_denot E2 sw_expr = getr (ms_regs ms0) 10)
      by (rewrite Q10; unfold sw_expr, ns_expr, a_expr, zb; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
          reflexivity);
    rewrite (denot_lit_U E2) in Hd10;
    rewrite (U_sw_expr E2 c0 c1 c2 c3 ltac:(rewrite HE2 by lia; exact E34) ltac:(rewrite HE2 by lia; exact E35)
      ltac:(rewrite HE2 by lia; exact E36) ltac:(rewrite HE2 by lia; exact E37) R0 R1 R2 R3
      ltac:(apply U_atom; [rewrite HE2 by lia; rewrite E14, R14; reflexivity | lia])) in Hd10;
    repeat match goal with Q : getr _ _ = ew E2 ?n |- _ => rewrite (HE2 n ltac:(lia)) in Q end
  end.
  apply (NEXTD cx fp k acc ly3 S3 W3 (mkst (ms_regs ms0) (Z_to_bv 64 (BASE + PP_LD)) (ms_mem ms0) (seg_rom SEGS))
    _ HB (gx_pack0 cx _ memS _ _ _ _ _ _ HJ Hag) Hfrs Hmo).
  exists bb, hh, bf, p, e. cbn [ms_regs mkst].
  split; [|split; [|split; [|split; [|split]]]].
  + apply (LW_move PP_LB PP_LD cx fp k acc ly3 S3 W3 ms3 md3 _ _ bb hh bf p e e HLW);
      cbn [ms_mem ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr ms_regs mkst]; try reflexivity;
      try exact HFm; try kr; try (rewrite Q27, Rs11; reflexivity); try lia; try exact Hsk;
      first [rewrite !(proj1 (fs_wvb _ _)); reflexivity | rewrite !(proj2 (fs_wvb _ _)); reflexivity].
  + rewrite <- Hd10. unfold p_incl, PSN.incl, PSN.hw. rewrite Hswt. unfold c0, c1, c2, c3.
    replace (e + 8 + 1) with (e + 9) by lia. replace (e + 8 + 2) with (e + 10) by lia.
    replace (e + 8 + 3) with (e + 11) by lia. reflexivity.
  + rewrite Q15, E15. exact R15.
  + rewrite Q13, E13. exact R13.
  + exact HeF16.
  + exact Hmeas.
Qed.

(* The loop, by induction on the measure |F| - e. *)
Lemma tail_KWn : pe_from SK B MT KS POST (GI_K6 B MT KS) -> forall n, pe_from SK B MT KS POST (GI_KWn n).
Proof.
  intros NEXT6 n. induction n as [|n IH].
  - intros cx fp k acc ly3 S3 W3 ms3 md3 _ _ _ _ (bb & hh & bf & p & e & (_ & _ & HeF & _) & _ & _ & Hm). cbn in Hm. lia.
  - apply (segH (S n) NEXT6). apply segB. exact (segD n NEXT6 IH (segC n NEXT6 IH)).
Qed.

Lemma tail_KW : pe_from SK B MT KS POST (GI_K6 B MT KS) -> pe_from SK B MT KS POST (GI_KW B MT KS).
Proof.
  intros NEXT6 cx fp k acc ly3 S3 W3 ms3 md3 HB HJ Hfrs Hmo HG.
  destruct HG as (bb & hh & bf & p & e & HPC & Hpad & Hn26 & Hgood & (Hpe & HpeF) & HeF & Hne & Hsk & Hkind & R11 & R12 & R13 &
    R14 & R18 & R19 & R20 & R21 & R22 & R23 & R26 & R29 & Hslots & Hglob & Hreader).
  apply (tail_KWn NEXT6 (S (Z.to_nat (p_nF cx - e))) cx fp k acc ly3 S3 W3 ms3 md3 HB HJ Hfrs Hmo).
  exists bb, hh, bf, p, e. split; [|split; [exact R18 | split; [exact R13 | lia]]].
  split; [|split; [lia | split; [lia | split; [exact Hsk | split; [exact Hkind | split; [exact R11 | exact R14]]]]]].
  repeat (split; [assumption|]). exact Hreader.
Qed.

(* ---- W: PP_K5 -> the check loop -> pcap_source_close (0x810a8) -> PP_K6 ---- *)
Lemma tail_W : pe_from SK B MT KS POST (GI_K6 B MT KS) -> pe_from SK B MT KS POST (GI_K5 B MT KS).
Proof. intros NEXT6. exact (tail_W5 NEXT6 (tail_KW NEXT6)). Qed.

(* ---- R1: PP_K6 0x810ac -> the second pcap_source_open (0x810c4) -> PP_K7 0x810c8 -----------------------------
   ld s2,0x58(s1) (the spill slot PS_PSP, &ps); ld a0,0(s2) (ps->f, NULL after the close); bnez a0 0x810b4 (abort,
   refuted by GI_K6's p_psnull); auipc/addi a1 = the path literal (object 3); mv a0,s2; jal pcap_source_open. The
   file is the same (g_file, g_file_len unchanged), so the open's accepted arm applies. *)
Lemma magicZ_magic : forall cx, pcap_magicZ (p_C cx) = PST.pcap_magic (p_F cx).
Proof.
  intros cx. unfold pcap_magicZ, PST.pcap_magic, PST.pcap_byte. rewrite !pC_nth. reflexivity.
Qed.

Lemma goodZ_good : forall cx, pcap_goodZ (p_C cx) = p_good cx.
Proof.
  intros cx. unfold pcap_goodZ, p_good, PST.pcap_good. rewrite magicZ_magic.
  unfold p_C, p_nF. rewrite length_map. reflexivity.
Qed.

Lemma swZ_sw : forall cx, pcap_swZ (p_C cx) = p_swz cx.
Proof. intros cx. unfold pcap_swZ, p_swz, PST.pcap_sw. rewrite magicZ_magic. reflexivity. Qed.

Definition r1_rs : smem :=
  [ YP09.mkRegion (Some 9%nat) 88 96 0 0 [YP09.mkChunk 88 (CVal 8 (SOff 32 0))];
    YP09.mkRegion (Some 32%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SLit 0))] ].

Lemma tail_R1 : pe_from SK B MT KS POST (GI_K7 B MT KS) -> pe_from SK B MT KS POST (GI_K6 B MT KS).
Proof.
intros NEXT cx fp k acc ly3 S3 W3 ms3 md3 HB HJ Hfrs Hmo HG.
destruct HG as (bb & bf & (Hbody & Hk & Hacc & Hperm & Hfds & Hfs) & Hpad & Hn26 & Hgood & R19 & R20 & R21 & R22 &
  R23 & R26 & Hslots & Hglob & Hcopy & Hnull & Hsrc).
destruct Hbody as (Hpc & Hresv & Hsvc & Hrom & Hfrg & Hfcsr & Hregs & Hsaved & Hhdr & Hsh & Hlen & Hin).
pose proof (tail_geo cx HB) as (Hal & Hs1m & Hs1b & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
unfold LLVMF_STK in Hslo, Hbot.
pose proof HB as ((HAR0 & Hrok & Hra4 & Hgp0 & Htp0 & _) & HraL & _ & _ & _ & _ & _ & Hev & Hlive & _ & _ & _ & _ & _ &
  _ & _ & Hmok & Hneed & HGX & HGD & _ & _ & Hftr).
destruct (gx_open _ _ _ _ _ _ _ _ HJ) as (memS & HJi & Hag). clear HJ. rename HJi into HJ.
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & Hnev & Hk0 & _).
destruct Hregs as (Rsp & Rs0 & Rs1 & Rs11 & Rgp & Rtp).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as (HB0 & HB1 & HB2). pose proof (pa_base_lo (PL := PL_pcap) (PI := PI)) as HBLO.
pose proof (p_sizes cx) as (Hsz1 & Hsz2 & Hsz3).
destruct (lay_eqs _ _ _ Hly) as (EF & Etop & Eslo & Eshi).
assert (Efa : frame_addr ly3 PE_CID fp = pF cx fp) by (unfold pF, frame_addr; rewrite EF; reflexivity).
assert (Hfin : In (PE_CID, fp) (frames S3)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 PE_CID fp HAR Hfin) as (Hf4096 & Hfceil & Hfapp).
rewrite Efa in Hf4096, Hfceil, Hfapp. change (fs_frame_bytes PE_CID) with 128 in Hfceil, Hfapp.
destruct (frame_al64 SEGS B ly3 S3 W3 (ms_mem ms3) md3 PE_CID fp HAR Hfin) as (Hfa64 & _ & _). rewrite Efa in Hfa64.
assert (Hbin : In (bb, p_nF cx) (ablocks B ly3 S3))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; right; left; reflexivity).
assert (Hfbin : In (bf, p_bn cx) (ablocks B ly3 S3))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; right; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ bb (p_nF cx) HAR Hbin) as (_ & Hb4096 & Hbceil & _ & _ & _ & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ bf (p_bn cx) HAR Hfbin) as (_ & Hf4096' & Hfbceil & _ & _ & _ & _).
pose proof (req_size_pos (p_nF cx) ltac:(lia)) as [Hrqb1 Hrqb2].
pose proof (req_size_pos (p_bn cx) ltac:(lia)) as [Hrqf1 Hrqf2].
assert (ELC : Z.of_nat (length (p_C cx)) = p_nF cx) by (unfold p_C, p_nF; rewrite length_map; reflexivity).
assert (EBB : blocks_bytes S3 = blocks_bytes (c_S cx) + p_nF cx + p_bn cx).
{ rewrite (blocks_bytes_bsum B ly3 S3), (blocks_bytes_bsum B (c_ly cx) (c_S cx)).
  rewrite (bsum_perm _ _ Hperm), bsum_app. cbn [bsum fold_right snd]. lia. }
assert (Hps : pPS cx fp = pF cx fp + 32) by reflexivity.
assert (Hps8 : pPS cx fp mod 8 = 0).
{ rewrite Hps. apply Z.mod_divide; [lia|]. apply Z.mod_divide in Hfa64; [|lia]. destruct Hfa64 as [q Hq]. exists (8 * q + 4). lia. }
(* the symbolic state at 0x810ac *)
remember (Eimg (Ereg (ms_regs ms3) [Z_to_bv 64 (pPS cx fp)])) as E eqn:HEdef.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg (ms_regs ms3) [Z_to_bv 64 (pPS cx fp)]) n)
  by (intros n Hn; subst E; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr (ms_regs ms3) 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr (ms_regs ms3) 3) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr (ms_regs ms3) 4) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 4 4%bv eq_refl)).
assert (E8 : ew E 8 = getr (ms_regs ms3) 8) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 8 8%bv eq_refl)).
assert (E9 : ew E 9 = getr (ms_regs ms3) 9) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 9 9%bv eq_refl)).
assert (E19 : ew E 19 = getr (ms_regs ms3) 19) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 19 19%bv eq_refl)).
assert (E20 : ew E 20 = getr (ms_regs ms3) 20) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 20 20%bv eq_refl)).
assert (E21 : ew E 21 = getr (ms_regs ms3) 21) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 21 21%bv eq_refl)).
assert (E22 : ew E 22 = getr (ms_regs ms3) 22) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 22 22%bv eq_refl)).
assert (E23 : ew E 23 = getr (ms_regs ms3) 23) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 23 23%bv eq_refl)).
assert (E26 : ew E 26 = getr (ms_regs ms3) 26) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 26 26%bv eq_refl)).
assert (E27 : ew E 27 = getr (ms_regs ms3) 27) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 27 27%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 (pPS cx fp)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 0)).
assert (EO3 : ew E 244%nat = Z_to_bv 64 (pa_val (A_OBJ 3)))
  by (subst E; apply (Eimg_img _ 244%nat); unfold A_TEXT, A_LIM; lia).
assert (U9 : bv_unsigned (ew E 9) = c_sp1 cx) by (rewrite E9, Rs1; unfold w64; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = pPS cx fp) by (rewrite E32; apply unsigned_lit_small; lia).
assert (HS : st_ok_pi SEGS VAL E (mkSS PP_K6 sr_atoms r1_rs None nofacts) (restrict (w_H W3) ms3)).
{ rewrite HEdef. rewrite HEdef in U9, U32, E32.
  apply entryR; try assumption; [vm_compute; reflexivity | | | split; [exact I | split; exact I]].
  - unfold r1_rs. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS _ _ (c_sp1 cx) 88 8 (SOff 32 0) (pPS cx fp));
        [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3) _ _ (proj1 Hslots)).
    + rewrite U32. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS _ _ (pPS cx fp) 0 8 (SLit 0) 0); [reflexivity | zside | zside |].
      rewrite Z.add_0_r. exact Hnull.
  - apply pairwise_disjoint_of_extents. unfold r1_rs, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U32.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. rewrite Hps. repeat split; lia. }
clear HEdef EL.
assert (SHOK : sh_ok SEGS TBx [] E (mrestrict (w_H W3) (ms_mem ms3))) by constructor.
paj_run_tok RUN HS HJ SHOK TBspan;
  [ unfold r1_rs; cbn [ss_mem]; apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_nil |].
assert (HFm : ms_mem ms = ms_mem ms3).
{ refine (frame_of_ro E r1_rs _ _ _ HF). intros r Hr1. unfold r1_rs in Hr1. cbn [In] in Hr1.
  destruct Hr1 as [<- | [<- | []]]; cbn [YP09.r_wlo YP09.r_whi]; lia. }
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19. prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21.
prreg HS (22%bv : bv 5) Q22. prreg HS (23%bv : bv 5) Q23. prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
rewrite pa_sigma_pcap_source_open.
assert (Hsp : spZ (ms_regs ms) = c_sp1 cx) by (unfold spZ at 1; rewrite Q2, E2, Rsp; unfold w64; apply unsigned_lit_small; lia).
assert (Hs8 : rdword (aview SEGS (w_H W3) (ms_mem ms)) (spZ (c_regs cx) - 8) = Some (raZ (c_regs cx)))
  by (rewrite HFm; exact (proj1 Hsaved)).
assert (Hs16 : rdword (aview SEGS (w_H W3) (ms_mem ms)) (spZ (c_regs cx) - 16) = Some (s0Z (c_regs cx))).
{ rewrite HFm. pose proof (proj2 Hsaved 0 ltac:(lia)) as H0.
  replace (spZ (c_regs cx) - 16 - 8 * 0) with (spZ (c_regs cx) - 16) in H0 by lia. exact H0. }
eapply SRr_bind.
{ eapply (OPENS LLVMF_STK (spZ (c_regs cx)) [sink_token] (c_ly cx) (c_S cx) (c_W cx) memS (c_md cx) [(PE_CID, fp)]
    ly3 S3 W3 (ms_mem ms) _ k (ms_regs ms) (pch cx) (pPS cx fp) (p_nF cx) bb (c_M cx) (p_C cx) PE_CID fp HJ).
  - exact (aro_now cx memS _ ly3 S3 W3 (ms_mem ms) _ k HB HJ Hag).
  - rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - unfold raZ. rewrite Q1, unsigned_lit_small by lia. lia.
  - rewrite Q3, E3, Rgp. exact Hgp0.
  - rewrite Q4, E4, Rtp. exact Htp0.
  - rewrite Q10, E32. reflexivity.
  - rewrite Q11, EO3. reflexivity.
  - rewrite Hsp. unfold s0Z at 1. rewrite Q8, E8, Rs0. unfold w64. rewrite unsigned_lit_small by lia.
    exact (pch_achain cx _ memS ly3 S3 W3 (ms_mem ms) _ k HB HJ Hag Hs8 Hs16).
  - unfold raZ. rewrite Q1, unsigned_lit_small by lia.
    unfold pch, spine. destruct (Z.ltb_spec (spZ (c_regs cx) + 16) (ly_top (c_ly cx))) as [Ht|Ht].
    + cbn [map]. rewrite HraL. exact (proj1 HCTX).
    + cbn [map]. exact (proj2 HCTX).
  - rewrite Hsp. apply Z.mod_divide; [lia|]. apply Z.mod_divide in Hs1m; [|lia]. destruct Hs1m as [q Hq]. exists (2 * q). lia.
  - rewrite Hsp, TPCAP_SOURCE_OPEN_STK_val. unfold LLVMF_STK. lia.
  - rewrite Hsp. lia.
  - rewrite Hsp, Etop. lia.
  - rewrite Hfrs. cbn [length Z.of_nat]. lia.
  - left. reflexivity.
  - rewrite Efa, Hps. lia.
  - rewrite Efa, Hps. change (fs_frame_bytes PE_CID) with 128. lia.
  - rewrite Hps. lia.
  - exact Hps8.
  - rewrite HFm. apply zero_shadow_range; [exact Hps8 | reflexivity |].
    intros i Hi. change (24 / 8) with 3 in Hi.
    rewrite Hps, shadow_of_addr_aligned_off by (apply Z.mod_divide; [lia|]; apply Z.mod_divide in Hfa64; [|lia];
      destruct Hfa64 as [q Hq]; exists (8 * q); lia).
    change (32 / 8) with 4.
    assert (Hi3 : i = 0 \/ i = 1 \/ i = 2) by lia.
    destruct Hi3 as [-> | [-> | ->]].
    + replace (shadow_of_addr SHADOW_OFF (pF cx fp) + 4 + 0) with (pSH cx fp + Z.of_nat 4) by (unfold pSH; lia).
      exact (Hsh 4%nat ltac:(rewrite Hlen; unfold PE_NSH; lia)).
    + replace (shadow_of_addr SHADOW_OFF (pF cx fp) + 4 + 1) with (pSH cx fp + Z.of_nat 5) by (unfold pSH; lia).
      exact (Hsh 5%nat ltac:(rewrite Hlen; unfold PE_NSH; lia)).
    + replace (shadow_of_addr SHADOW_OFF (pF cx fp) + 4 + 2) with (pSH cx fp + Z.of_nat 6) by (unfold pSH; lia).
      exact (Hsh 6%nat ltac:(rewrite Hlen; unfold PE_NSH; lia)).
  - exists sink_token. split; [left; reflexivity|]. unfold sink_token. cbn [fst snd]. lia.
  - apply HROI. exact (aro_now cx memS _ ly3 S3 W3 (ms_mem ms) _ k HB HJ Hag).
  - rewrite HFm. exact (proj1 (HPATH ly3 S3 W3 (ms_mem ms3) md3 HAR)).
  - rewrite HFm. exact (proj2 (HPATH ly3 S3 W3 (ms_mem ms3) md3 HAR)).
  - rewrite HFm. exact (proj2 Hglob).
  - rewrite HFm. exact (proj1 Hglob).
  - lia.
  - rewrite HFm. exact Hsrc.
  - symmetry. exact ELC.
  - lia.
  - intros _. split; [exact Hbin|]. split; [rewrite HFm; exact Hcopy|].
    exact (garr8_bytes_ok SEGS _ _ _ Hcopy).
  - exact (meta_now cx memS _ ly3 S3 W3 (ms_mem ms) _ k HB HJ Hag).
  - unfold EV_OPEN, EV_FUZZ_FOPEN, EV_LIB in *. lia.
  - rewrite EBB. unfold SRC_FILE_BLOCK, LIVE_LIB in *. lia.
  - apply (mok_station MT (c_S cx) S3 (c_T cx) acc (mo_malloc MT SRC_FILE_BLOCK) MLAWS Hmok Hmo
      (mo_malloc_nonneg MT MLAWS SRC_FILE_BLOCK ltac:(unfold SRC_FILE_BLOCK; lia))).
    pose proof (PA_K12_need MT MLAWS cx) as Hn. pose proof (mo_free_nonneg MT MLAWS).
    unfold PA_K12, PA_K11, PA_K9, PA_K7 in *. lia.
  - exact (proj1 HFMU).
  - exact (proj2 HFMU). }
cbv beta. intros W2 c2 Hwle (ly2 & S2 & regs2 & mem2 & md2 & -> & HP2 & Hfr2 & Hfd2 & Hfs2 & HK & Hmle & Hz12 & Hz16 &
  Hz20 & Harm).
rewrite Q1.
destruct Harm as [(HJ2 & Ha0 & _ & hh & Hh4096 & Hh16 & Hbl2 & Hpf2 & Hpsw2 & Hsrc2 & Hmle2) |
                  (_ & _ & Hbad & _)]; [| rewrite goodZ_good, Hgood in Hbad; discriminate Hbad].
destruct HK as (K1 & K2 & K3 & K4 & K5 & K6).
assert (Hfoot : forall a, hfoot cx fp a -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W3) (ms_mem ms3) a).
{ intros a Ha. rewrite <- HFm.
  refine (foot_kept cx fp ly3 S3 W3 (ms_mem ms) W2 mem2 _ _ (fun a => pPS cx fp <= a < pPS cx fp + 22) HB
    (fun a Ha1 Ha2 _ => K1 a Ha1 Ha2) K2 K4 _
    Hfin Efa (input_block cx ly3 S3 _ HB Hperm) _ a Ha); [rewrite Hsp; lia|].
  intros x Hx Hw.
  exact (frame_off_hfoot cx fp ly3 S3 W3 (ms_mem ms3) md3 _ (pPS cx fp) 22 HB HAR Hperm Hfin Efa
    ltac:(rewrite Hps; lia) ltac:(rewrite Hps; lia) x Hx Hw). }
destruct (tail_kept cx fp W3 ms3 W2 (mkst regs2 (Z_to_bv 64 (BASE + PP_K7)) mem2 (seg_rom SEGS)) PSH_ts Hfoot
  Hsaved Hhdr Hsh Hlen Hin Hslots) as (T1 & T2 & T3 & T4 & T5).
assert (P : forall r : Z, acallee_saved r -> getr regs2 (Z_to_bv 5 r) = getr (ms_regs ms) (Z_to_bv 5 r)) by exact HP2.
eapply (NEXT cx fp (k + EV_FUZZ_FOPEN) (acc + mo_malloc MT SRC_FILE_BLOCK) ly2 S2 W2
  (mkst regs2 (Z_to_bv 64 (BASE + PP_K7)) mem2 (seg_rom SEGS)) md2 HB).
- exact (gx_pack0 cx _ memS _ _ _ _ _ _ HJ2 Hag).
- rewrite Hfr2. exact Hfrs.
- exact (mle_station MT _ _ _ _ _ MLAWS Hmo Hmle2).
- unfold GI_K7, p_cut. exists bb, bf, hh.
  split; [|split; [exact Hn26 | split; [exact Hgood | split; [|split; [|split; [|split; [|split; [|split; [|split;
    [|split; [|split; [|split]]]]]]]]]]]].
  + split; [|split; [unfold EV_FUZZ_FOPEN; lia | split; [|split; [|split]]]].
    * unfold pe_body. cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr mkst ms_regs].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|]. split; [reflexivity|].
      split; [|split; [exact T1 | split; [exact T2 | split; [exact T3 | split; [exact Hlen | exact T4]]]]].
      unfold pregs. cbn [ms_regs mkst].
      split; [transitivity (getr (ms_regs ms) 2); [exact (P 2 ltac:(unfold acallee_saved; lia)) | rewrite Q2, E2; exact Rsp]|].
      split; [transitivity (getr (ms_regs ms) 8); [exact (P 8 ltac:(unfold acallee_saved; lia)) | rewrite Q8, E8; exact Rs0]|].
      split; [transitivity (getr (ms_regs ms) 9); [exact (P 9 ltac:(unfold acallee_saved; lia)) | rewrite Q9, E9; exact Rs1]|].
      split; [transitivity (getr (ms_regs ms) 27); [exact (P 27 ltac:(unfold acallee_saved; lia)) | rewrite Q27, E27; exact Rs11]|].
      split; [transitivity (getr (ms_regs ms) 3); [exact (P 3 ltac:(unfold acallee_saved; lia)) | rewrite Q3, E3; exact Rgp]|].
      transitivity (getr (ms_regs ms) 4); [exact (P 4 ltac:(unfold acallee_saved; lia)) | rewrite Q4, E4; exact Rtp].
    * unfold PA_K7. pose proof (mo_malloc_nonneg MT MLAWS SRC_FILE_BLOCK ltac:(unfold SRC_FILE_BLOCK; lia)). lia.
    * rewrite Hbl2. eapply Permutation_trans; [apply (Permutation_app_tail [(hh, SRC_FILE_BLOCK)] Hperm)|].
      first [rewrite <- app_assoc | rewrite app_assoc]; cbn [app]; apply Permutation_refl.
    * rewrite Hfd2. rewrite (proj1 (fs_wvb md3 mat)). exact Hfds.
    * rewrite Hfs2. rewrite (proj2 (fs_wvb md3 mat)). exact Hfs.
  + cbn [ms_regs mkst]. exact Ha0.
  + cbn [ms_regs mkst]. transitivity (getr (ms_regs ms) 18); [exact (P 18 ltac:(unfold acallee_saved; lia)) | rewrite Q18, E32; reflexivity].
  + cbn [ms_regs mkst]. transitivity (getr (ms_regs ms) 19); [exact (P 19 ltac:(unfold acallee_saved; lia)) | rewrite Q19, E19; exact R19].
  + cbn [ms_regs mkst]. transitivity (getr (ms_regs ms) 20); [exact (P 20 ltac:(unfold acallee_saved; lia)) | rewrite Q20, E20; exact R20].
  + cbn [ms_regs mkst]. transitivity (getr (ms_regs ms) 21); [exact (P 21 ltac:(unfold acallee_saved; lia)) | rewrite Q21, E21; exact R21].
  + cbn [ms_regs mkst]. transitivity (getr (ms_regs ms) 22); [exact (P 22 ltac:(unfold acallee_saved; lia)) | rewrite Q22, E22; exact R22].
  + cbn [ms_regs mkst]. transitivity (getr (ms_regs ms) 23); [exact (P 23 ltac:(unfold acallee_saved; lia)) | rewrite Q23, E23; exact R23].
  + cbn [ms_regs mkst]. transitivity (getr (ms_regs ms) 26); [exact (P 26 ltac:(unfold acallee_saved; lia)) | rewrite Q26, E26; exact R26].
  + exact T5.
  + unfold p_psopen, pval. cbn [ms_mem mkst]. split; [exact Hpf2|]. rewrite <- swZ_sw. exact Hpsw2.
  + split; [|cbn [ms_mem mkst]; exact Hsrc2].
    unfold p_psfresh, pval. cbn [ms_mem mkst].
    split; [exact Hz12|]. split; [exact Hz16|]. split; [exact Hz20|].
    unfold p_pspad. cbn [ms_mem mkst]. apply (garr8_frame SEGS _ _ _ _ Hpad).
    intros a Ha. cbn [length Z.of_nat] in Ha. apply (mbyte_of_aview SEGS). rewrite <- HFm.
    apply (K4 PE_CID fp a Hfin); [|cbv beta; lia].
    left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite Efa. change (fs_frame_bytes PE_CID) with 128.
    rewrite Hps in Ha. lia.
Qed.

(* ---- R2: PP_K7 0x810c8 -> pcap_source_next of the second reader (0x810dc) -> PP_K8 0x810e0 ----------------------
   bnez a0 0x810c8 (the second open's answer, 0: not taken); mv a0,s2 (ps); mv a1,s6 (buf); mv a2,s5 (cap);
   mv a3,zero (no timestamp cell); jal pcap_source_next. The reader is open at 24 (GI_K7), so the statement's open
   arm: the walk from 24 answers p_first and leaves the stream at p_pos (p_q 24). *)
Lemma tail_R2 : pe_from SK B MT KS POST (GI_K8 B MT KS) -> pe_from SK B MT KS POST (GI_K7 B MT KS).
Proof.
intros NEXT cx fp k acc ly3 S3 W3 ms3 md3 HB HJ Hfrs Hmo HG.
destruct HG as (bb & bf & hh & (Hbody & Hk & Hacc & Hperm & Hfds & Hfs) & Hn26 & Hgood & R10 & R18 & R19 & R20 & R21 &
  R22 & R23 & R26 & Hslots & (Hpsf & Hpsw) & (Hlol & Hlvt & Hlvid & Hpad) & Hsrc).
destruct Hbody as (Hpc & Hresv & Hsvc & Hrom & Hfrg & Hfcsr & Hregs & Hsaved & Hhdr & Hsh & Hlen & Hin).
pose proof (tail_geo cx HB) as (Hal & Hs1m & Hs1b & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
unfold LLVMF_STK in Hslo, Hbot.
pose proof HB as ((HAR0 & Hrok & Hra4 & Hgp0 & Htp0 & _) & HraL & _ & _ & _ & _ & _ & Hev & _ & _ & _ & _ & _ & _ &
  _ & _ & Hmok & Hneed & HGX & HGD & _ & _ & Hftr).
destruct (gx_open _ _ _ _ _ _ _ _ HJ) as (memS & HJi & Hag). clear HJ. rename HJi into HJ.
pose proof HJ as (HAR & Hly & _).
destruct Hregs as (Rsp & Rs0 & Rs1 & Rs11 & Rgp & Rtp).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as (HB0 & HB1 & HB2). pose proof (pa_base_lo (PL := PL_pcap) (PI := PI)) as HBLO.
pose proof (p_sizes cx) as (Hsz1 & Hsz2 & Hsz3).
pose proof (p_good_len cx Hgood) as H24.
destruct (lay_eqs _ _ _ Hly) as (EF & Etop & Eslo & Eshi).
assert (Efa : frame_addr ly3 PE_CID fp = pF cx fp) by (unfold pF, frame_addr; rewrite EF; reflexivity).
assert (Hfin : In (PE_CID, fp) (frames S3)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 PE_CID fp HAR Hfin) as (Hf4096 & Hfceil & Hfapp).
rewrite Efa in Hf4096, Hfceil, Hfapp. change (fs_frame_bytes PE_CID) with 128 in Hfceil, Hfapp.
destruct (frame_al64 SEGS B ly3 S3 W3 (ms_mem ms3) md3 PE_CID fp HAR Hfin) as (Hfa64 & _ & _). rewrite Efa in Hfa64.
assert (Hbin : In (bb, p_nF cx) (ablocks B ly3 S3))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; right; left; reflexivity).
assert (Hfbin : In (bf, p_bn cx) (ablocks B ly3 S3))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; right; right; left; reflexivity).
assert (Hhin : In (hh, SRC_FILE_BLOCK) (ablocks B ly3 S3))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; right; right; right; left; reflexivity).
assert (Hfbout : ~ In (bf, p_bn cx) (ablocks B (c_ly cx) (c_S cx)))
  by (refine (notin_prefix _ _ _ _ (ablocks_nodup _ _ _ _ _ HAR) Hperm _); right; left; reflexivity).
assert (Hhout : ~ In (hh, SRC_FILE_BLOCK) (ablocks B (c_ly cx) (c_S cx)))
  by (refine (notin_prefix _ _ _ _ (ablocks_nodup _ _ _ _ _ HAR) Hperm _); right; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ hh SRC_FILE_BLOCK HAR Hhin) as (_ & Hh4096 & Hhceil & _ & _ & _ & _).
change (req_size SRC_FILE_BLOCK) with 1304 in Hhceil.
destruct (al_blocks _ _ LAWS _ _ _ _ _ bf (p_bn cx) HAR Hfbin) as (_ & Hf4096' & Hfbceil & _ & Hfbpres & _ & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ bb (p_nF cx) HAR Hbin) as (_ & Hb4096 & Hbceil & _ & _ & _ & _).
pose proof (req_size_pos (p_bn cx) ltac:(lia)) as [Hrqf1 Hrqf2].
pose proof (req_size_pos (p_nF cx) ltac:(lia)) as [Hrqb1 Hrqb2].
pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ bf (p_bn cx) PE_CID fp HAR Hfbin Hfin) as Dff.
pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ hh SRC_FILE_BLOCK PE_CID fp HAR Hhin Hfin) as Dhf.
pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ bb (p_nF cx) PE_CID fp HAR Hbin Hfin) as Dbf.
unfold zdisjoint in Dff, Dhf, Dbf. cbn [fst snd] in Dff, Dhf, Dbf. rewrite Efa in Dff, Dhf, Dbf.
change (fs_frame_bytes PE_CID) with 128 in Dff, Dhf, Dbf. change (req_size SRC_FILE_BLOCK) with 1304 in Dhf.
assert (HL : List.NoDup [(bb, p_nF cx); (bf, p_bn cx); (hh, SRC_FILE_BLOCK)])
  by exact (List.NoDup_app_remove_l _ _ (Permutation_NoDup Hperm (ablocks_nodup _ _ _ _ _ HAR))).
assert (Hne_fb : (bf, p_bn cx) <> (bb, p_nF cx)) by (intros Heq; inversion HL as [|x l Hx _]; apply Hx; rewrite Heq; left; reflexivity).
assert (Hne_fh : (bf, p_bn cx) <> (hh, SRC_FILE_BLOCK)).
{ intros Heq. inversion HL as [|x l _ HL2]. inversion HL2 as [|y l2 Hy _]. apply Hy. rewrite Heq. left. reflexivity. }
assert (Dfh : bf + req_size (p_bn cx) <= hh \/ hh + 1304 <= bf).
{ pose proof (sep_blocks SEGS B LAWS _ _ _ _ _ _ _ _ _ HAR Hfbin Hhin Hne_fh) as D. unfold zdisjoint in D. cbn [fst snd] in D.
  change (req_size SRC_FILE_BLOCK) with 1304 in D. exact D. }
assert (Dfb : bf + req_size (p_bn cx) <= bb \/ bb + req_size (p_nF cx) <= bf).
{ pose proof (sep_blocks SEGS B LAWS _ _ _ _ _ _ _ _ _ HAR Hfbin Hbin Hne_fb) as D. unfold zdisjoint in D. cbn [fst snd] in D. exact D. }
assert (ELC : Z.of_nat (length (p_C cx)) = p_nF cx) by (unfold p_C, p_nF; rewrite length_map; reflexivity).
assert (EBN : nx_bufn (p_cap cx) = p_bn cx) by reflexivity.
(* the symbolic state at 0x810c8 *)
pose proof (entry0 PP_K7 ms3 W3 Hpc Hresv Hsvc Hrom Hfrg Hfcsr) as HS.
remember (Eimg (Ereg (ms_regs ms3) [])) as E eqn:HEdef.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg (ms_regs ms3) []) n)
  by (intros n Hn; subst E; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr (ms_regs ms3) 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr (ms_regs ms3) 3) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr (ms_regs ms3) 4) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 4 4%bv eq_refl)).
assert (E8 : ew E 8 = getr (ms_regs ms3) 8) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 8 8%bv eq_refl)).
assert (E9 : ew E 9 = getr (ms_regs ms3) 9) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 9 9%bv eq_refl)).
assert (E10 : ew E 10 = getr (ms_regs ms3) 10) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 10 10%bv eq_refl)).
assert (E18 : ew E 18 = getr (ms_regs ms3) 18) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 18 18%bv eq_refl)).
assert (E19 : ew E 19 = getr (ms_regs ms3) 19) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 19 19%bv eq_refl)).
assert (E20 : ew E 20 = getr (ms_regs ms3) 20) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 20 20%bv eq_refl)).
assert (E21 : ew E 21 = getr (ms_regs ms3) 21) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 21 21%bv eq_refl)).
assert (E22 : ew E 22 = getr (ms_regs ms3) 22) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 22 22%bv eq_refl)).
assert (E23 : ew E 23 = getr (ms_regs ms3) 23) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 23 23%bv eq_refl)).
assert (E26 : ew E 26 = getr (ms_regs ms3) 26) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 26 26%bv eq_refl)).
assert (E27 : ew E 27 = getr (ms_regs ms3) 27) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 27 27%bv eq_refl)).
assert (SHOK : sh_ok SEGS TBx [] E (mrestrict (w_H W3) (ms_mem ms3))) by constructor.
clear HEdef EL.
(* 0x810c8 bnez a0 to the abort at 0x81340: the second open answered 0 *)
psrr_branch_tok RUN BR HS SHOK TBspan.
{ exfalso. rewrite branch_ne_U in Hc. unfold U in Hc. cbn [sv_denot] in Hc.
  rewrite E10, R10 in Hc. vm_compute in Hc. discriminate Hc. }
clear Hc.
(* 0x810cc mv a0,s2; mv a1,s6; mv a2,s5; mv a3,zero; 0x810dc jal pcap_source_next *)
paj_run_tok RUN HS HJ SHOK TBspan; [apply awr_ok_nil |].
assert (HFm : ms_mem ms = ms_mem ms3) by exact (frame_of_nil _ _ _ HF).
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
prreg HS (12%bv : bv 5) Q12. prreg HS (13%bv : bv 5) Q13. prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19.
prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21. prreg HS (22%bv : bv 5) Q22. prreg HS (23%bv : bv 5) Q23.
prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
rewrite pa_sigma_pcap_source_next.
assert (Hsp : spZ (ms_regs ms) = c_sp1 cx) by (unfold spZ at 1; rewrite Q2, E2, Rsp; unfold w64; apply unsigned_lit_small; lia).
assert (Hps : pPS cx fp = pF cx fp + 32) by reflexivity.
assert (Hps8 : pPS cx fp mod 8 = 0).
{ rewrite Hps. apply Z.mod_divide; [lia|]. apply Z.mod_divide in Hfa64; [|lia]. destruct Hfa64 as [q Hq]. exists (8 * q + 4). lia. }
assert (Hs8 : rdword (aview SEGS (w_H W3) (ms_mem ms)) (spZ (c_regs cx) - 8) = Some (raZ (c_regs cx)))
  by (rewrite HFm; exact (proj1 Hsaved)).
assert (Hs16 : rdword (aview SEGS (w_H W3) (ms_mem ms)) (spZ (c_regs cx) - 16) = Some (s0Z (c_regs cx))).
{ rewrite HFm. pose proof (proj2 Hsaved 0 ltac:(lia)) as H0.
  replace (spZ (c_regs cx) - 16 - 8 * 0) with (spZ (c_regs cx) - 16) in H0 by lia. exact H0. }
destruct (garr8_of_present SEGS (rdW W3 (ms_mem ms)) bf (Z.to_nat (p_bn cx))) as (bj & Hbjl & Hbj).
{ intros a Ha. rewrite Z2Nat.id in Ha by lia. apply present_rdW. rewrite HFm. apply (Hfbpres a). lia. }
assert (Hwr : forall q n, (forall a, q <= a < q + n -> awr_byte LLVMF_STK (spZ (c_regs cx)) [sink_token]
    (ablocks B (c_ly cx) (c_S cx)) (ablocks B ly3 S3) ly3 [(PE_CID, fp)] a) ->
  (forall a, q <= a < q + n -> a < alloc_ceiling) ->
  forall a, q <= a < q + n -> awr_byte LLVMF_STK (spZ (c_regs cx)) [sink_token] (ablocks B (c_ly cx) (c_S cx))
    (ablocks B ly3 S3) ly3 [(PE_CID, fp)] a /\ ~ (spZ (ms_regs ms) - NX_STK <= a < spZ (ms_regs ms))).
{ intros q n H1 H2 a Ha. split; [exact (H1 a Ha)|]. pose proof (H2 a Ha). rewrite Hsp.
  assert (HNX : NX_STK = 8496) by reflexivity. rewrite HNX. lia. }
eapply SRr_bind.
{ eapply (NEXTS LLVMF_STK (spZ (c_regs cx)) [sink_token] (c_ly cx) (c_S cx) (c_W cx) memS (c_md cx) [(PE_CID, fp)]
    ly3 S3 W3 (ms_mem ms) _ k (ms_regs ms) (pPS cx fp) bf (p_cap cx) 0 hh bb 24 (p_swz cx) 0 0 0 0 (c_M cx) PE_CID fp
    (p_C cx) bj [165; 165] (pch cx) HJ).
  - exact (aro_now cx memS _ ly3 S3 W3 (ms_mem ms) _ k HB HJ Hag).
  - rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - unfold raZ. rewrite Q1, unsigned_lit_small by lia. lia.
  - rewrite Q3, E3, Rgp. exact Hgp0.
  - rewrite Q4, E4, Rtp. exact Htp0.
  - rewrite Q10, E18, R18. reflexivity.
  - rewrite Q11, E22, R22. reflexivity.
  - rewrite Q12, E21, R21. reflexivity.
  - rewrite Q13. reflexivity.
  - rewrite Hsp. apply Z.mod_divide; [lia|]. apply Z.mod_divide in Hs1m; [|lia]. destruct Hs1m as [q Hq]. exists (2 * q). lia.
  - rewrite Hsp. assert (HNX : NX_STK = 8496) by reflexivity. rewrite HNX. unfold LLVMF_STK. lia.
  - rewrite Hsp. lia.
  - rewrite Hsp. unfold s0Z at 1. rewrite Q8, E8, Rs0. unfold w64. rewrite unsigned_lit_small by lia.
    exact (pch_achain cx _ memS ly3 S3 W3 (ms_mem ms) _ k HB HJ Hag Hs8 Hs16).
  - rewrite Hfrs. vm_compute. reflexivity.
  - unfold PS_F_OFF. rewrite Z.add_0_r, HFm. exact Hpsf.
  - lia.
  - exact Hps8.
  - rewrite Hps. lia.
  - unfold PS_LEN. rewrite Hps. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hfapp. lia.
  - unfold amem_range, PS_LEN. rewrite Hps. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hfapp. lia.
  - left. reflexivity.
  - rewrite Efa, Hps. lia.
  - rewrite Efa, Hps. change (fs_frame_bytes PE_CID) with 128. unfold PS_LEN. lia.
  - rewrite HFm. apply zero_shadow_range; [exact Hps8 | reflexivity |].
    intros i Hi. unfold PS_LEN in Hi. change (24 / 8) with 3 in Hi.
    rewrite Hps, shadow_of_addr_aligned_off by (apply Z.mod_divide; [lia|]; apply Z.mod_divide in Hfa64; [|lia];
      destruct Hfa64 as [q Hq]; exists (8 * q); lia).
    change (32 / 8) with 4.
    assert (Hi3 : i = 0 \/ i = 1 \/ i = 2) by lia.
    destruct Hi3 as [-> | [-> | ->]].
    + replace (shadow_of_addr SHADOW_OFF (pF cx fp) + 4 + 0) with (pSH cx fp + Z.of_nat 4) by (unfold pSH; lia).
      exact (Hsh 4%nat ltac:(rewrite Hlen; unfold PE_NSH; lia)).
    + replace (shadow_of_addr SHADOW_OFF (pF cx fp) + 4 + 1) with (pSH cx fp + Z.of_nat 5) by (unfold pSH; lia).
      exact (Hsh 5%nat ltac:(rewrite Hlen; unfold PE_NSH; lia)).
    + replace (shadow_of_addr SHADOW_OFF (pF cx fp) + 4 + 2) with (pSH cx fp + Z.of_nat 6) by (unfold pSH; lia).
      exact (Hsh 6%nat ltac:(rewrite Hlen; unfold PE_NSH; lia)).
  - intros _. unfold nx_ps_at, PS_F_OFF, PS_SW_OFF, PS_OL_OFF, PS_VT_OFF, PS_VID_OFF. rewrite !HFm.
    rewrite Z.add_0_r. split; [exact Hpsf|]. split; [exact Hpsw|]. split; [exact Hlol|]. split; [exact Hlvt|].
    split; [exact Hlvid|]. split; [exact Hpad | reflexivity].
  - intros _. exact (p_swz01 cx).
  - intros _. lia.
  - intros _. refine (Hwr (pPS cx fp) PS_LEN _ _).
    + intros a Ha. apply (awr_ownframe _ _ _ _ _ _ cx fp a Efa). left. unfold PS_LEN in Ha. lia.
    + intros a Ha. unfold PS_LEN in Ha. lia.
  - intros _. rewrite EBN.
    assert (ERS : req_size (p_bn cx) = p_bn cx)
      by (unfold req_size; destruct (Z.eqb_spec (p_bn cx) 0) as [E0|_]; [lia | reflexivity]).
    rewrite ERS in Dff. split; [exact Hfbin|]. split; [lia|]. split; [lia|].
    split; [exact Hbj|]. split; [rewrite Hbjl, Z2Nat.id by lia; reflexivity|]. split; [unfold NX_CAP_MAX; lia|].
    split; [|unfold PS_LEN; rewrite Hps; lia].
    refine (Hwr bf (p_bn cx) _ _).
    + intros a Ha. right; right; left. exists bf, (p_bn cx). split; [exact Hfbin|]. split; [exact Hfbout | lia].
    + intros a Ha. lia.
  - intros _ Hts. exfalso. apply Hts. reflexivity.
  - intros _. rewrite ELC. split; [exact Hhin|]. split; [exact Hbin|].
    split; [rewrite HFm; exact Hsrc|]. split; [lia|]. split; [lia|].
    rewrite EBN. assert (ERS : req_size (p_bn cx) = p_bn cx)
      by (unfold req_size; destruct (Z.eqb_spec (p_bn cx) 0) as [E0|_]; [lia | reflexivity]).
    rewrite ERS in Dfh, Dfb.
    change SRC_FILE_BLOCK with 1304. split; [lia|]. split; [pose proof Hrqb2; lia|].
    split; [unfold PS_LEN; rewrite Hps; lia|].
    split; [unfold PS_LEN; rewrite Hps; lia|]. split; [intros Hts; exfalso; apply Hts; reflexivity|].
    intros x Hx. unfold asource_fp in Hx. apply inFP_cons in Hx as [Hx|Hx]; [|left; exact Hx].
    right. exists hh, SRC_FILE_BLOCK. split; [exact Hhin|]. split; [exact Hhout|]. change (req_size SRC_FILE_BLOCK) with 1304.
    unfold SRC_FILE_BLOCK in Hx. lia.
  - intros _. exact (meta_now cx memS _ ly3 S3 W3 (ms_mem ms) _ k HB HJ Hag). }
cbv beta. intros W2 c2 Hwle (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hbl2 & Hfr2 & Hmle & Hfd2 & Hfs2 & Hfin2).
destruct Hfin2 as [(Hh0 & _) | (_ & Ha0 & HK & Hsrc2 & Hps2 & _ & _)]; [lia|].
rewrite Q1.
destruct HK as (K1 & K2 & K3 & K4 & K5 & K6).
assert (Hfoot : forall a, hfoot cx fp a -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W3) (ms_mem ms3) a).
{ intros a Ha. rewrite <- HFm.
  refine (foot_kept cx fp ly3 S3 W3 (ms_mem ms) W2 mem2 _ _ (nx_wrset (pPS cx fp) bf (p_cap cx) 0 hh) HB K1 K2 K4 _
    Hfin Efa (input_block cx ly3 S3 _ HB Hperm) _ a Ha); [rewrite Hsp; lia|].
  intros x Hx Hw. unfold nx_wrset in Hw. rewrite EBN in Hw.
  destruct Hw as [Hw | [Hw | [[Hw _] | [_ Hw]]]].
  - exact (frame_off_hfoot cx fp ly3 S3 W3 (ms_mem ms3) md3 _ (pPS cx fp) PS_LEN HB HAR Hperm Hfin Efa
      ltac:(rewrite Hps; lia) ltac:(rewrite Hps; unfold PS_LEN; lia) x Hx Hw).
  - exact (block_off_hfoot cx fp ly3 S3 W3 (ms_mem ms3) md3 _ bf (p_bn cx) HB HAR Hperm Hfbin Hfbout Hfin Efa x Hx
      ltac:(lia)).
  - exact (Hw eq_refl).
  - exact (block_off_hfoot cx fp ly3 S3 W3 (ms_mem ms3) md3 _ hh SRC_FILE_BLOCK HB HAR Hperm Hhin Hhout Hfin Efa x Hx Hw). }
destruct (tail_kept cx fp W3 ms3 W2 (mkst regs2 (Z_to_bv 64 (BASE + PP_K8)) mem2 (seg_rom SEGS)) PSH_ts Hfoot
  Hsaved Hhdr Hsh Hlen Hin Hslots) as (T1 & T2 & T3 & T4 & T5).
assert (P : forall r : Z, acallee_saved r -> getr regs2 (Z_to_bv 5 r) = getr (ms_regs ms) (Z_to_bv 5 r)) by exact HP2.
eapply (NEXT cx fp (k + EV_NEXT) (acc + 0) ly2 S2 W2 (mkst regs2 (Z_to_bv 64 (BASE + PP_K8)) mem2 (seg_rom SEGS)) md2 HB).
- exact (gx_pack0 cx _ memS _ _ _ _ _ _ HJ2 Hag).
- rewrite Hfr2. exact Hfrs.
- exact (mle_station MT _ _ _ _ _ MLAWS Hmo Hmle).
- unfold GI_K8, p_cut. exists bb, bf, hh.
  split; [|split; [exact Hn26 | split; [exact Hgood | split; [|split; [|split; [|split; [|split; [|split; [|split;
    [|split; [|split; [|split]]]]]]]]]]]].
  + split; [|split; [unfold EV_NEXT; lia | split; [lia | split; [|split]]]].
    * unfold pe_body. cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr mkst ms_regs].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|]. split; [reflexivity|].
      split; [|split; [exact T1 | split; [exact T2 | split; [exact T3 | split; [exact Hlen | exact T4]]]]].
      unfold pregs. cbn [ms_regs mkst].
      split; [transitivity (getr (ms_regs ms) 2); [exact (P 2 ltac:(unfold acallee_saved; lia)) | rewrite Q2, E2; exact Rsp]|].
      split; [transitivity (getr (ms_regs ms) 8); [exact (P 8 ltac:(unfold acallee_saved; lia)) | rewrite Q8, E8; exact Rs0]|].
      split; [transitivity (getr (ms_regs ms) 9); [exact (P 9 ltac:(unfold acallee_saved; lia)) | rewrite Q9, E9; exact Rs1]|].
      split; [transitivity (getr (ms_regs ms) 27); [exact (P 27 ltac:(unfold acallee_saved; lia)) | rewrite Q27, E27; exact Rs11]|].
      split; [transitivity (getr (ms_regs ms) 3); [exact (P 3 ltac:(unfold acallee_saved; lia)) | rewrite Q3, E3; exact Rgp]|].
      transitivity (getr (ms_regs ms) 4); [exact (P 4 ltac:(unfold acallee_saved; lia)) | rewrite Q4, E4; exact Rtp].
    * rewrite Hbl2. exact Hperm.
    * rewrite Hfd2. rewrite (proj1 (fs_wvb md3 mat)). exact Hfds.
    * rewrite Hfs2. rewrite (proj2 (fs_wvb md3 mat)). exact Hfs.
  + cbn [ms_regs mkst]. rewrite Ha0. unfold nx_res, nx_q. rewrite nxF_pC. reflexivity.
  + cbn [ms_regs mkst]. transitivity (getr (ms_regs ms) 18); [exact (P 18 ltac:(unfold acallee_saved; lia)) | rewrite Q18, E18; exact R18].
  + cbn [ms_regs mkst]. transitivity (getr (ms_regs ms) 19); [exact (P 19 ltac:(unfold acallee_saved; lia)) | rewrite Q19, E19; exact R19].
  + cbn [ms_regs mkst]. transitivity (getr (ms_regs ms) 20); [exact (P 20 ltac:(unfold acallee_saved; lia)) | rewrite Q20, E20; exact R20].
  + cbn [ms_regs mkst]. transitivity (getr (ms_regs ms) 21); [exact (P 21 ltac:(unfold acallee_saved; lia)) | rewrite Q21, E21; exact R21].
  + cbn [ms_regs mkst]. transitivity (getr (ms_regs ms) 22); [exact (P 22 ltac:(unfold acallee_saved; lia)) | rewrite Q22, E22; exact R22].
  + cbn [ms_regs mkst]. transitivity (getr (ms_regs ms) 23); [exact (P 23 ltac:(unfold acallee_saved; lia)) | rewrite Q23, E23; exact R23].
  + cbn [ms_regs mkst]. transitivity (getr (ms_regs ms) 26); [exact (P 26 ltac:(unfold acallee_saved; lia)) | rewrite Q26, E26; exact R26].
  + exact T5.
  + destruct Hps2 as (Hf2 & Hsw2 & _). unfold PS_F_OFF, PS_SW_OFF in Hf2, Hsw2. rewrite Z.add_0_r in Hf2.
    split; [exact Hf2 | exact Hsw2].
  + cbn [ms_mem mkst]. unfold nx_pos, nx_q in Hsrc2. rewrite nxF_pC in Hsrc2. exact Hsrc2.
Qed.


(* ---- R3: PP_K8 0x810e0 -> the check of the second reader's answer -> pcap_source_close 0x810e8 -> PP_K9 ------- *)

Lemma tail_R3 : pe_from SK B MT KS POST (GI_K9 B MT KS) -> pe_from SK B MT KS POST (GI_K8 B MT KS).
Proof.
intros NEXT cx fp k acc ly3 S3 W3 ms3 md3 HB HJ Hfrs Hmo HG.
destruct HG as (bb & bf & hh & (Hbody & Hk & Hacc & Hperm & Hfds & Hfs) & Hn26 & Hgood & R10 & R18 & R19 & R20 & R21 &
  R22 & R23 & R26 & Hslots & (Hpsf & Hpsw) & Hsrc).
destruct Hbody as (Hpc & Hresv & Hsvc & Hrom & Hfrg & Hfcsr & Hregs & Hsaved & Hhdr & Hsh & Hlen & Hin).
pose proof (tail_geo cx HB) as (Hal & Hs1m & Hs1b & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
unfold LLVMF_STK in Hslo, Hbot.
pose proof HB as ((HAR0 & Hrok & Hra4 & Hgp0 & Htp0 & _) & HraL & _ & _ & _ & _ & _ & Hev & _ & _ & _ & _ & _ & _ &
  _ & _ & Hmok & Hneed & HGX & HGD & _ & _ & Hftr).
destruct (gx_open _ _ _ _ _ _ _ _ HJ) as (memS & HJi & Hag). clear HJ. rename HJi into HJ.
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & Hnev & Hk0 & _).
destruct Hregs as (Rsp & Rs0 & Rs1 & Rs11 & Rgp & Rtp).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as (HB0 & HB1 & HB2). pose proof (pa_base_lo (PL := PL_pcap) (PI := PI)) as HBLO.
pose proof (p_sizes cx) as (Hsz1 & Hsz2 & Hsz3).
destruct (lay_eqs _ _ _ Hly) as (EF & Etop & Eslo & Eshi).
assert (Efa : frame_addr ly3 PE_CID fp = pF cx fp) by (unfold pF, frame_addr; rewrite EF; reflexivity).
assert (Hfin : In (PE_CID, fp) (frames S3)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 PE_CID fp HAR Hfin) as (Hf4096 & Hfceil & Hfapp).
rewrite Efa in Hf4096, Hfceil, Hfapp. change (fs_frame_bytes PE_CID) with 128 in Hfceil, Hfapp.
destruct (frame_al64 SEGS B ly3 S3 W3 (ms_mem ms3) md3 PE_CID fp HAR Hfin) as (Hfa64 & _ & _). rewrite Efa in Hfa64.
assert (Hhin : In (hh, SRC_FILE_BLOCK) (ablocks B ly3 S3))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; right; right; right; left; reflexivity).
assert (Hbin : In (bb, p_nF cx) (ablocks B ly3 S3))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; right; left; reflexivity).
assert (Hhout : ~ In (hh, SRC_FILE_BLOCK) (ablocks B (c_ly cx) (c_S cx)))
  by (refine (notin_prefix _ _ _ _ (ablocks_nodup _ _ _ _ _ HAR) Hperm _); right; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ hh SRC_FILE_BLOCK HAR Hhin) as (_ & Hh4096 & Hhceil & _ & _ & _ & _).
change (req_size SRC_FILE_BLOCK) with 1304 in Hhceil.
(* the symbolic state at 0x810e0 *)
pose proof (entry0 PP_K8 ms3 W3 Hpc Hresv Hsvc Hrom Hfrg Hfcsr) as HS.
remember (Eimg (Ereg (ms_regs ms3) [])) as E eqn:HEdef.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg (ms_regs ms3) []) n)
  by (intros n Hn; subst E; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr (ms_regs ms3) 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr (ms_regs ms3) 3) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr (ms_regs ms3) 4) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 4 4%bv eq_refl)).
assert (E8 : ew E 8 = getr (ms_regs ms3) 8) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 8 8%bv eq_refl)).
assert (E9 : ew E 9 = getr (ms_regs ms3) 9) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 9 9%bv eq_refl)).
assert (E10 : ew E 10 = getr (ms_regs ms3) 10) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 10 10%bv eq_refl)).
assert (E18 : ew E 18 = getr (ms_regs ms3) 18) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 18 18%bv eq_refl)).
assert (E19 : ew E 19 = getr (ms_regs ms3) 19) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 19 19%bv eq_refl)).
assert (E20 : ew E 20 = getr (ms_regs ms3) 20) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 20 20%bv eq_refl)).
assert (E21 : ew E 21 = getr (ms_regs ms3) 21) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 21 21%bv eq_refl)).
assert (E22 : ew E 22 = getr (ms_regs ms3) 22) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 22 22%bv eq_refl)).
assert (E23 : ew E 23 = getr (ms_regs ms3) 23) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 23 23%bv eq_refl)).
assert (E26 : ew E 26 = getr (ms_regs ms3) 26) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 26 26%bv eq_refl)).
assert (E27 : ew E 27 = getr (ms_regs ms3) 27) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 27 27%bv eq_refl)).
assert (SHOK : sh_ok SEGS TBx [] E (mrestrict (w_H W3) (ms_mem ms3))) by constructor.
clear HEdef EL.
(* 0x810e0 bne a0,s10 to the abort at 0x81340: both are the reader's first answer *)
psrr_branch_tok RUN BR HS SHOK TBspan.
{ exfalso. rewrite branch_ne_U in Hc. unfold U in Hc. cbn [sv_denot] in Hc.
  rewrite E10, E26, R10, R26, Z.eqb_refl in Hc. discriminate Hc. }
clear Hc.
(* 0x810e4 mv a0,s2; 0x810e8 jal pcap_source_close *)
paj_run_tok RUN HS HJ SHOK TBspan; [apply awr_ok_nil |].
assert (HFm : ms_mem ms = ms_mem ms3) by exact (frame_of_nil _ _ _ HF).
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (10%bv : bv 5) Q10. prreg HS (18%bv : bv 5) Q18.
prreg HS (19%bv : bv 5) Q19. prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21. prreg HS (22%bv : bv 5) Q22.
prreg HS (23%bv : bv 5) Q23. prreg HS (27%bv : bv 5) Q27.
rewrite pa_sigma_pcap_source_close.
assert (Hsp : spZ (ms_regs ms) = c_sp1 cx) by (unfold spZ at 1; rewrite Q2, E2, Rsp; unfold w64; apply unsigned_lit_small; lia).
assert (Hps : pPS cx fp = pF cx fp + 32) by reflexivity.
eapply SRr_bind.
{ eapply (CLOSE LLVMF_STK (spZ (c_regs cx)) [sink_token] (c_ly cx) (c_S cx) (c_W cx) memS (c_md cx) [(PE_CID, fp)]
    ly3 S3 W3 (ms_mem ms) _ k (ms_regs ms) (pPS cx fp) hh bb (c_M cx) (p_pos cx (p_q cx 24)) (p_C cx) PE_CID fp HJ).
  - exact (aro_now cx memS _ ly3 S3 W3 (ms_mem ms) _ k HB HJ Hag).
  - rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - unfold raZ. rewrite Q1, unsigned_lit_small by lia. lia.
  - rewrite Q3, E3, Rgp. exact Hgp0.
  - rewrite Q4, E4, Rtp. exact Htp0.
  - rewrite Q10, E18, R18. reflexivity.
  - rewrite Hsp. apply Z.mod_divide; [lia|]. apply Z.mod_divide in Hs1m; [|lia]. destruct Hs1m as [q Hq]. exists (2 * q). lia.
  - rewrite Hsp. assert (HTS : TPCAP_SOURCE_CLOSE_STK = 16560) by reflexivity. rewrite HTS. unfold LLVMF_STK. lia.
  - rewrite Hsp. lia.
  - left. reflexivity.
  - rewrite Efa, Hps. lia.
  - rewrite Efa, Hps. change (fs_frame_bytes PE_CID) with 128. lia.
  - rewrite Hps. split; [lia|]. apply Z.mod_divide; [lia|]. apply Z.mod_divide in Hfa64; [|lia].
    destruct Hfa64 as [q Hq]. exists (8 * q + 4). lia.
  - rewrite HFm. exact Hpsf.
  - lia.
  - rewrite HFm. apply zero_shadow_range; [rewrite Hps; apply Z.mod_divide; [lia|]; apply Z.mod_divide in Hfa64; [|lia];
      destruct Hfa64 as [q Hq]; exists (8 * q + 4); lia | reflexivity |].
    intros i Hi. change (8 / 8) with 1 in Hi. replace i with 0 by lia. rewrite Z.add_0_r.
    rewrite Hps, shadow_of_addr_aligned_off by (apply Z.mod_divide; [lia|]; apply Z.mod_divide in Hfa64; [|lia];
      destruct Hfa64 as [q Hq]; exists (8 * q); lia).
    change (32 / 8) with 4. exact (Hsh 4%nat ltac:(rewrite Hlen; unfold PE_NSH; lia)).
  - intros _. split; [exact Hhin|]. split.
    { replace (Z.of_nat (length (p_C cx))) with (p_nF cx) by (unfold p_C, p_nF; rewrite length_map; reflexivity). exact Hbin. }
    split; [rewrite HFm; exact Hsrc|]. split; [exact (meta_now cx memS _ ly3 S3 W3 (ms_mem ms) _ k HB HJ Hag)|].
    intros x Hx. unfold asource_fp in Hx. apply inFP_cons in Hx as [Hx|Hx]; [|left; exact Hx].
    right. exists hh, SRC_FILE_BLOCK. split; [exact Hhin|]. split; [exact Hhout|]. change (req_size SRC_FILE_BLOCK) with 1304.
    unfold SRC_FILE_BLOCK in Hx. lia.
  - unfold EV_CLOSE, EV_LIB in *. lia. }
cbv beta. intros W2 c2 Hwle (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hfr2 & Hmle & Hfd2 & Hfs2 & HPm & Hnull & HK & Hsrc2).
rewrite Q1.
assert (Hh0 : hh <> 0) by lia.
unfold tclose_fblk in HPm. destruct (Z.eqb_spec hh 0) as [|_]; [lia|]. cbn [app] in HPm.
destruct (Z.eqb_spec hh 0) as [|_]; [lia|].
destruct (Hsrc2 Hh0) as [Hnone2 Hcopy2].
destruct HK as (K1 & K2 & K3 & K4 & K5 & K6).
assert (Hfoot : forall a, hfoot cx fp a -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W3) (ms_mem ms3) a).
{ intros a Ha. rewrite <- HFm.
  refine (foot_kept cx fp ly3 S3 W3 (ms_mem ms) W2 mem2 _ _
    (fun a => (pPS cx fp <= a < pPS cx fp + 8) \/ (hh <> 0 /\ hh <= a < hh + req_size SRC_FILE_BLOCK)) HB
    (fun a Ha Hn _ => K1 a Ha Hn) K2 K4 _ Hfin Efa (input_block cx ly3 S3 _ HB Hperm) _ a Ha); [rewrite Hsp; lia|].
  intros x Hx [Hx1 | [_ Hx2]].
  - exact (frame_off_hfoot cx fp ly3 S3 W3 (ms_mem ms3) md3 _ (pPS cx fp) 8 HB HAR Hperm Hfin Efa ltac:(rewrite Hps; lia)
      ltac:(rewrite Hps; lia) x Hx Hx1).
  - exact (block_off_hfoot cx fp ly3 S3 W3 (ms_mem ms3) md3 _ hh SRC_FILE_BLOCK HB HAR Hperm Hhin Hhout Hfin Efa x Hx Hx2). }
destruct (tail_kept cx fp W3 ms3 W2 (mkst regs2 (Z_to_bv 64 (BASE + PP_K9)) mem2 (seg_rom SEGS)) PSH_ts Hfoot
  Hsaved Hhdr Hsh Hlen Hin Hslots) as (T1 & T2 & T3 & T4 & T5).
assert (P : forall r : Z, acallee_saved r -> getr regs2 (Z_to_bv 5 r) = getr (ms_regs ms) (Z_to_bv 5 r)) by exact HP2.
eapply (NEXT cx fp (k + EV_CLOSE) (acc + (mo_free MT + mo_free MT)) ly2 S2 W2
  (mkst regs2 (Z_to_bv 64 (BASE + PP_K9)) mem2 (seg_rom SEGS)) md2 HB).
- exact (gx_pack0 cx _ memS _ _ _ _ _ _ HJ2 Hag).
- rewrite Hfr2. exact Hfrs.
- exact (mle_station MT _ _ _ _ _ MLAWS Hmo Hmle).
- unfold GI_K9, p_cut. exists bb, bf.
  split; [|split; [exact Hn26 | split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]]]].
  + split; [|split; [unfold EV_CLOSE; lia | split; [unfold PA_K9; lia | split; [|split]]]].
    * unfold pe_body. cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr mkst ms_regs].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|]. split; [reflexivity|].
      split; [|split; [exact T1 | split; [exact T2 | split; [exact T3 | split; [exact Hlen | exact T4]]]]].
      unfold pregs. cbn [ms_regs mkst].
      split; [transitivity (getr (ms_regs ms) 2); [exact (P 2 ltac:(unfold acallee_saved; lia)) | rewrite Q2, E2; exact Rsp]|].
      split; [transitivity (getr (ms_regs ms) 8); [exact (P 8 ltac:(unfold acallee_saved; lia)) | rewrite Q8, E8; exact Rs0]|].
      split; [transitivity (getr (ms_regs ms) 9); [exact (P 9 ltac:(unfold acallee_saved; lia)) | rewrite Q9, E9; exact Rs1]|].
      split; [transitivity (getr (ms_regs ms) 27); [exact (P 27 ltac:(unfold acallee_saved; lia)) | rewrite Q27, E27; exact Rs11]|].
      split; [transitivity (getr (ms_regs ms) 3); [exact (P 3 ltac:(unfold acallee_saved; lia)) | rewrite Q3, E3; exact Rgp]|].
      transitivity (getr (ms_regs ms) 4); [exact (P 4 ltac:(unfold acallee_saved; lia)) | rewrite Q4, E4; exact Rtp].
    * assert (HP' : Permutation ((hh, SRC_FILE_BLOCK) :: ablocks B ly2 S2)
        ((ablocks B (c_ly cx) (c_S cx) ++ [(bb, p_nF cx); (bf, p_bn cx)]) ++ [(hh, SRC_FILE_BLOCK)])).
      { rewrite <- app_assoc. cbn [app]. exact (Permutation_trans (Permutation_sym HPm) Hperm). }
      pose proof (Permutation_app_inv [] _ _ [] _ HP') as Hq. cbn [app] in Hq. rewrite app_nil_r in Hq. exact Hq.
    * rewrite Hfd2. rewrite (proj1 (fs_wvb md3 mat)). exact Hfds.
    * rewrite Hfs2. rewrite (proj2 (fs_wvb md3 mat)). exact Hfs.
  + cbn [ms_regs mkst]. transitivity (getr (ms_regs ms) 18); [exact (P 18 ltac:(unfold acallee_saved; lia)) | rewrite Q18, E18; exact R18].
  + cbn [ms_regs mkst]. transitivity (getr (ms_regs ms) 19); [exact (P 19 ltac:(unfold acallee_saved; lia)) | rewrite Q19, E19; exact R19].
  + cbn [ms_regs mkst]. transitivity (getr (ms_regs ms) 20); [exact (P 20 ltac:(unfold acallee_saved; lia)) | rewrite Q20, E20; exact R20].
  + cbn [ms_regs mkst]. transitivity (getr (ms_regs ms) 21); [exact (P 21 ltac:(unfold acallee_saved; lia)) | rewrite Q21, E21; exact R21].
  + cbn [ms_regs mkst]. transitivity (getr (ms_regs ms) 22); [exact (P 22 ltac:(unfold acallee_saved; lia)) | rewrite Q22, E22; exact R22].
  + cbn [ms_regs mkst]. transitivity (getr (ms_regs ms) 23); [exact (P 23 ltac:(unfold acallee_saved; lia)) | rewrite Q23, E23; exact R23].
  + exact T5.
  + exact Hcopy2.
  + exact Hnull.
  + exact Hnone2.
Qed.

(* ---- R4: PP_K9 0x810ec -> pcap_source_next of the closed reader (0x810fc) -> PP_K10 0x81100 --------------------
   mv a0,s2 (ps); mv a1,s6 (buf); mv a2,s5 (cap); mv a3,zero (no timestamp cell); jal pcap_source_next. ps->f = 0
   (p_psnull), so the statement's closed-reader arm: a0 = -1 and nothing of the caller's is written. *)
Lemma tail_R4 : pe_from SK B MT KS POST (GI_K10 B MT KS) -> pe_from SK B MT KS POST (GI_K9 B MT KS).
Proof.
intros NEXT cx fp k acc ly3 S3 W3 ms3 md3 HB HJ Hfrs Hmo HG.
destruct HG as (bb & bf & (Hbody & Hk & Hacc & Hperm & Hfds & Hfs) & Hn26 & R18 & R19 & R20 & R21 & R22 & R23 &
  Hslots & Hcopy & Hnull & Hsrc).
destruct Hbody as (Hpc & Hresv & Hsvc & Hrom & Hfrg & Hfcsr & Hregs & Hsaved & Hhdr & Hsh & Hlen & Hin).
pose proof (tail_geo cx HB) as (Hal & Hs1m & Hs1b & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
unfold LLVMF_STK in Hslo, Hbot.
pose proof HB as ((HAR0 & Hrok & Hra4 & Hgp0 & Htp0 & _) & HraL & _ & _ & _ & _ & _ & Hev & _ & _ & _ & _ & _ & _ &
  _ & _ & Hmok & Hneed & HGX & HGD & _ & _ & Hftr).
destruct (gx_open _ _ _ _ _ _ _ _ HJ) as (memS & HJi & Hag). clear HJ. rename HJi into HJ.
pose proof HJ as (HAR & Hly & _).
destruct Hregs as (Rsp & Rs0 & Rs1 & Rs11 & Rgp & Rtp).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as (HB0 & HB1 & HB2). pose proof (pa_base_lo (PL := PL_pcap) (PI := PI)) as HBLO.
destruct (lay_eqs _ _ _ Hly) as (EF & Etop & Eslo & Eshi).
assert (Efa : frame_addr ly3 PE_CID fp = pF cx fp) by (unfold pF, frame_addr; rewrite EF; reflexivity).
assert (Hfin : In (PE_CID, fp) (frames S3)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 PE_CID fp HAR Hfin) as (Hf4096 & Hfceil & Hfapp).
rewrite Efa in Hf4096, Hfceil, Hfapp. change (fs_frame_bytes PE_CID) with 128 in Hfceil, Hfapp.
destruct (frame_al64 SEGS B ly3 S3 W3 (ms_mem ms3) md3 PE_CID fp HAR Hfin) as (Hfa64 & _ & _). rewrite Efa in Hfa64.
(* the symbolic state at 0x810ec *)
pose proof (entry0 PP_K9 ms3 W3 Hpc Hresv Hsvc Hrom Hfrg Hfcsr) as HS.
remember (Eimg (Ereg (ms_regs ms3) [])) as E eqn:HEdef.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg (ms_regs ms3) []) n)
  by (intros n Hn; subst E; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr (ms_regs ms3) 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr (ms_regs ms3) 3) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr (ms_regs ms3) 4) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 4 4%bv eq_refl)).
assert (E8 : ew E 8 = getr (ms_regs ms3) 8) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 8 8%bv eq_refl)).
assert (E9 : ew E 9 = getr (ms_regs ms3) 9) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 9 9%bv eq_refl)).
assert (E18 : ew E 18 = getr (ms_regs ms3) 18) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 18 18%bv eq_refl)).
assert (E19 : ew E 19 = getr (ms_regs ms3) 19) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 19 19%bv eq_refl)).
assert (E20 : ew E 20 = getr (ms_regs ms3) 20) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 20 20%bv eq_refl)).
assert (E21 : ew E 21 = getr (ms_regs ms3) 21) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 21 21%bv eq_refl)).
assert (E22 : ew E 22 = getr (ms_regs ms3) 22) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 22 22%bv eq_refl)).
assert (E23 : ew E 23 = getr (ms_regs ms3) 23) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 23 23%bv eq_refl)).
assert (E27 : ew E 27 = getr (ms_regs ms3) 27) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 27 27%bv eq_refl)).
assert (SHOK : sh_ok SEGS TBx [] E (mrestrict (w_H W3) (ms_mem ms3))) by constructor.
clear HEdef EL.
(* 0x810ec mv a0,s2; mv a1,s6; mv a2,s5; mv a3,zero; 0x810fc jal pcap_source_next *)
paj_run_tok RUN HS HJ SHOK TBspan; [apply awr_ok_nil |].
assert (HFm : ms_mem ms = ms_mem ms3) by exact (frame_of_nil _ _ _ HF).
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
prreg HS (12%bv : bv 5) Q12. prreg HS (13%bv : bv 5) Q13. prreg HS (19%bv : bv 5) Q19. prreg HS (20%bv : bv 5) Q20.
prreg HS (22%bv : bv 5) Q22. prreg HS (23%bv : bv 5) Q23. prreg HS (27%bv : bv 5) Q27.
rewrite pa_sigma_pcap_source_next.
assert (Hsp : spZ (ms_regs ms) = c_sp1 cx) by (unfold spZ at 1; rewrite Q2, E2, Rsp; unfold w64; apply unsigned_lit_small; lia).
assert (Hps : pPS cx fp = pF cx fp + 32) by reflexivity.
assert (Hps8 : pPS cx fp mod 8 = 0).
{ rewrite Hps. apply Z.mod_divide; [lia|]. apply Z.mod_divide in Hfa64; [|lia]. destruct Hfa64 as [q Hq]. exists (8 * q + 4). lia. }
assert (Hs8 : rdword (aview SEGS (w_H W3) (ms_mem ms3)) (spZ (c_regs cx) - 8) = Some (raZ (c_regs cx)))
  by exact (proj1 Hsaved).
assert (Hs16 : rdword (aview SEGS (w_H W3) (ms_mem ms3)) (spZ (c_regs cx) - 16) = Some (s0Z (c_regs cx))).
{ pose proof (proj2 Hsaved 0 ltac:(lia)) as H0. replace (spZ (c_regs cx) - 16 - 8 * 0) with (spZ (c_regs cx) - 16) in H0 by lia.
  exact H0. }
eapply SRr_bind.
{ eapply (NEXTS LLVMF_STK (spZ (c_regs cx)) [sink_token] (c_ly cx) (c_S cx) (c_W cx) memS (c_md cx) [(PE_CID, fp)]
    ly3 S3 W3 (ms_mem ms) _ k (ms_regs ms) (pPS cx fp) bf (p_cap cx) 0 0 0 0 0 0 0 0 0 (c_M cx) PE_CID fp [] [] []
    (pch cx) HJ).
  - exact (aro_now cx memS _ ly3 S3 W3 (ms_mem ms) _ k HB HJ Hag).
  - rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - unfold raZ. rewrite Q1, unsigned_lit_small by lia. lia.
  - rewrite Q3, E3, Rgp. exact Hgp0.
  - rewrite Q4, E4, Rtp. exact Htp0.
  - rewrite Q10, E18, R18. reflexivity.
  - rewrite Q11, E22, R22. reflexivity.
  - rewrite Q12, E21, R21. reflexivity.
  - rewrite Q13. reflexivity.
  - rewrite Hsp. apply Z.mod_divide; [lia|]. apply Z.mod_divide in Hs1m; [|lia]. destruct Hs1m as [q Hq]. exists (2 * q). lia.
  - rewrite Hsp. assert (HNX : NX_STK = 8496) by reflexivity. rewrite HNX. unfold LLVMF_STK. lia.
  - rewrite Hsp. lia.
  - rewrite Hsp. unfold s0Z at 1. rewrite Q8, E8, Rs0. unfold w64. rewrite unsigned_lit_small by lia.
    rewrite <- HFm in Hs8, Hs16. exact (pch_achain cx _ memS ly3 S3 W3 (ms_mem ms) _ k HB HJ Hag Hs8 Hs16).
  - rewrite Hfrs. vm_compute. reflexivity.
  - unfold PS_F_OFF. rewrite Z.add_0_r, HFm. exact Hnull.
  - lia.
  - exact Hps8.
  - rewrite Hps. lia.
  - unfold PS_LEN. rewrite Hps. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hfapp. lia.
  - unfold amem_range, PS_LEN. rewrite Hps. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hfapp. lia.
  - left. reflexivity.
  - rewrite Efa, Hps. lia.
  - rewrite Efa, Hps. change (fs_frame_bytes PE_CID) with 128. unfold PS_LEN. lia.
  - rewrite HFm. apply zero_shadow_range; [exact Hps8 | reflexivity |].
    intros i Hi. unfold PS_LEN in Hi. change (24 / 8) with 3 in Hi.
    rewrite Hps, shadow_of_addr_aligned_off by (apply Z.mod_divide; [lia|]; apply Z.mod_divide in Hfa64; [|lia];
      destruct Hfa64 as [q Hq]; exists (8 * q); lia).
    change (32 / 8) with 4.
    assert (Hi3 : i = 0 \/ i = 1 \/ i = 2) by lia.
    destruct Hi3 as [-> | [-> | ->]].
    + replace (shadow_of_addr SHADOW_OFF (pF cx fp) + 4 + 0) with (pSH cx fp + Z.of_nat 4) by (unfold pSH; lia).
      exact (Hsh 4%nat ltac:(rewrite Hlen; unfold PE_NSH; lia)).
    + replace (shadow_of_addr SHADOW_OFF (pF cx fp) + 4 + 1) with (pSH cx fp + Z.of_nat 5) by (unfold pSH; lia).
      exact (Hsh 5%nat ltac:(rewrite Hlen; unfold PE_NSH; lia)).
    + replace (shadow_of_addr SHADOW_OFF (pF cx fp) + 4 + 2) with (pSH cx fp + Z.of_nat 6) by (unfold pSH; lia).
      exact (Hsh 6%nat ltac:(rewrite Hlen; unfold PE_NSH; lia)).
  - intros H0. exfalso. apply H0. reflexivity.
  - intros H0. exfalso. apply H0. reflexivity.
  - intros H0. exfalso. apply H0. reflexivity.
  - intros H0. exfalso. apply H0. reflexivity.
  - intros H0. exfalso. apply H0. reflexivity.
  - intros H0. exfalso. apply H0. reflexivity.
  - intros H0. exfalso. apply H0. reflexivity.
  - intros H0. exfalso. apply H0. reflexivity. }
cbv beta. intros W2 c2 Hwle (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hbl2 & Hfr2 & Hmle & Hfd2 & Hfs2 & Hfin2).
destruct Hfin2 as [(_ & Ha0 & HK) | (Hh & _)]; [| exfalso; apply Hh; reflexivity].
rewrite Q1.
destruct HK as (K1 & K2 & K3 & K4 & K5 & K6).
assert (Hfoot : forall a, hfoot cx fp a -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W3) (ms_mem ms3) a).
{ intros a Ha. rewrite <- HFm.
  refine (foot_kept cx fp ly3 S3 W3 (ms_mem ms) W2 mem2 _ _ (fun _ => False) HB K1 K2 K4 _ Hfin Efa
    (input_block cx ly3 S3 _ HB Hperm) _ a Ha); [rewrite Hsp; lia|].
  intros x _ Hx. exact Hx. }
destruct (tail_kept cx fp W3 ms3 W2 (mkst regs2 (Z_to_bv 64 (BASE + PP_K10)) mem2 (seg_rom SEGS)) PSH_ts Hfoot
  Hsaved Hhdr Hsh Hlen Hin Hslots) as (T1 & T2 & T3 & T4 & T5).
assert (P : forall r : Z, acallee_saved r -> getr regs2 (Z_to_bv 5 r) = getr (ms_regs ms) (Z_to_bv 5 r)) by exact HP2.
eapply (NEXT cx fp (k + EV_NEXT) (acc + 0) ly2 S2 W2 (mkst regs2 (Z_to_bv 64 (BASE + PP_K10)) mem2 (seg_rom SEGS)) md2 HB).
- exact (gx_pack0 cx _ memS _ _ _ _ _ _ HJ2 Hag).
- rewrite Hfr2. exact Hfrs.
- exact (mle_station MT _ _ _ _ _ MLAWS Hmo Hmle).
- unfold GI_K10, p_cut. exists bb, bf.
  split; [|split; [exact Hn26 | split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]].
  + split; [|split; [unfold EV_NEXT; lia | split; [lia | split; [|split]]]].
    * unfold pe_body. cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr mkst ms_regs].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|]. split; [reflexivity|].
      split; [|split; [exact T1 | split; [exact T2 | split; [exact T3 | split; [exact Hlen | exact T4]]]]].
      unfold pregs. cbn [ms_regs mkst].
      split; [transitivity (getr (ms_regs ms) 2); [exact (P 2 ltac:(unfold acallee_saved; lia)) | rewrite Q2, E2; exact Rsp]|].
      split; [transitivity (getr (ms_regs ms) 8); [exact (P 8 ltac:(unfold acallee_saved; lia)) | rewrite Q8, E8; exact Rs0]|].
      split; [transitivity (getr (ms_regs ms) 9); [exact (P 9 ltac:(unfold acallee_saved; lia)) | rewrite Q9, E9; exact Rs1]|].
      split; [transitivity (getr (ms_regs ms) 27); [exact (P 27 ltac:(unfold acallee_saved; lia)) | rewrite Q27, E27; exact Rs11]|].
      split; [transitivity (getr (ms_regs ms) 3); [exact (P 3 ltac:(unfold acallee_saved; lia)) | rewrite Q3, E3; exact Rgp]|].
      transitivity (getr (ms_regs ms) 4); [exact (P 4 ltac:(unfold acallee_saved; lia)) | rewrite Q4, E4; exact Rtp].
    * rewrite Hbl2. exact Hperm.
    * rewrite Hfd2. rewrite (proj1 (fs_wvb md3 mat)). exact Hfds.
    * rewrite Hfs2. rewrite (proj2 (fs_wvb md3 mat)). exact Hfs.
  + cbn [ms_regs mkst]. exact Ha0.
  + cbn [ms_regs mkst]. transitivity (getr (ms_regs ms) 19); [exact (P 19 ltac:(unfold acallee_saved; lia)) | rewrite Q19, E19; exact R19].
  + cbn [ms_regs mkst]. transitivity (getr (ms_regs ms) 20); [exact (P 20 ltac:(unfold acallee_saved; lia)) | rewrite Q20, E20; exact R20].
  + cbn [ms_regs mkst]. transitivity (getr (ms_regs ms) 22); [exact (P 22 ltac:(unfold acallee_saved; lia)) | rewrite Q22, E22; exact R22].
  + cbn [ms_regs mkst]. transitivity (getr (ms_regs ms) 23); [exact (P 23 ltac:(unfold acallee_saved; lia)) | rewrite Q23, E23; exact R23].
  + exact T5.
  + unfold p_psnull, pval. cbn [ms_mem mkst]. eapply vm_frame_segs; [|exact Hnull].
    intros x Hx. apply (mbyte_of_aview SEGS). rewrite <- HFm.
    apply (K4 PE_CID fp x Hfin); [|intros []].
    left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite Efa. change (fs_frame_bytes PE_CID) with 128.
    rewrite Hps in Hx. lia.
  + cbn [ms_mem mkst]. apply (asource_none_frame KS (rdW W3 (ms_mem ms3))); [|exact Hsrc].
    intros a Ha. apply (mbyte_of_aview SEGS). rewrite <- HFm.
    destruct (asil_env _ _ _ _ ASIL a Ha) as (Hi & Ho & He). exact (K3 a Hi Ho He).
Qed.

(* ---- R7: PP_K12 0x81118 -> PP_K12r 0x81124: `ts` out of scope ---------------------------------------------------
   addi a0,zero,-8 0x81118; ld s9,8(s1) 0x8111c (the spill slot PS_SH); sb a0,0xc(s9) 0x81120. The plain engine over
   two regions: the slot (base s1, the value an extra atom 32 = pSH) and the shadow byte 12 (base atom 32). *)
Definition r7_rs : smem :=
  [ YP09.mkRegion (Some 9%nat) 8 16 0 0 [YP09.mkChunk 8 (CVal 8 (SOff 32 0))];
    YP09.mkRegion (Some 32%nat) 12 13 12 13 [] ].


Lemma tail_R7 : pe_from SK B MT KS POST (GI_K12r B MT KS) -> pe_from SK B MT KS POST (GI_K12 B MT KS).
Proof.
intros NEXT cx fp k acc ly3 S3 W3 ms3 md3 HB HJ Hfrs Hmo HG.
destruct HG as ((Hbody & Hk & Hacc & Hperm & Hfds & Hfs) & Hn26 & R20 & R23 & Hslots & Hsrc).
destruct Hbody as (Hpc & Hresv & Hsvc & Hrom & Hfrg & Hfcsr & Hregs & Hsaved & Hhdr & Hsh & Hlen & Hin).
pose proof (tail_geo cx HB) as (Hal & Hs1m & Hs1b & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
unfold LLVMF_STK in Hslo, Hbot.
destruct (gx_open _ _ _ _ _ _ _ _ HJ) as (memS & HJi & Hag). clear HJ. rename HJi into HJ.
pose proof HJ as (HAR & Hly & _).
destruct Hregs as (Rsp & Rs0 & Rs1 & Rs11 & Rgp & Rtp).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (lay_eqs _ _ _ Hly) as (EF & Etop & Eslo & Eshi).
assert (Efa : frame_addr ly3 PE_CID fp = pF cx fp) by (unfold pF, frame_addr; rewrite EF; reflexivity).
assert (Hfin : In (PE_CID, fp) (frames S3)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 PE_CID fp HAR Hfin) as (Hf4096 & Hfceil & Hfapp).
rewrite Efa in Hf4096, Hfceil, Hfapp. change (fs_frame_bytes PE_CID) with 128 in Hfceil, Hfapp.
destruct (al_frames _ _ LAWS _ _ _ _ _ PE_CID fp HAR Hfin) as (_ & _ & _ & HFSpres).
change (fs_frame_bytes PE_CID / 8) with 16 in HFSpres. rewrite Efa in HFSpres.
change (shadow_addr (pF cx fp)) with (pSH cx fp) in HFSpres.
assert (HSHb : 0x7fff8000 <= pSH cx fp /\ pSH cx fp + 16 <= alloc_ceiling).
{ unfold pSH, shadow_of_addr, SHADOW_OFF. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hfapp.
  Z.div_mod_to_equations. lia. }
pose proof Hslots as (_ & _ & _ & PSHs & _). unfold pslot, PS_SH in PSHs.
remember (Eimg (Ereg (ms_regs ms3) [Z_to_bv 64 (pSH cx fp)])) as E eqn:HEdef.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg (ms_regs ms3) [Z_to_bv 64 (pSH cx fp)]) n)
  by (intros n Hn; subst E; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr (ms_regs ms3) 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr (ms_regs ms3) 3) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr (ms_regs ms3) 4) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 4 4%bv eq_refl)).
assert (E8 : ew E 8 = getr (ms_regs ms3) 8) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 8 8%bv eq_refl)).
assert (E9 : ew E 9 = getr (ms_regs ms3) 9) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 9 9%bv eq_refl)).
assert (E20 : ew E 20 = getr (ms_regs ms3) 20) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 20 20%bv eq_refl)).
assert (E23 : ew E 23 = getr (ms_regs ms3) 23) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 23 23%bv eq_refl)).
assert (E27 : ew E 27 = getr (ms_regs ms3) 27) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 27 27%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 (pSH cx fp)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 0)).
assert (U9 : bv_unsigned (ew E 9) = c_sp1 cx) by (rewrite E9, Rs1; unfold w64; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = pSH cx fp) by (rewrite E32; apply unsigned_lit_small; lia).
assert (HS : st_ok_pi SEGS VAL E (mkSS PP_K12 sr_atoms r7_rs None nofacts) (restrict (w_H W3) ms3)).
{ rewrite HEdef. rewrite HEdef in U9, U32, E32.
  apply entryR; try assumption; [vm_compute; reflexivity | | | split; [exact I | split; exact I]].
  - unfold r7_rs. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS _ _ (c_sp1 cx) 8 8 (SOff 32 0) (pSH cx fp));
        [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3) _ _ PSHs).
    + rewrite U32. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). replace (pSH cx fp + o) with (pSH cx fp + 12) by lia.
      exact (proj1 (HFSpres 12 ltac:(lia))).
  - apply pairwise_disjoint_of_extents. unfold r7_rs, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U32.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia. }
clear HEdef EL.
paj_run_to_sh RUNTOP HS HJ PP_K12r.
{ unfold r7_rs. cbn [ss_mem]. apply awr_ok_cons_ro; [cbn; lia|].
  eapply awr_ok_cons_gen; [reflexivity | exact U32 | | apply awr_ok_nil].
  intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. apply (awr_ownframe _ _ _ _ _ _ cx fp a Efa). right. lia. }
pmkst HS.
prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8.
prreg HS (9%bv : bv 5) Q9. prreg HS (20%bv : bv 5) Q20. prreg HS (23%bv : bv 5) Q23. prreg HS (25%bv : bv 5) Q25.
prreg HS (27%bv : bv 5) Q27.
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => pSH cx fp + 12 <= a < pSH cx fp + 13) HFr
  ltac:(intros bbW wloW whiW aW HinW HrrW; vm_compute in HinW;
        repeat (destruct HinW as [HqW | HinW]; [injection HqW as <- <- <-; cbn [base_val] in HrrW;
          rewrite ?U9, ?U32 in HrrW; cbv beta; lia|]);
        destruct HinW)) as UN.
lazymatch type of HS with st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
  pose proof (st_ok_pi_region_nth E ssx (restrict (w_H W3) msx) 1 _ HS eq_refl) as HR1 end.
cbn [ms_mem restrict mkst] in HR1.
pose proof (field_of_region_any E _ 32%nat (pSH cx fp) _ _ _ _ _ 12 1%N (SLit 18446744073709551608) HR1 U32
  ltac:(left; reflexivity) ltac:(cbn; lia)) as V12.
pose proof (aview_lit_byte _ _ _ _ _ 248 V12 ltac:(vm_compute; reflexivity)) as A12.
assert (UNs : forall a, hfoot_ns cx fp a -> aview SEGS (w_H W3) (ms_mem ms) a = aview SEGS (w_H W3) (ms_mem ms3) a).
{ intros a Ha. pose proof (shadow_off_hfoot_ns cx fp ly3 S3 W3 (ms_mem ms3) md3 _ HB HAR Hperm Hfin Efa a Ha) as Hn.
  apply UN; [|cbv beta; lia].
  unfold hfoot_ns in Ha. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hfapp.
  destruct Ha as [Ha|[Ha|Ha]]; [lia | lia |].
  assert (Hcn : 0 < c_n cx) by lia. pose proof (input_block cx ly3 S3 _ HB Hperm Hcn) as Hpin.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hpin) as (_ & _ & _ & Hpapp & _).
  pose proof (req_size_pos (c_n cx) ltac:(lia)). unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hpapp. lia. }
destruct (tail_kept_ns cx fp W3 ms3 W3 (mkst (ms_regs ms) (Z_to_bv 64 (BASE + PP_K12r)) (ms_mem ms) (seg_rom SEGS))
  UNs Hsaved Hhdr Hin) as (T1 & T2 & T4).
eapply (NEXT cx fp k acc ly3 S3 W3 (mkst (ms_regs ms) (Z_to_bv 64 (BASE + PP_K12r)) (ms_mem ms) (seg_rom SEGS)) _ HB).
- exact (gx_pack0 cx _ memS _ _ _ _ _ _ HJ Hag).
- exact Hfrs.
- exact Hmo.
- unfold GI_K12r. split; [|split; [exact Hn26 | split; [|split; [|split]]]].
  + exists PSH_tsout. split; [left; reflexivity|].
    split; [|split; [unfold EV_LIB; lia | split; [exact Hacc | split; [exact Hperm | split]]]].
    * unfold pe_body. cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr mkst ms_regs].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|]. split; [reflexivity|].
      split; [|split; [exact T1 | split; [exact T2 | split; [|split; [reflexivity | exact T4]]]]].
      { unfold pregs. cbn [ms_regs mkst].
        rewrite Q2, Q8, Q9, Q27, Q3, Q4, E2, E8, E9, E27, E3, E4.
        repeat split; assumption. }
      { intros i Hi. cbn [ms_mem mkst]. destruct (Nat.eq_dec i 12) as [->|Hne].
        - exact A12.
        - assert (Hi16 : (i < 16)%nat) by exact Hi.
          rewrite UN; [| pose proof (proj1 HSHb); lia | cbv beta; lia].
          rewrite (psh_tsout_eq i Hne). apply Hsh. rewrite Hlen. unfold PE_NSH. exact Hi16. }
    * rewrite (proj1 (fs_wvb md3 mat)). exact Hfds.
    * rewrite (proj2 (fs_wvb md3 mat)). exact Hfs.
  + cbn [ms_regs mkst]. rewrite Q20, E20. exact R20.
  + cbn [ms_regs mkst]. rewrite Q23, E23. exact R23.
  + cbn [ms_regs mkst]. rewrite Q25, E32. reflexivity.
  + cbn [ms_mem mkst]. apply (asource_none_frame KS (rdW W3 (ms_mem ms3))); [|exact Hsrc].
    intros a Ha. apply (mbyte_of_aview SEGS).
    destruct (asil_env _ _ _ _ ASIL a Ha) as (Hi & _).
    pose proof (pa_img_range a Hi) as Har. unfold pcap_img_end, YImgTop.IMG_TOP in Har.
    apply UN; [lia | cbv beta; lia].
Qed.

(* ---- K12r -> leave: PP_K12r 0x81124 -> PP_leave 0x81134: `ps` out of scope -------------------------------------
   addi a0,zero,-8 0x81124; sb a0,4(s9) / 5(s9) / 6(s9) 0x81128..0x81130. One region: the shadow bytes 4..6. *)
Definition bt1_rs : smem := [ YP09.mkRegion (Some 25%nat) 4 7 4 7 [] ].

Lemma tail_K12r : pe_from SK B MT KS POST (GI_leave B MT KS) -> pe_from SK B MT KS POST (GI_K12r B MT KS).
Proof.
intros NEXT cx fp k acc ly3 S3 W3 ms3 md3 HB HJ Hfrs Hmo HG.
destruct HG as ((sh & Hshc & (Hbody & Hk & Hacc & Hperm & Hfds & Hfs)) & Hn26 & R20 & R23 & R25 & Hsrc).
destruct Hbody as (Hpc & Hresv & Hsvc & Hrom & Hfrg & Hfcsr & Hregs & Hsaved & Hhdr & Hsh & Hlen & Hin).
pose proof (tail_geo cx HB) as (Hal & Hs1m & Hs1b & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
unfold LLVMF_STK in Hslo, Hbot.
destruct (gx_open _ _ _ _ _ _ _ _ HJ) as (memS & HJi & Hag). clear HJ. rename HJi into HJ.
pose proof HJ as (HAR & Hly & _).
destruct Hregs as (Rsp & Rs0 & Rs1 & Rs11 & Rgp & Rtp).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (lay_eqs _ _ _ Hly) as (EF & Etop & Eslo & Eshi).
assert (Efa : frame_addr ly3 PE_CID fp = pF cx fp) by (unfold pF, frame_addr; rewrite EF; reflexivity).
assert (Hfin : In (PE_CID, fp) (frames S3)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 PE_CID fp HAR Hfin) as (Hf4096 & Hfceil & Hfapp).
rewrite Efa in Hf4096, Hfceil, Hfapp. change (fs_frame_bytes PE_CID) with 128 in Hfceil, Hfapp.
destruct (al_frames _ _ LAWS _ _ _ _ _ PE_CID fp HAR Hfin) as (_ & _ & _ & HFSpres).
change (fs_frame_bytes PE_CID / 8) with 16 in HFSpres. rewrite Efa in HFSpres.
change (shadow_addr (pF cx fp)) with (pSH cx fp) in HFSpres.
assert (HSHb : 0x7fff8000 <= pSH cx fp /\ pSH cx fp + 16 <= alloc_ceiling).
{ unfold pSH, shadow_of_addr, SHADOW_OFF. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hfapp.
  Z.div_mod_to_equations. lia. }
remember (Eimg (Ereg (ms_regs ms3) [])) as E eqn:HEdef.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg (ms_regs ms3) []) n)
  by (intros n Hn; subst E; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr (ms_regs ms3) 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr (ms_regs ms3) 3) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr (ms_regs ms3) 4) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 4 4%bv eq_refl)).
assert (E8 : ew E 8 = getr (ms_regs ms3) 8) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 8 8%bv eq_refl)).
assert (E9 : ew E 9 = getr (ms_regs ms3) 9) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 9 9%bv eq_refl)).
assert (E20 : ew E 20 = getr (ms_regs ms3) 20) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 20 20%bv eq_refl)).
assert (E23 : ew E 23 = getr (ms_regs ms3) 23) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 23 23%bv eq_refl)).
assert (E25 : ew E 25 = getr (ms_regs ms3) 25) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 25 25%bv eq_refl)).
assert (E27 : ew E 27 = getr (ms_regs ms3) 27) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 27 27%bv eq_refl)).
assert (U25 : bv_unsigned (ew E 25) = pSH cx fp) by (rewrite E25, R25; unfold w64; apply unsigned_lit_small; lia).
assert (HS : st_ok_pi SEGS VAL E (mkSS PP_K12r sr_atoms bt1_rs None nofacts) (restrict (w_H W3) ms3)).
{ rewrite HEdef. rewrite HEdef in U25.
  apply entryR; try assumption; [vm_compute; reflexivity | | | split; [exact I | split; exact I]].
  - unfold bt1_rs. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U25. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). exact (proj1 (HFSpres o ltac:(lia))).
  - apply pairwise_disjoint_of_extents. unfold bt1_rs, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val zpairwise_disjoint zall_disjoint]. repeat split. }
clear HEdef EL.
paj_run_to_sh RUNTOP HS HJ PP_leave.
{ unfold bt1_rs. cbn [ss_mem].
  eapply awr_ok_cons_gen; [reflexivity | exact U25 | | apply awr_ok_nil].
  intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. apply (awr_ownframe _ _ _ _ _ _ cx fp a Efa). right. lia. }
pmkst HS.
prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8.
prreg HS (9%bv : bv 5) Q9. prreg HS (20%bv : bv 5) Q20. prreg HS (23%bv : bv 5) Q23. prreg HS (25%bv : bv 5) Q25.
prreg HS (27%bv : bv 5) Q27.
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => pSH cx fp + 4 <= a < pSH cx fp + 7) HFr
  ltac:(intros bbW wloW whiW aW HinW HrrW; vm_compute in HinW;
        repeat (destruct HinW as [HqW | HinW]; [injection HqW as <- <- <-; cbn [base_val] in HrrW;
          rewrite ?U25 in HrrW; cbv beta; lia|]);
        destruct HinW)) as UN.
lazymatch type of HS with st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
  pose proof (st_ok_pi_region_nth E ssx (restrict (w_H W3) msx) 0 _ HS eq_refl) as HR0 end.
cbn [ms_mem restrict mkst] in HR0.
pose proof (field_of_region_any E _ 25%nat (pSH cx fp) _ _ _ _ _ 4 1%N (SLit 18446744073709551608) HR0 U25
  ltac:(right; right; left; reflexivity) ltac:(cbn; lia)) as V4.
pose proof (field_of_region_any E _ 25%nat (pSH cx fp) _ _ _ _ _ 5 1%N (SLit 18446744073709551608) HR0 U25
  ltac:(right; left; reflexivity) ltac:(cbn; lia)) as V5.
pose proof (field_of_region_any E _ 25%nat (pSH cx fp) _ _ _ _ _ 6 1%N (SLit 18446744073709551608) HR0 U25
  ltac:(left; reflexivity) ltac:(cbn; lia)) as V6.
pose proof (aview_lit_byte _ _ _ _ _ 248 V4 ltac:(vm_compute; reflexivity)) as A4.
pose proof (aview_lit_byte _ _ _ _ _ 248 V5 ltac:(vm_compute; reflexivity)) as A5.
pose proof (aview_lit_byte _ _ _ _ _ 248 V6 ltac:(vm_compute; reflexivity)) as A6.
assert (UNs : forall a, hfoot_ns cx fp a -> aview SEGS (w_H W3) (ms_mem ms) a = aview SEGS (w_H W3) (ms_mem ms3) a).
{ intros a Ha. pose proof (shadow_off_hfoot_ns cx fp ly3 S3 W3 (ms_mem ms3) md3 _ HB HAR Hperm Hfin Efa a Ha) as Hn.
  apply UN; [|cbv beta; lia].
  unfold hfoot_ns in Ha. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hfapp.
  destruct Ha as [Ha|[Ha|Ha]]; [lia | lia |].
  assert (Hcn : 0 < c_n cx) by lia. pose proof (input_block cx ly3 S3 _ HB Hperm Hcn) as Hpin.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hpin) as (_ & _ & _ & Hpapp & _).
  pose proof (req_size_pos (c_n cx) ltac:(lia)). unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hpapp. lia. }
destruct (tail_kept_ns cx fp W3 ms3 W3 (mkst (ms_regs ms) (Z_to_bv 64 (BASE + PP_leave)) (ms_mem ms) (seg_rom SEGS))
  UNs Hsaved Hhdr Hin) as (T1 & T2 & T4).
eapply (NEXT cx fp k acc ly3 S3 W3 (mkst (ms_regs ms) (Z_to_bv 64 (BASE + PP_leave)) (ms_mem ms) (seg_rom SEGS)) _ HB).
- exact (gx_pack0 cx _ memS _ _ _ _ _ _ HJ Hag).
- exact Hfrs.
- exact Hmo.
- unfold GI_leave. split; [|split; [|split; [|split]]].
  + split; [|split; [exact Hk | split; [exact Hacc | split; [exact Hperm | split]]]].
    * unfold pe_body. cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr mkst ms_regs].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|]. split; [reflexivity|].
      split; [|split; [exact T1 | split; [exact T2 | split; [|split; [reflexivity | exact T4]]]]].
      { unfold pregs. cbn [ms_regs mkst].
        rewrite Q2, Q8, Q9, Q27, Q3, Q4, E2, E8, E9, E27, E3, E4.
        repeat split; assumption. }
      { intros i Hi. cbn [ms_mem mkst]. assert (Hi16 : (i < 16)%nat) by exact Hi.
        destruct (Nat.eq_dec i 4) as [->|H4]; [exact A4|].
        destruct (Nat.eq_dec i 5) as [->|H5]; [exact A5|].
        destruct (Nat.eq_dec i 6) as [->|H6]; [exact A6|].
        rewrite UN; [| pose proof (proj1 HSHb); lia | cbv beta; lia].
        rewrite (psh_out_eq sh i Hshc ltac:(lia)). apply Hsh. rewrite Hlen. unfold PE_NSH. exact Hi16. }
    * rewrite (proj1 (fs_wvb md3 mat)). exact Hfds.
    * rewrite (proj2 (fs_wvb md3 mat)). exact Hfs.
  + cbn [ms_regs mkst]. rewrite Q20, E20. exact R20.
  + cbn [ms_regs mkst]. rewrite Q23, E23. exact R23.
  + cbn [ms_regs mkst]. rewrite Q25, E25. exact R25.
  + cbn [ms_mem mkst]. apply (asource_none_frame KS (rdW W3 (ms_mem ms3))); [|exact Hsrc].
    intros a Ha. apply (mbyte_of_aview SEGS).
    destruct (asil_env _ _ _ _ ASIL a Ha) as (Hi & _).
    pose proof (pa_img_range a Hi) as Har. unfold pcap_img_end, YImgTop.IMG_TOP in Har.
    apply UN; [lia | cbv beta; lia].
Qed.

(* ---- leave -> ret: PP_leave 0x81134 -> PP_ret 0x81214: the frame given back -------------------------------------
   lui/addiw a0 = 0x45e0360e, sd a0,0(s7) 0x8113c (the retired-frame magic); beqz s4,0x81194 at 0x81140, not taken:
   s4 = F, the side-stack frame pe_from fixes (frames S3 = [(PE_CID, fp)], from AR_const_law's use-after-return cell
   and the stack_malloc rule at 0x80838), and F >= 4096 (frames_bounds), the atom fact on s4 below; so the machine-
   stack arm 0x81194..0x811d0 is never run. a0 = -0xb, sb a0 to the 16 shadow bytes 0x81144..0x81184;
   ld a0,0x78(s4) 0x81188 (the frame's flag pointer, pheader); sb zero,0(a0) 0x8118c (the flag: the frame is free,
   PcapFrame.aj_flag_store_pi, astack_free_law); j 0x811d4; a0 = 0; sp = s0 - 0xe0; the 13 saved registers
   0x811dc..0x8120c; sp += 0xe0; at the ret. Regions: the 13 saved words (base s0, values the extra atoms 32..44),
   the header word (base s7), the flag-pointer word (base s4, value the extra atom 45 = the flag), the shadow
   (base s9), the flag byte (base atom 45). *)
Definition bt2_rs : smem :=
  [ YP09.mkRegion (Some 8%nat) (-104) 0 0 0
      [YP09.mkChunk (-8) (CVal 8 (SOff 32 0)); YP09.mkChunk (-16) (CVal 8 (SOff 33 0));
       YP09.mkChunk (-24) (CVal 8 (SOff 34 0)); YP09.mkChunk (-32) (CVal 8 (SOff 35 0));
       YP09.mkChunk (-40) (CVal 8 (SOff 36 0)); YP09.mkChunk (-48) (CVal 8 (SOff 37 0));
       YP09.mkChunk (-56) (CVal 8 (SOff 38 0)); YP09.mkChunk (-64) (CVal 8 (SOff 39 0));
       YP09.mkChunk (-72) (CVal 8 (SOff 40 0)); YP09.mkChunk (-80) (CVal 8 (SOff 41 0));
       YP09.mkChunk (-88) (CVal 8 (SOff 42 0)); YP09.mkChunk (-96) (CVal 8 (SOff 43 0));
       YP09.mkChunk (-104) (CVal 8 (SOff 44 0))];
    YP09.mkRegion (Some 23%nat) 0 8 0 8 [];
    YP09.mkRegion (Some 20%nat) 120 128 0 0 [YP09.mkChunk 120 (CVal 8 (SOff 45 0))];
    YP09.mkRegion (Some 25%nat) 0 16 0 16 [];
    YP09.mkRegion (Some 45%nat) 0 1 0 1 [] ].
Definition bt2_facts : facts := mkFacts [(20%nat, mkAF 4096 (2 ^ 47) 6)] [] [].
Definition bt2_ext (cx : ecx) (fp : Z) : list word :=
  [getr (c_regs cx) (Z_to_bv 5 1); getr (c_regs cx) (Z_to_bv 5 8); getr (c_regs cx) (Z_to_bv 5 9);
   getr (c_regs cx) (Z_to_bv 5 18); getr (c_regs cx) (Z_to_bv 5 19); getr (c_regs cx) (Z_to_bv 5 20);
   getr (c_regs cx) (Z_to_bv 5 21); getr (c_regs cx) (Z_to_bv 5 22); getr (c_regs cx) (Z_to_bv 5 23);
   getr (c_regs cx) (Z_to_bv 5 24); getr (c_regs cx) (Z_to_bv 5 25); getr (c_regs cx) (Z_to_bv 5 26);
   getr (c_regs cx) (Z_to_bv 5 27); Z_to_bv 64 (pFL cx fp)].

Lemma tail_leave : pe_from_ret SK B MT KS POST (GI_ret B MT KS) -> pe_from SK B MT KS POST (GI_leave B MT KS).
Proof.
intros NEXT cx fp k acc ly3 S3 W3 ms3 md3 HB HJ Hfrs Hmo HG.
destruct HG as ((Hbody & Hk & Hacc & Hperm & Hfds & Hfs) & R20 & R23 & R25 & Hsrc).
destruct Hbody as (Hpc & Hresv & Hsvc & Hrom & Hfrg & Hfcsr & Hregs & Hsaved & Hhdr & Hsh & Hlen & Hin).
pose proof (tail_geo cx HB) as (Hal & Hs1m & Hs1b & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
unfold LLVMF_STK in Hslo, Hbot.
destruct (gx_open _ _ _ _ _ _ _ _ HJ) as (memS & HJi & Hag). clear HJ. rename HJi into HJ.
pose proof HJ as (HAR & Hly & _).
destruct Hregs as (Rsp & Rs0 & Rs1 & Rs11 & Rgp & Rtp).
destruct Hsaved as (Hs8 & Hsj). destruct Hhdr as (_ & _ & _ & Hh120). unfold PE_FLAGPTR in Hh120.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (lay_eqs _ _ _ Hly) as (EF & Etop & Eslo & Eshi).
assert (Efa : frame_addr ly3 PE_CID fp = pF cx fp) by (unfold pF, frame_addr; rewrite EF; reflexivity).
assert (EFL : flag_addr ly3 PE_CID fp = pFL cx fp) by (unfold pFL, flag_addr; rewrite EF; reflexivity).
assert (Hfin : In (PE_CID, fp) (frames S3)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 PE_CID fp HAR Hfin) as (Hf4096 & Hfceil & Hfapp).
rewrite Efa in Hf4096, Hfceil, Hfapp. change (fs_frame_bytes PE_CID) with 128 in Hfceil, Hfapp.
destruct (frame_al64 SEGS B ly3 S3 W3 (ms_mem ms3) md3 PE_CID fp HAR Hfin) as (Hfa64 & _ & _). rewrite Efa in Hfa64.
destruct (al_frames _ _ LAWS _ _ _ _ _ PE_CID fp HAR Hfin) as (_ & _ & HFpres & HFSpres).
change (fs_frame_bytes PE_CID / 8) with 16 in HFSpres. change (fs_frame_bytes PE_CID) with 128 in HFpres.
rewrite Efa in HFpres, HFSpres. change (shadow_addr (pF cx fp)) with (pSH cx fp) in HFSpres.
destruct (FFL ly3 S3 W3 (ms_mem ms3) md3 PE_CID fp HAR Hfin) as (HFLpres & HFLown & (HFLapp & HFLimg) & (HFL4096 & _ & HFLceil)).
rewrite EFL in HFLpres, HFLown, HFLapp, HFLimg, HFL4096, HFLceil.
assert (HSHb : 0x7fff8000 <= pSH cx fp /\ pSH cx fp + 16 <= alloc_ceiling).
{ unfold pSH, shadow_of_addr, SHADOW_OFF. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hfapp.
  Z.div_mod_to_equations. lia. }
assert (HSHF : pSH cx fp + 16 <= pF cx fp \/ pF cx fp + 128 <= pSH cx fp).
{ unfold pSH, shadow_of_addr, SHADOW_OFF. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hfapp.
  Z.div_mod_to_equations. lia. }
assert (HnF : ~ (pF cx fp <= pFL cx fp < pF cx fp + 128)) by (intros Hc; exact (proj2 (HFpres _ Hc) HFLown)).
assert (HnS : ~ (pSH cx fp <= pFL cx fp < pSH cx fp + 16)).
{ intros Hc. pose proof (proj2 (HFSpres (pFL cx fp - pSH cx fp) ltac:(lia))) as Hno.
  replace (pSH cx fp + (pFL cx fp - pSH cx fp)) with (pFL cx fp) in Hno by lia. exact (Hno HFLown). }
remember (Eimg (Ereg (ms_regs ms3) (bt2_ext cx fp))) as E eqn:HEdef.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg (ms_regs ms3) (bt2_ext cx fp)) n)
  by (intros n Hn; subst E; apply Eimg_low; exact Hn).
assert (E3 : ew E 3 = getr (ms_regs ms3) 3) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr (ms_regs ms3) 4) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 4 4%bv eq_refl)).
assert (E8 : ew E 8 = getr (ms_regs ms3) 8) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 8 8%bv eq_refl)).
assert (E20 : ew E 20 = getr (ms_regs ms3) 20) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 20 20%bv eq_refl)).
assert (E23 : ew E 23 = getr (ms_regs ms3) 23) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 23 23%bv eq_refl)).
assert (E25 : ew E 25 = getr (ms_regs ms3) 25) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 25 25%bv eq_refl)).
assert (E32 : ew E 32 = getr (c_regs cx) (Z_to_bv 5 1)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 0)).
assert (E33 : ew E 33 = getr (c_regs cx) (Z_to_bv 5 8)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 1)).
assert (E34 : ew E 34 = getr (c_regs cx) (Z_to_bv 5 9)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 2)).
assert (E35 : ew E 35 = getr (c_regs cx) (Z_to_bv 5 18)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 3)).
assert (E36 : ew E 36 = getr (c_regs cx) (Z_to_bv 5 19)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 4)).
assert (E37 : ew E 37 = getr (c_regs cx) (Z_to_bv 5 20)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 5)).
assert (E38 : ew E 38 = getr (c_regs cx) (Z_to_bv 5 21)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 6)).
assert (E39 : ew E 39 = getr (c_regs cx) (Z_to_bv 5 22)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 7)).
assert (E40 : ew E 40 = getr (c_regs cx) (Z_to_bv 5 23)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 8)).
assert (E41 : ew E 41 = getr (c_regs cx) (Z_to_bv 5 24)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 9)).
assert (E42 : ew E 42 = getr (c_regs cx) (Z_to_bv 5 25)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 10)).
assert (E43 : ew E 43 = getr (c_regs cx) (Z_to_bv 5 26)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 11)).
assert (E44 : ew E 44 = getr (c_regs cx) (Z_to_bv 5 27)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 12)).
assert (E45 : ew E 45 = Z_to_bv 64 (pFL cx fp)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 13)).
assert (U8 : bv_unsigned (ew E 8) = spZ (c_regs cx)) by (rewrite E8, Rs0; unfold w64; apply unsigned_lit_small; lia).
assert (U20 : bv_unsigned (ew E 20) = pF cx fp) by (rewrite E20, R20; unfold w64; apply unsigned_lit_small; lia).
assert (U23 : bv_unsigned (ew E 23) = pF cx fp) by (rewrite E23, R23; unfold w64; apply unsigned_lit_small; lia).
assert (U25 : bv_unsigned (ew E 25) = pSH cx fp) by (rewrite E25, R25; unfold w64; apply unsigned_lit_small; lia).
assert (U45 : bv_unsigned (ew E 45) = pFL cx fp) by (rewrite E45; apply unsigned_lit_small; lia).
assert (HS : st_ok_pi SEGS VAL E (mkSS PP_leave sr_atoms bt2_rs None bt2_facts) (restrict (w_H W3) ms3)).
{ rewrite HEdef. rewrite HEdef in U8, U20, U23, U25, U45, E32, E33, E34, E35, E36, E37, E38, E39, E40, E41, E42, E43, E44, E45.
  apply entryR; try assumption; [vm_compute; reflexivity | | |].
  - unfold bt2_rs. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite U8. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      * apply (chunk_saved _ _ _ _ _ _ _ _ _ E32 eq_refl (Z.eq_refl _)).
        replace (spZ (c_regs cx) + -8) with (spZ (c_regs cx) - 8) by lia. exact Hs8.
      * apply (chunk_saved _ _ _ _ _ _ _ _ _ E33 eq_refl (Z.eq_refl _)). replace (spZ (c_regs cx) + -16) with (spZ (c_regs cx) - 16 - 8 * 0) by lia. exact (Hsj 0 ltac:(lia)).
      * apply (chunk_saved _ _ _ _ _ _ _ _ _ E34 eq_refl (Z.eq_refl _)). replace (spZ (c_regs cx) + -24) with (spZ (c_regs cx) - 16 - 8 * 1) by lia. exact (Hsj 1 ltac:(lia)).
      * apply (chunk_saved _ _ _ _ _ _ _ _ _ E35 eq_refl (Z.eq_refl _)). replace (spZ (c_regs cx) + -32) with (spZ (c_regs cx) - 16 - 8 * 2) by lia. exact (Hsj 2 ltac:(lia)).
      * apply (chunk_saved _ _ _ _ _ _ _ _ _ E36 eq_refl (Z.eq_refl _)). replace (spZ (c_regs cx) + -40) with (spZ (c_regs cx) - 16 - 8 * 3) by lia. exact (Hsj 3 ltac:(lia)).
      * apply (chunk_saved _ _ _ _ _ _ _ _ _ E37 eq_refl (Z.eq_refl _)). replace (spZ (c_regs cx) + -48) with (spZ (c_regs cx) - 16 - 8 * 4) by lia. exact (Hsj 4 ltac:(lia)).
      * apply (chunk_saved _ _ _ _ _ _ _ _ _ E38 eq_refl (Z.eq_refl _)). replace (spZ (c_regs cx) + -56) with (spZ (c_regs cx) - 16 - 8 * 5) by lia. exact (Hsj 5 ltac:(lia)).
      * apply (chunk_saved _ _ _ _ _ _ _ _ _ E39 eq_refl (Z.eq_refl _)). replace (spZ (c_regs cx) + -64) with (spZ (c_regs cx) - 16 - 8 * 6) by lia. exact (Hsj 6 ltac:(lia)).
      * apply (chunk_saved _ _ _ _ _ _ _ _ _ E40 eq_refl (Z.eq_refl _)). replace (spZ (c_regs cx) + -72) with (spZ (c_regs cx) - 16 - 8 * 7) by lia. exact (Hsj 7 ltac:(lia)).
      * apply (chunk_saved _ _ _ _ _ _ _ _ _ E41 eq_refl (Z.eq_refl _)). replace (spZ (c_regs cx) + -80) with (spZ (c_regs cx) - 16 - 8 * 8) by lia. exact (Hsj 8 ltac:(lia)).
      * apply (chunk_saved _ _ _ _ _ _ _ _ _ E42 eq_refl (Z.eq_refl _)). replace (spZ (c_regs cx) + -88) with (spZ (c_regs cx) - 16 - 8 * 9) by lia. exact (Hsj 9 ltac:(lia)).
      * apply (chunk_saved _ _ _ _ _ _ _ _ _ E43 eq_refl (Z.eq_refl _)). replace (spZ (c_regs cx) + -96) with (spZ (c_regs cx) - 16 - 8 * 10) by lia. exact (Hsj 10 ltac:(lia)).
      * apply (chunk_saved _ _ _ _ _ _ _ _ _ E44 eq_refl (Z.eq_refl _)). replace (spZ (c_regs cx) + -104) with (spZ (c_regs cx) - 16 - 8 * 11) by lia. exact (Hsj 11 ltac:(lia)).
    + rewrite U23. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). exact (proj1 (HFpres (pF cx fp + o) ltac:(lia))).
    + rewrite U20. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_saved _ _ _ _ _ _ _ _ _ E45 (eq_sym (unsigned_lit_small (pFL cx fp) ltac:(lia))) (Z.eq_refl _)).
      exact Hh120.
    + rewrite U25. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). exact (proj1 (HFSpres o ltac:(lia))).
    + rewrite U45. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). replace (pFL cx fp + o) with (pFL cx fp) by lia. exact HFLpres.
  - apply pairwise_disjoint_of_extents. unfold bt2_rs, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U8, U23, U20, U25, U45.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  - split; [|split; exact I]. cbn [bt2_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U20. change (2 ^ 6) with 64. repeat match goal with |- _ /\ _ => split end; first [exact I | lia]. }
clear HEdef EL.
paj_run_flag_sh RUNF HS HJ.
{ unfold PE_CID. lia. }
{ intros a (r & Hinr & Hr). cbn [ss_mem] in Hinr. unfold bt2_rs in Hinr. cbn [In] in Hinr.
  destruct Hinr as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr.
  - rewrite U8 in Hr. lia.
  - rewrite U23 in Hr. left. apply (awr_ownframe _ _ _ _ _ _ cx fp a Efa). left. lia.
  - rewrite U20 in Hr. lia.
  - rewrite U25 in Hr. left. apply (awr_ownframe _ _ _ _ _ _ cx fp a Efa). right. lia.
  - rewrite U45 in Hr. right. rewrite EFL. lia. }
{ intros msr HSr. rewrite EFL.
  pose proof (st_ok_pi_region_nth E _ msr 4 _ HSr eq_refl) as HR.
  pose proof (field_of_region E (ms_mem msr) 45%nat (pFL cx fp) _ _ _ _ _ 0 1%N (SLit 0) 0 HR U45
    ltac:(left; reflexivity) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V.
  specialize (V 0%nat ltac:(cbv; lia)). cbn [Z.of_nat] in V. rewrite !Z.add_0_r in V. exact V. }
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10.
prreg HS (Z_to_bv 5 2) P2. prreg HS (Z_to_bv 5 3) P3. prreg HS (Z_to_bv 5 4) P4. prreg HS (Z_to_bv 5 8) P8.
prreg HS (Z_to_bv 5 9) P9. prreg HS (Z_to_bv 5 18) P18. prreg HS (Z_to_bv 5 19) P19. prreg HS (Z_to_bv 5 20) P20.
prreg HS (Z_to_bv 5 21) P21. prreg HS (Z_to_bv 5 22) P22. prreg HS (Z_to_bv 5 23) P23. prreg HS (Z_to_bv 5 24) P24.
prreg HS (Z_to_bv 5 25) P25. prreg HS (Z_to_bv 5 26) P26. prreg HS (Z_to_bv 5 27) P27.
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _
  (fun a => (pF cx fp <= a < pF cx fp + 8) \/ (pSH cx fp <= a < pSH cx fp + 16) \/ (pFL cx fp <= a < pFL cx fp + 1)) HFr
  ltac:(intros bbW wloW whiW aW HinW HrrW; vm_compute in HinW;
        repeat (destruct HinW as [HqW | HinW]; [injection HqW as <- <- <-; cbn [base_val] in HrrW;
          rewrite ?U8, ?U20, ?U23, ?U25, ?U45 in HrrW; cbv beta; lia|]);
        destruct HinW)) as UN.
pose proof (frm_off_imgP B ly3 S3 W3 (ms_mem ms3) md3 PE_CID fp HAR Hfin) as Hfimg.
rewrite Efa in Hfimg. change (fs_frame_bytes PE_CID) with 128 in Hfimg.
unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in Hfimg.
eapply (NEXT cx k acc ly3 (stack_free_state PE_CID fp S3) W3
  (mkst (ms_regs ms) (Z_to_bv 64 (BASE + PP_ret)) (ms_mem ms) (seg_rom SEGS)) _ HB).
- exact (gx_pack0 cx _ memS _ _ _ _ _ _ HJ Hag).
- change (del_pos (frames S3) PE_CID fp = []). rewrite Hfrs. cbn [del_pos]. rewrite !Z.eqb_refl. reflexivity.
- apply (mo_le_set_fs_r MT MFSL). exact Hmo.
- unfold GI_ret. cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr mkst ms_regs ms_mem].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|].
  split.
  { intros r Hr. unfold acallee_saved in Hr.
    assert (Hr' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
      r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    destruct Hr' as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]].
    - rewrite P2, E8, Rs0. unfold w64, spZ. apply Z_to_bv_bv_unsigned.
    - rewrite P3, E3. exact Rgp.
    - rewrite P4, E4. exact Rtp.
    - rewrite P8. exact E33.
    - rewrite P9. exact E34.
    - rewrite P18. exact E35.
    - rewrite P19. exact E36.
    - rewrite P20. exact E37.
    - rewrite P21. exact E38.
    - rewrite P22. exact E39.
    - rewrite P23. exact E40.
    - rewrite P24. exact E41.
    - rewrite P25. exact E42.
    - rewrite P26. exact E43.
    - rewrite P27. exact E44. }
  split; [rewrite Q1; exact E32|].
  split; [exact Q10|].
  split; [exact Hk|]. split; [exact Hacc|].
  split.
  { assert (EA : ablocks B ly3 (stack_free_state PE_CID fp S3) = ablocks B ly3 S3)
      by (unfold ablocks; rewrite blocks_stack_free_state; reflexivity).
    rewrite EA. rewrite app_nil_r in Hperm. exact Hperm. }
  split; [rewrite (proj1 (fs_wvb md3 mat)); exact Hfds|].
  split; [rewrite (proj2 (fs_wvb md3 mat)); exact Hfs|].
  split.
  { apply (asource_none_frame KS (rdW W3 (ms_mem ms3))); [|exact Hsrc].
    intros a Ha. apply (mbyte_of_aview SEGS).
    destruct (asil_env _ _ _ _ ASIL a Ha) as (Hi & _).
    assert (HaF : a <> pFL cx fp) by (intros ->; exact (HFLimg Hi)).
    pose proof (pa_segs_low a Hi) as Ha1. pose proof (pa_img_range a Hi) as Ha2.
    unfold pcap_img_end, YImgTop.IMG_TOP in Ha2.
    apply UN; [lia | cbv beta; lia]. }
  { apply (garr8_frame SEGS _ _ _ _ Hin). intros a Ha. apply (mbyte_of_aview SEGS).
    rewrite length_map in Ha. fold (c_n cx) in Ha.
    assert (Hcn : 0 < c_n cx) by lia. pose proof (input_block cx ly3 S3 _ HB Hperm Hcn) as Hpin.
    destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hpin) as (_ & _ & _ & Hpapp & Hpown & _).
    pose proof (req_size_pos (c_n cx) ltac:(lia)) as Hrq.
    pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ _ _ PE_CID fp HAR Hpin Hfin) as D.
    unfold zdisjoint in D. cbn [fst snd] in D. rewrite Efa in D. change (fs_frame_bytes PE_CID) with 128 in D.
    assert (HaF : a <> pFL cx fp) by (intros ->; exact (proj2 (Hpown (pFL cx fp) ltac:(lia)) HFLown)).
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hpapp.
    assert (HSHk : pSH cx fp + 16 <= 0x10007fff8000).
    { unfold pSH, shadow_of_addr, SHADOW_OFF. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hfapp.
      Z.div_mod_to_equations. lia. }
    apply UN; [lia | cbv beta; lia]. }
Qed.

(* ---- ret: PP_ret 0x81214, the `ret`, to the post-condition of the whole call ---------------------------------- *)

Lemma garr8_mbyte_eq : forall (m m' : word -> option byte) p l i,
  garr8 SEGS m p l -> garr8 SEGS m' p l -> 0 <= i < Z.of_nat (length l) -> mbyte SEGS m' (p + i) = mbyte SEGS m (p + i).
Proof.
  intros m m' p l i H H' Hi.
  destruct (H (Z.to_nat i) ltac:(lia)) as [V _]. destruct (H' (Z.to_nat i) ltac:(lia)) as [V' _].
  specialize (V 0%nat ltac:(lia)). specialize (V' 0%nat ltac:(lia)).
  rewrite Z2Nat.id in V, V' by lia. cbn [Z.of_nat] in V, V'. rewrite Z.add_0_r in V, V'. rewrite V, V'. reflexivity.
Qed.

Lemma tail_ret : pe_from_ret SK B MT KS (pe_post SK B MT KS) (GI_ret B MT KS).
Proof.
intros cx k acc ly3 S3 W3 ms3 md3 HB HJ Hfrs Hmo HG.
destruct HG as (Hpc & Hresv & Hsvc & Hrom & Hfrg & Hfcsr & Hpres & Hra & Ha0 & Hk & Hacc & Hperm & Hfds & Hfs & Hnone & Hin).
pose proof HB as ((HAR0 & Hrok & _) & _ & _ & _ & _ & Hgin & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hmok & Hneed & _).
pose proof (entry0 PP_ret ms3 W3 Hpc Hresv Hsvc Hrom Hfrg Hfcsr) as HS.
eapply (RET W3 _ _ ms3 md3 _ HS eq_refl); [vm_compute; reflexivity|].
intros mat'. unfold pe_post.
exists ly3, S3, (ms_regs ms3), (ms_mem ms3), (with_vm_backing (m_vm_lazy md3) mat' md3), k.
split; [rewrite Hra; unfold YK0s.ret_ok in Hrok; rewrite Hrok; reflexivity|].
split; [apply ajournal_gx_materialize; first [exact LAWS | exact pa_segs_low | exact HJ]|].
split; [exact Hk|]. split; [exact Hpres|]. split; [exact Ha0|]. split; [exact Hperm|].
split; [rewrite (proj1 (fs_wvb md3 mat')); exact Hfds|].
split; [rewrite (proj2 (fs_wvb md3 mat')); exact Hfs|].
split; [exact Hnone|].
split; [apply (mle_weaken MT _ _ acc _ MLAWS Hmo); pose proof (PA_K12_need MT MLAWS cx); lia|].
intros i Hi. unfold aview. f_equal. apply (garr8_mbyte_eq _ _ _ _ i Hgin Hin). rewrite length_map. unfold c_n in Hi. lia.
Qed.

End c.
End b.
End a.


(* The sink head is EXPLICIT on every exported statement that depends on it (a Theorem Labs lane, 21:57Z): the only global
   sink_head instance in this closure is the plain build's, so it must never be inferred. *)
Arguments tail_W {fx rc} SK {PI}.
Arguments tail_KW {fx rc} SK {PI}.
Arguments tail_W5 {fx rc} SK {PI}.
Arguments tail_close6 {fx rc} SK {PI}.
Arguments tail_R2 {fx rc} SK {PI}.
Arguments tail_R1 {fx rc} SK {PI}.
Arguments tail_R3 {fx rc} SK {PI}.
Arguments tail_R4 {fx rc} SK {PI}.
Arguments tail_R5 {fx rc} SK {PI}.
Arguments gx_open {rc} SK {PI}.
Arguments gx_pack0 {rc} SK {PI}.
Arguments tail_R6 {fx rc} SK {PI}.
Arguments tail_R7 {fx rc} SK {PI}.
Arguments tail_K12r {fx rc} SK {PI}.
Arguments tail_leave {fx rc} SK {PI}.
Arguments tail_ret {fx rc} SK {PI}.



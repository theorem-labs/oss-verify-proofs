From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Written by Theorem Labs, 2026-10 (a Theorem Labs lane), for libreac/fuzz_pcap v1.9.0 (ASan build).

   WHAT THIS FILE PROVES. a Theorem Labs lane's afmemopen_spec (lib/A/Stdio/PFmemopenISpec.v, a working branch
   8fe833c8d36; Definition byte-identical to bd307b59958), statement UNCHANGED, for pcap's ASan fmemopen wrapper:
   theorem pcap_afmemopen_spec below is
   afmemopen_spec SK tfibsegs B K MT CTX 0x415c4 ra 0x10350 0x10370. The C library's fmemopen enters only as a
   Section hypothesis at the REAL call: a Theorem Labs lane's rfmemopen_contract (lib/A/Stdio/PFmemopenM.v,
   a working branch 7504d592f23, Definitions byte-identical to c53fee70393: rfmemopen_post carries md
   and ends with
   m_fds md' = m_fds md /\ m_fs md' = m_fs md - this lane asked for that clause, because the sink token alone
   lets aos_step change the sink fd and path and the tail call takes md' from this post alone), instantiated at
   (PFMEMOPEN 0x8e870, ra, 0x10350, 0x10370) with the same K and CTX. rfmemopen_contract takes amalloc04_rule
   (YC5d.v:56) as a premise, so that rule is a Section hypothesis too. The only other hypotheses are the image's
   own laws: AR_laws, PcapSyms (A/AF0m.v) and a Theorem Labs lane's asource_img_laws (A/Stdio/PSourceMeta.v), the last
   carried as PFclose.v:107 (a working branch 3fc82453590) carries it, discharged once at
   instantiation.
   THE CONSTANT WINDOW [0x10350, 0x10370) (__strchrnul's two 8-byte constants, read by fmemopen's strchr calls;
   cgif's MC_LO / MC_HI, A/AE39.v:26-31; the same window on both pcap pins, auditor 00:27Z). Both statements
   take it as a premise, the image's bytes there. The run writes only [sp - 48, sp), far above it, so the walk
   carries it from the entry memory to the REAL call in one step (fm_window at the REAL call below), the move
   cgif's mconsts_view_keep (A/AE39.v:42) makes across calls.

   THE CODE (measured on the pin fuzz_pcap.asan, sha256 b7a91d9b1fb0017d..., listing
   fuzz_pcap.objdump.txt (sha256 bf9d80d6e30f; internal record)):
     0x415c4 `j 0x46644`                                        (objdump.txt:18220-18221, the trampoline)
     0x46644 ___interceptor_fmemopen, 20 instructions           (objdump.txt:23464-23484):
       addi sp,-32; sd ra/s0/s1/s2; mv s0,a2; mv s1,a1; mv s2,a0; jal 0x59894 TryAsanInitFromRtl;
       auipc a0 + ld t1,-128(a0) from 0x9b5e8 (__interception::real_fmemopen); mv a0,s2; mv a1,s1; mv a2,s0;
       ld ra/s0/s1/s2; addi sp,32 (0x4668c); jr t1 (0x46690, a TAIL jump)
     0x59894 __asan::TryAsanInitFromRtl, frame 16                (objdump.txt:43352-43392)
   The walk is ONE symbolic run (fm_front) from 0x415c4 to 0x8e870 over tbl_icpt plus the 20 words at 0x46644
   (tbl_fm; tbl_fm_probe checks the words against the image). At 0x8e870 sp, ra, gp, tp and s0..s11 are the
   caller's again (shapeM), a0..a2 are the caller's arguments, and only the 48 bytes [sp - 48, sp) were written
   (32 for the wrapper, 16 for TryAsanInitFromRtl). So the frame chain (CTX, ch) passes to the REAL call
   UNCHANGED: the wrapper adds no return address (a Theorem Labs lane's measurement; here it is shapeM's s0 / ra clauses).

   THE ERROR EDGES ARE PROVED UNREACHABLE, NOT BUDGETED. The wrapper has no READ_RANGE, no report call and no
   CheckFailed call. Its one callee, TryAsanInitFromRtl, has one escape: `bne a1,a0,0x598c8` at 0x598b4, taken
   when the byte __asan::asan_inited (0xa2598) is not 1; that path does the lr/sc on asan_init_is_running and
   calls AsanInitInternal 0x595e0, whose CHECKs reach CheckFailed. The run reads asan_inited from the AR const
   law (fm_const, through PcapSyms' Tfib_const) as 1, so the branch is decided not-taken inside the run:
   escape_operands states the two operands at 0x598b4 (a1 = 1, a0 = 1), and r_M ends RS_running AT 0x8e870, which
   a run through 0x598c8 cannot do (AsanInitInternal is outside tbl_fm, so such a run stops at its first word).
   E-PEND: that value is AF0m.v:83 `z1 (ANum 0xa2598) 0x1 (* E-PEND pcrel/RT *)` on a working branch
   3820d10f234 (WIP, pending af0m.py); the auditor measured the same cell independently at 22:52Z. The store
   that sets it is AsanInitInternal's `sb a0,0(s3)` at 0x597b8, with s3 = 0xa2598 from 0x595f8 / 0x595fc
   (objdump.txt:43184-43185, :43296; s3 is reloaded only on the early-return path at 0x59620). NOT the `sw` at
   0x5971c, which stores through the GOT cell 0x99888, a different runtime cell. No step of this proof reads
   either store: the walk takes asan_inited = 1 from the AR const law (fm_const). If af0m.py changes that cell,
   fm_const_chk fails and this file must be re-checked.
   THE REAL CELL: 0x9b5e8 -> 0x8e870 is AF0m.v:244 Tfib_const_abs `z8 (ANum 0x9b5e8) 0x8e870` (M-IMG, added by
   a Theorem Labs lane at bd2fdd5e81f on this lane's request; this lane measured the same value in the pin's PT_LOAD).

   NO META-REGION PREMISE (class R2). afmemopen_spec has no (M : Z) and no asrc_meta_inv, and needs none: the
   20 wrapper instructions and TryAsanInitFromRtl's taken path (objdump.txt:23464-23484, 43352-43365) touch no
   AddrHashMap / FileMetadata cell and have no path to CheckFailed at 0x6b918 (ruling relayed by a Theorem Labs lane).

   THE IMAGE. segs := tfibsegs (the pin image) and pc := 0x415c4; B, K, MT, CTX, ra and SK stay general. The
   stdio cells K names cannot collide with the 48 stack bytes the wrapper writes: asil_env (PSourceMeta.v:80)
   puts every address of asrc_env_addr K inside the image, and fm_segs_low puts the image below kLowMemEnd,
   which is below alloc_ceiling and so below the stack floor.

   THE STACK. The run needs 48 bytes below sp; the contract needs RFMEMOPEN_STK = 48 + ASTACK = 16432 at the SAME
   sp (the tail jump restores sp). Both are below AFMEMOPEN_STK = 18624, so afn_pre at 18624 gives the contract's
   afn_pre at 16432, and the two journals compose (ajournal_sub_tok, A/Prog/YC85.v) into the 18624 journal the
   statement asks for, with the footprint [YI16.sink_token] on both sides.

   SOURCES. The run, its shape check and the frame / AR transfer follow cgif's iopen_front (lib/A/AE2g.v:93); the
   overall shape (front run, callee hypotheses, journal composition) follows cgif's tfib_afopen_spec
   (lib/A/AE25.v:195). Both are read from the DONOR ref origin/ossv/recipes c8557374ad2e,
   proofs/cgif/cgif_file_fuzzer, because the relocated AE2g / AE25 are held out of a working branch. The relocated layer
   used here (AB1v, AE34, AF0l, AF0m, AF0x, AE2y) is a working branch 3820d10f234.
   rule 24: pcapmemopeni-fmemopen-icpt.txt (sha256 8c3dffd65a3d; internal record) (the proof index exit 1, index built 2026-10-28T21:58:24Z),
   pcapmemopeni-gitgrep.txt (sha256 75264fbb8006; internal record) (git grep of the names on the four released refs, exit 1) and a fresh
   read-only scout's CONFIRM (a Theorem Labs lane): no released proof of this function. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PcapImgEnd YImgTop.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A Require Import AB1v AE34 AF0l AF0m AF0x AE2y.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YI16 YCbq YC20 YC5d.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import YC85.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PSource PSourceMeta PFmemopenISpec PFmemopenM.
(* The asan stdio pcs (PFMEMOPEN, FM_MALLOC_RA) come from their single home, PStdioImgA (a Theorem Labs lane,
   02:27Z); Required after PFmemopenM so its names are the ones in scope. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PStdioImgA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Definition FM_ENTRY : Z := (symaddr Symbols.Asan.s___wrap_fmemopen).
(* 32 bytes of wrapper frame (0x46644) and 16 of TryAsanInitFromRtl's (0x59894). *)
Definition FM_WIN : Z := 48.

(* tbl_icpt (AE34.v) holds the trampoline block (0x4155c, 38 words) and TryAsanInitFromRtl (0x59894, 40); the
   wrapper's 20 words are added here. *)
Definition fm_ranges : list (Z * nat) := [((symaddr Symbols.Asan.s___interceptor_fmemopen), 20%nat)].
Definition tbl_fm : ctable := Eval vm_compute in build_ranges fm_ranges tbl_icpt.
Lemma tbl_fm_eq : tbl_fm = build_ranges fm_ranges tbl_icpt.
Proof. vm_cast_no_check (eq_refl tbl_fm). Qed.
Lemma tbl_fm_ok : table_ok tfibsegs tbl_fm.
Proof.
rewrite tbl_fm_eq. apply build_ranges_ok; [| apply tbl_icpt_ok].
unfold fm_ranges. repeat constructor; cbn; discriminate.
Qed.
(* The words read out of the image (the table is built from tfibsegs): the trampoline's `j`, the wrapper's first
   and last words (`addi sp,sp,-32`, `jr t1`), TryAsanInitFromRtl's first word and its escape test `bne a1,a0`;
   REAL fmemopen 0x8e870 and AsanInitInternal 0x595e0 are NOT in the table. *)
Lemma tbl_fm_probe :
clookup tbl_fm (symaddr Symbols.Asan.s___wrap_fmemopen) = Some 0x0800506f /\ clookup tbl_fm (symaddr Symbols.Asan.s___interceptor_fmemopen) = Some 0xfe010113 /\
clookup tbl_fm (symaddr (Symbols.Asan.s___interceptor_fmemopen + 0x4c)%Z) = Some 0x00030067 /\ clookup tbl_fm (symaddr Symbols.Asan.s__ZN6__asan18TryAsanInitFromRtlEv) = Some 0xff010113 /\
clookup tbl_fm (symaddr (Symbols.Asan.s__ZN6__asan18TryAsanInitFromRtlEv + 0x20)%Z) = Some 0x00a59a63 /\ clookup tbl_fm PFMEMOPEN = None /\ clookup tbl_fm (symaddr Symbols.Asan.s__ZN6__asanL16AsanInitInternalEv) = None.
Proof. vm_compute. repeat split; reflexivity. Qed.

Lemma fm_phase_to : forall (W : world tfibsegs) E stop ss ss' st ms md,
st_ok tfibsegs E ss (restrict (w_H W) ms) ->
sym_run_toN tfibsegs tbl_fm FUEL stop ss = (ss', st) ->
SRr tfibsegs W (mkCfg ms md)
(fun W' c' => W' = W /\ exists ms1 mat1, c' = mkCfg ms1 (with_vm_backing (m_vm_lazy md) mat1 md) /\
match st with RS_ecall => st_ok_ecall tfibsegs E ss' (restrict (w_H W) ms1)
| _ => st_ok tfibsegs E ss' (restrict (w_H W) ms1) end /\
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms1) /\
frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms1))).
Proof.
intros W E stop ss ss' st ms md HS Hrun.
eapply (SRr_run_to_gen tfibsegs tbl_fm tbl_fm_ok AF0x.Hwx_tfa W FUEL stop E ss ss' st ms md _ HS Hrun).
intros ms1 mat1 HS1 HF HFr. apply SRr_ret. split; [reflexivity|]. exists ms1, mat1. split; [reflexivity|].
split; [exact HS1|]. split; [exact HF | exact HFr].
Qed.

(* The two runtime cells the run reads, from the AR const law (PcapSyms' Tfib_const, AF0m.v at a working branch
   3820d10f234): asan_inited = 1 (E-PEND, AF0m.v:83) and the REAL(fmemopen) slot 0x9b5e8 = 0x8e870 (M-IMG, :244). *)
Definition fm_const : list (Z * Z * list (Z * N * Z)) :=
[ ((symaddr Symbols.Asan.s__ZN6__asanL11asan_initedE), 1, [(0, 1%N, 1)]); ((symaddr Symbols.Asan.s__ZN14__interception13real_fmemopenE), 8, [(0, 8%N, PFMEMOPEN)]) ].
Lemma fm_const_chk : forall ly, rodata_chk ly fm_const = true.
Proof. intros ly. vm_compute. reflexivity. Qed.

Definition stkM : YP09.region := YP09.mkRegion (Some 2%nat) (- FM_WIN) 0 (- FM_WIN) 0 [].
Definition memM : smem := stkM :: map ro_region fm_const.
Definition ssM : sstate := mkSS FM_ENTRY sr_atoms memM None (mkFacts [(2%nat, mkAF (2^44) (2^47) 4)] [] []).
Definition fm_RUNTO (stop : Z) (s : sstate) := sym_run_toN tfibsegs tbl_fm FUEL stop s.
Definition fm_RG (s : sstate) (r : Z) : sv := sr_get (ss_regs s) (Z_to_bv 5 r).
Definition fm_reg_is (ss : sstate) (r : Z) (v : sv) : bool := sv_eqb (fm_RG ss r) v.
Definition eM : sstate := Eval vm_compute in fst (fm_RUNTO PFMEMOPEN ssM).
Lemma r_M : fm_RUNTO PFMEMOPEN ssM = (eM, RS_running). Proof. vm_compute. reflexivity. Qed.
(* The escape test, stated on its own: run to 0x598b4 and read the two operands of `bne a1,a0`. *)
Definition eB : sstate := Eval vm_compute in fst (fm_RUNTO (symaddr (Symbols.Asan.s__ZN6__asan18TryAsanInitFromRtlEv + 0x20)%Z) ssM).
Lemma r_B : fm_RUNTO (symaddr (Symbols.Asan.s__ZN6__asan18TryAsanInitFromRtlEv + 0x20)%Z) ssM = (eB, RS_running). Proof. vm_compute. reflexivity. Qed.
Lemma escape_operands : ss_pc eB = (symaddr (Symbols.Asan.s__ZN6__asan18TryAsanInitFromRtlEv + 0x20)%Z) /\ fm_RG eB 11 = SLit 1 /\ fm_RG eB 10 = SLit 1.
Proof. vm_compute. repeat split; reflexivity. Qed.
(* At REAL fmemopen: ra and a0..a2 are the entry's, every callee-saved register (sp included) is the entry's, the
   stack window is [sp - 48, sp) and every other region is read-only. *)
Definition KEPTM : list Z := [1; 10; 11; 12].
Definition shapeM (ss : sstate) : bool :=
(ss_pc ss =? PFMEMOPEN) && match ss_resv ss with None => true | _ => false end &&
forallb (fun r => fm_reg_is ss r (SOff (Z.to_nat r) 0)) KEPTM &&
forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) CALLEE_SAVED &&
match ss_mem ss with r0 :: _ => obase_eqb (YP09.r_base r0) (Some 2%nat) && (YP09.r_wlo r0 =? - FM_WIN) && (YP09.r_whi r0 =? 0) | _ => false end &&
forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) (skipn 1 (ss_mem ss)).
Lemma shapeM_ok : shapeM eM = true. Proof. vm_compute. reflexivity. Qed.

Lemma fm_segs_low : forall a, in_img tfibsegs a -> 0 <= a < kLowMemEnd.
Proof.
intros a (sg & Hin & Hr). unfold kLowMemEnd.
unfold tfibsegs, Asan.M.loaded_segments in Hin. cbn in Hin.
destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn in Hr; lia.
Qed.

Lemma fds_fs_of_sbm : forall md md', same_but_materialized md md' -> m_fds md' = m_fds md /\ m_fs md' = m_fs md.
Proof.
intros md md' H. pose proof (same_but_materialized_frame _ _ H) as (_ & _ & _ & _ & _ & _ & _ & _ & E1 & _ & _ & E2 & _).
split; assumption.
Qed.

Section d.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : PcapSyms B.

(* The trampoline, the wrapper and TryAsanInitFromRtl, as one run to REAL fmemopen (cgif AE2g.v:93's form). *)
Theorem fm_front : forall ly S (W : world tfibsegs) regs mem md,
AR tfibsegs B ly S W mem md ->
spZ regs mod 16 = 0 -> ly_stk_lo ly + FM_WIN <= spZ regs -> spZ regs <= ly_stk_hi ly ->
(forall a, spZ regs - FM_WIN <= a < spZ regs -> apresent (w_H W) mem a) ->
SRr tfibsegs W (cfg_at tfibsegs FM_ENTRY regs mem md)
(fun W' c' => W' = W /\ exists regs1 mem1 md1,
c' = cfg_at tfibsegs PFMEMOPEN regs1 mem1 md1 /\ same_but_materialized md md1 /\ AR tfibsegs B ly S W mem1 md1 /\
(forall r, In r KEPTM -> getr regs1 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) /\
aregs_preserved regs regs1 /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - FM_WIN <= a < spZ regs) -> aview tfibsegs (w_H W) mem1 a = aview tfibsegs (w_H W) mem a) /\
(forall a, spZ regs - FM_WIN <= a < spZ regs -> apresent (w_H W) mem1 a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem1 a)).
Proof.
intros ly S W regs mem md HAR Hal16 Hslo Hshi HpresE.
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg).
unfold kHighMemBeg, kHighMemEnd in Lbeg, Lhi.
unfold FM_WIN in *.
set (sp0 := spZ regs) in *. set (H := w_H W) in *.
assert (Hsp : 2 ^ 44 <= sp0 <= 2 ^ 47) by (subst sp0; lia).
pose proof AF0x.Hwx_tfa as Hwx.
set (EE := AE2y.Env regs []).
assert (EEreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE i = getr regs r) by (intros; apply AE2y.Env_reg; assumption).
assert (EE2 : bv_unsigned (ew EE 2) = sp0) by (rewrite (EEreg 2%nat 2%bv eq_refl); reflexivity).
unfold cfg_at at 1. change (w64 FM_ENTRY) with (Z_to_bv 64 FM_ENTRY).
assert (HS0 : st_ok tfibsegs EE ssM (restrict H (mkst regs (Z_to_bv 64 FM_ENTRY) mem (seg_rom tfibsegs)))).
{ unfold ssM. rewrite restrict_mkst_fx. unfold EE, AE2y.Env. apply (entry_st_ok_full tfibsegs);
change (Ereg regs (map (Z_to_bv 64) [])) with EE.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- unfold memM. apply Forall_cons.
{ unfold stkM, FM_WIN. apply (region_ok_stack tfibsegs EE _ 2 sp0 (- 48)); [exact EE2 | lia | lia |].
intros a Ha. apply AE2y.apresent_writable. apply HpresE. lia. }
exact (AE2y.rodata_ok B TB fm_const ly S H mem EE (fm_const_chk ly) (proj1 HAR)).
- apply pairwise_disjoint_of_extents. unfold memM, stkM, fm_const, ro_region, extent_of_region, FM_WIN.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite EE2.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite EE2. change (2 ^ 4) with 16. repeat split; try lia; exact Hal16. }
eapply SRr_bind; [exact (fm_phase_to W EE PFMEMOPEN ssM eM RS_running _ md HS0 r_M)|].
intros W1' c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). apply SRr_ret. split; [reflexivity|].
assert (MEQ1 : forall z : word, ~ (sp0 - 48 <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. apply (HF1 z). intros Hin.
pose proof (in_wrange_single_b EE memM (bv_unsigned z) 2 (- 48) 0 sp0 ltac:(vm_compute; reflexivity) EE2 Hin). lia. }
clear HF1 HFr1.
pose proof shapeM_ok as Hsh. unfold shapeM in Hsh.
apply andb_prop in Hsh as [Hsh Hro]. apply andb_prop in Hsh as [Hsh Hwin]. apply andb_prop in Hsh as [Hsh HCS].
apply andb_prop in Hsh as [Hsh HK]. apply andb_prop in Hsh as [Hpc Hrv]. apply Z.eqb_eq in Hpc.
assert (Hresv : ss_resv eM = None) by (destruct (ss_resv eM); [discriminate | reflexivity]).
destruct (ss_mem eM) as [|r0 rest] eqn:Hmem; [discriminate |].
apply andb_prop in Hwin as [Hwin W0c]. apply andb_prop in Hwin as [W0a W0b].
apply obase_eqb_eq in W0a. apply Z.eqb_eq in W0b. apply Z.eqb_eq in W0c. unfold FM_WIN in W0b.
assert (RD : forall (r : bv 5) v, fm_reg_is eM (bv_unsigned r) v = true -> getr (ms_regs ms1) r = sv_denot EE v).
{ intros r v Hr. unfold fm_reg_is, fm_RG in Hr. apply sv_eqb_eq in Hr. rewrite Z_to_bv_bv_unsigned in Hr. rewrite <- Hr.
apply (AF0x.st_ok_reg_denot H EE eM ms1 r HS1). }
assert (RK : forall r, In r KEPTM -> getr (ms_regs ms1) (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
{ intros r Hin. assert (Hr : 0 <= r < 32) by (unfold KEPTM in Hin; cbn in Hin; lia).
rewrite forallb_forall in HK. specialize (HK r Hin). cbn beta in HK.
assert (Hu : bv_unsigned (Z_to_bv 5 r) = r).
{ rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. apply Z.mod_small. lia. }
rewrite (RD (Z_to_bv 5 r) (SOff (Z.to_nat r) 0)); [| rewrite Hu; exact HK].
cbn [sv_denot]. rewrite (EEreg (Z.to_nat r) (Z_to_bv 5 r)); [| rewrite Hu; lia].
rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
pose proof (AE2y.aregs_preserved_of_st_ok H EE eM ms1 regs [] HS1 (env_agree_refl 32 EE) HCS) as RP1.
set (regs1 := ms_regs ms1) in *.
pose proof (st_ok_restrict_mkst tfibsegs H EE _ _ HS1 Hresv) as Hshape. rewrite Hpc in Hshape. fold regs1 in Hshape.
rewrite Hshape.
set (md1 := with_vm_backing (m_vm_lazy md) mat1 md) in *.
assert (MF1 : same_but_materialized md md1) by (subst md1; apply with_vm_backing_same).
assert (AV1 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 48 <= a < sp0) -> aview tfibsegs H (ms_mem ms1) a = aview tfibsegs H mem a).
{ intros a Hr Ha. apply AF0x.aview_same. apply MEQ1. rewrite unsigned_lit_small by lia. exact Ha. }
assert (PRS1 : forall a, sp0 - 48 <= a < sp0 -> apresent H (ms_mem ms1) a).
{ intros a Ha.
assert (HN : nth_error (ss_mem eM) 0%nat = Some r0) by (rewrite Hmem; reflexivity).
assert (HB : base_val EE (YP09.r_base r0) + YP09.r_wlo r0 <= a < base_val EE (YP09.r_base r0) + YP09.r_whi r0).
{ rewrite W0a, W0b, W0c. cbn [base_val]. rewrite EE2. lia. }
assert (HT : AF0x.TFIB_IMG_END <= a < 2 ^ 64) by (unfold AF0x.TFIB_IMG_END, pcap_img_end, IMG_TOP; lia).
exact (AF0x.st_ok_window_apresent H EE eM ms1 0%nat r0 a HS1 HN HB HT). }
assert (PM1 : forall a, apresent H mem a -> apresent H (ms_mem ms1) a).
{ intros a Hp. rewrite (AE2y.apresent_mod _ (ms_mem ms1) a). rewrite (AE2y.apresent_mod _ mem a) in Hp.
assert (Ha : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia). set (a' := a mod 2 ^ 64) in *.
destruct (Z_lt_le_dec a' (sp0 - 48)) as [L1|L1]; [|destruct (Z_lt_le_dec a' sp0) as [L3|L3]; [apply PRS1; lia|]];
(apply (AF0x.apresent_same H mem (ms_mem ms1) a'); [apply MEQ1; rewrite unsigned_lit_small by lia; lia | exact Hp]). }
assert (HAR1 : AR tfibsegs B ly S W (ms_mem ms1) md1).
{ pose proof (same_but_materialized_frame md _ MF1) as MF.
apply (al_frame _ _ LAWS ly S W mem md (ms_mem ms1) _ HAR).
+ intros a Hr Hown. apply AV1; [exact Hr|]. intros Hs. exact (al_stack _ _ LAWS ly S W mem md a HAR ltac:(lia) Hown).
+ intros a Hv. rewrite (AE2y.aview_mod _ (ms_mem ms1) a). rewrite (AE2y.aview_mod _ mem a) in Hv.
assert (Hr : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia). set (a' := a mod 2 ^ 64) in *.
destruct (Z_lt_le_dec a' (sp0 - 48)) as [L1|L1]; [rewrite AV1 by lia; exact Hv|].
destruct (Z_lt_le_dec a' sp0) as [L3|L3]; [| rewrite AV1 by lia; exact Hv].
apply AE2y.aview_some_of_apresent. apply PRS1. lia.
+ apply MF. + apply MF. + apply MF.
+ exact (AE2y.hs_kept_win _ _ _ _ _ _ _ _ MEQ1 HpresE ltac:(lia) ltac:(lia)). }
exists regs1, (ms_mem ms1), md1. split; [reflexivity|]. split; [exact MF1|]. split; [exact HAR1|].
split; [exact RK|]. split; [exact RP1|].
split; [exact AV1|]. split; [exact PRS1 | exact PM1].
Qed.

Section e.
Context {SK : YI16.sink_head}.
Variable K : asource_syms.
Variable MT : ameter_ops.
Variable CTX : list (list Z).
Variable ra : Z.
Hypothesis ASIL : asource_img_laws SK tfibsegs B K.
Hypothesis AMR : amalloc04_rule (SK:=SK) tfibsegs B MT.
Hypothesis RFM : rfmemopen_contract (SK:=SK) tfibsegs B K MT CTX PFMEMOPEN ra (symaddr (Symbols.Asan.Sec.s_rodata + 0x70)%Z) (symaddr (Symbols.Asan.Sec.s_rodata + 0x90)%Z).

(* The stream predicate reads only the cells asrc_env_addr K names, and asil_env puts each inside the image. *)
Lemma fm_none_frame : forall (m m' : word -> option byte),
(forall a, in_img tfibsegs a -> mbyte tfibsegs m' a = mbyte tfibsegs m a) ->
asource_none tfibsegs K m -> asource_none tfibsegs K m'.
Proof.
intros m m' Hfr ((Hth & Hnl & Hlk & Hmode & Hms & (cv & Hcv & Hc)) & Hhead).
assert (IMG : forall a, asrc_env_addr K a -> mbyte tfibsegs m' a = mbyte tfibsegs m a).
{ intros a Ha. apply Hfr. exact (proj1 (asil_env _ _ _ _ ASIL a Ha)). }
assert (VM : forall a (n : nat) v, (forall k, (k < n)%nat -> asrc_env_addr K (a + Z.of_nat k)) ->
  val_mem tfibsegs m a n v -> val_mem tfibsegs m' a n v).
{ intros a n v HA Hv k Hk. rewrite (IMG _ (HA k Hk)). exact (Hv k Hk). }
unfold asource_none, asrc_stdio_env, as_ofl_head in *. unfold asrc_env_addr in IMG, VM.
split; [split; [|split; [|split; [|split; [|split]]]]|].
- apply VM; [intros k Hk; left; cbn in Hk; lia | exact Hth].
- apply VM; [intros k Hk; right; left; cbn in Hk; lia | exact Hnl].
- apply VM; [intros k Hk; right; right; left; cbn in Hk; lia | exact Hlk].
- apply (garr8_frame tfibsegs m m' _ _ Hmode). intros x Hx. apply IMG.
  right; right; right; left. cbn [length app src_mode_Z] in Hx. lia.
- apply (garr8_frame tfibsegs m m' _ _ Hms). intros x Hx. apply IMG.
  right; right; right; right; left. cbn [length app src_modeset_Z] in Hx. lia.
- exists cv. split; [exact Hcv|]. apply VM; [intros k Hk; right; right; right; right; right; cbn in Hk; lia | exact Hc].
- apply VM; [intros k Hk; right; right; left; cbn in Hk; lia | exact Hhead].
Qed.

Theorem pcap_afmemopen_spec : afmemopen_spec SK tfibsegs B K MT CTX FM_ENTRY ra (symaddr (Symbols.Asan.Sec.s_rodata + 0x70)%Z) (symaddr (Symbols.Asan.Sec.s_rodata + 0x90)%Z).
Proof.
intros W ly S regs mem md ch b n C _ HPRE HCTX G10 G11 G12 HNONE Hn Hnr HBLK HG HBY HMC Hev Hlive HMO Hu0 HuC.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
assert (FS : AFMEMOPEN_STK = 18624) by reflexivity.
assert (RS : RFMEMOPEN_STK = 16432) by reflexivity.
rewrite FS in Hslo, Hpres, Hstk0, Hbot.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (al_blocks _ _ LAWS ly S W mem md b n HAR HBLK) as (_ & Hb4096 & Hbceil & _).
pose proof (req_size_pos n ltac:(lia)) as [_ Hreq].
eapply SRr_bind.
{ apply (fm_front ly S W regs mem md HAR Hal16); unfold FM_WIN; [lia | exact Hshi | intros a Ha; apply Hpres; lia]. }
intros W1 c1 _ (-> & regs1 & mem1 & md1 & -> & MF1 & HAR1 & RK & RP1 & AV1 & PRS1 & PM1).
unfold FM_WIN in AV1, PRS1.
assert (RK' : forall r (rb : bv 5), In r KEPTM -> Z_to_bv 5 r = rb -> getr regs1 rb = getr regs rb)
  by (intros r rb Hr <-; apply RK; exact Hr).
assert (RP' : forall r (rb : bv 5), acallee_saved r -> Z_to_bv 5 r = rb -> getr regs1 rb = getr regs rb)
  by (intros r rb Hr <-; apply RP1; exact Hr).
assert (R1 : getr regs1 1 = getr regs 1) by (apply (RK' 1); [cbn; tauto | apply bv_eq; reflexivity]).
assert (R10 : getr regs1 10 = getr regs 10) by (apply (RK' 10); [cbn; tauto | apply bv_eq; reflexivity]).
assert (R11 : getr regs1 11 = getr regs 11) by (apply (RK' 11); [cbn; tauto | apply bv_eq; reflexivity]).
assert (R12 : getr regs1 12 = getr regs 12) by (apply (RK' 12); [cbn; tauto | apply bv_eq; reflexivity]).
assert (R2 : getr regs1 2 = getr regs 2) by (apply (RP' 2); [unfold acallee_saved; lia | apply bv_eq; reflexivity]).
assert (R3 : getr regs1 3 = getr regs 3) by (apply (RP' 3); [unfold acallee_saved; lia | apply bv_eq; reflexivity]).
assert (R4 : getr regs1 4 = getr regs 4) by (apply (RP' 4); [unfold acallee_saved; lia | apply bv_eq; reflexivity]).
assert (R8 : getr regs1 8 = getr regs 8) by (apply (RP' 8); [unfold acallee_saved; lia | apply bv_eq; reflexivity]).
assert (SP1 : spZ regs1 = spZ regs) by (unfold spZ; rewrite R2; reflexivity).
assert (S01 : s0Z regs1 = s0Z regs) by (unfold s0Z; rewrite R8; reflexivity).
(* every byte below the allocator ceiling is the entry's: the run wrote only [sp - 48, sp) *)
assert (LOW : forall a, 0 <= a < alloc_ceiling -> mbyte tfibsegs (mrestrict (w_H W) mem1) a = mbyte tfibsegs (mrestrict (w_H W) mem) a).
{ intros a Ha. apply AE2y.mbyte_of_aview. apply AV1; lia. }
(* the journal of the run: only the 48 bytes below sp changed *)
assert (J00 : ajournal (SK:=SK) tfibsegs B AFMEMOPEN_STK (spZ regs) [YI16.sink_token] ly S W mem md [] ly S W mem md 0)
  by (eapply ajournal_init; eassumption).
assert (J0 : ajournal (SK:=SK) tfibsegs B AFMEMOPEN_STK (spZ regs) [YI16.sink_token] ly S W mem md [] ly S W mem1 md1 0).
{ apply (ajournal_after_write tfibsegs B LAWS fm_segs_low AFMEMOPEN_STK (spZ regs) [YI16.sink_token] ly S W mem md []
    ly S W mem md 0 mem1 md1 (fun a => spZ regs - 48 <= a < spZ regs) S [] J00).
- intros a Ha Hna. exact (AV1 a Ha Hna).
- exact PM1.
- exact MF1.
- intros a Ha. left. left. rewrite FS. lia.
- exact HAR1.
- reflexivity. - reflexivity. - lia. - reflexivity. - exact HQT. }
(* the C library's precondition at REAL fmemopen *)
eapply SRr_mono.
{ apply (RFM AMR W ly S regs1 mem1 md1 ch b n C).
unfold rfmemopen_pre.
split.
{ split; [exact HAR1|]. split; [rewrite R1; exact Hra|]. split; [unfold raZ; rewrite R1; exact Hra4|].
split; [rewrite R3; exact Hgp|]. split; [rewrite R4; exact Htp|].
split; [unfold astk_ok; rewrite SP1, RS; repeat split; lia|].
split; [rewrite SP1, RS; intros a Ha; apply PM1; apply Hpres; lia|].
split; [|exact HQT].
rewrite SP1, S01. apply (achain_kept ly (aview tfibsegs (w_H W) mem) (aview tfibsegs (w_H W) mem1) (spZ regs) (s0Z regs) ch (spZ regs) Hch);
  [lia | lia | intros a Ha; apply AV1; lia]. }
split; [rewrite R10; exact G10|].
split; [rewrite R11; exact G11|].
split; [rewrite R12; exact G12|].
split; [apply (fm_none_frame (mrestrict (w_H W) mem)); [intros a Ha; apply LOW; pose proof (fm_segs_low a Ha); unfold kLowMemEnd in *; lia | exact HNONE]|].
split; [exact Hn|].
split; [lia|].
split; [exact HBLK|].
split; [apply (garr8_frame tfibsegs (mrestrict (w_H W) mem)); [exact HG | intros a Ha; apply LOW; lia]|].
split; [exact HBY|].
(* fm_window: the constant window [0x10350, 0x10370) is far below [sp - 48, sp), the only bytes the run wrote *)
split; [intros a Ha; rewrite AV1 by lia; exact (HMC a Ha)|].
split; [exact Hev|].
split; [exact Hlive|].
split; [exact HMO|].
split; [exact HCTX|].
split; [exact Hu0 | exact HuC]. }
cbv beta. intros W' c' _ HP. unfold apost_base in HP.
destruct HP as (ly' & S' & regs' & mem' & md' & -> & J1 & RPF & HQ).
unfold rfmemopen_post in HQ. destruct HQ as (res & Q10 & QMO & Q4096 & Q16 & QAB & QSRC & QFD & QFS).
rewrite SP1 in J1.
pose proof J1 as (_ & _ & _ & _ & _ & FR1 & _).
destruct (fds_fs_of_sbm md md1 MF1) as [FD1 FS1].
exists ly', S', regs', mem', md', res.
split; [rewrite R1; reflexivity|].
split.
{ exact (ajournal_sub_tok tfibsegs B LAWS fm_segs_low AFMEMOPEN_STK (spZ regs) [YI16.sink_token] ly S W mem md []
    ly S W mem1 md1 0 RFMEMOPEN_STK (spZ regs) [YI16.sink_token] [] ly' S' W' mem' md' 1 J0 J1
    ltac:(rewrite FS, RS; lia) ltac:(lia) (fun a Ha => or_introl Ha)). }
split; [exact (aregs_preserved_trans _ _ _ RP1 RPF)|].
split; [exact Q10|].
split; [exact FR1|].
split; [exact QMO|].
split; [rewrite QFD; exact FD1|].
split; [rewrite QFS; exact FS1|].
split; [exact Q4096|]. split; [exact Q16|]. split; [exact QAB | exact QSRC].
Qed.

End e.
End d.
End b.

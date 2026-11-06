(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: asan-ubsan twin of lib/A/AD3d.v by a Theorem Labs lane; renames A->AU per derive_y.py; numerals re-measured on fuzz_knock's asan-ubsan pin f834165f5002: none changed (md_takes and md_room hold no image address; 4096 is the model's page size). *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_knock/lib/AU/YD3d.v (donor image sha256 f834165f5002), with its module paths changed and its addresses moved to reac-repacer/fuzz_wire's ASan+UBSan build. *)
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09 YO0d.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YI04 YK0v YK13.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0b YG0d.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require Import YB1v YB1w.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require YK0g.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* What the model records as taken before the call: a nonempty extent that lies in the model's reserved or mapped
   areas (the lists an anonymous mmap grant must avoid, grant_ok YK0v.v:110-114 region_free), or one at or above
   page_floor alloc_top (amendment 10). No grant reaches page_floor alloc_top: a grant x is
   page aligned, its size is a page multiple and x + size <= alloc_top (LPS Mmap.v:1425-1427), so
   x + size <= page_floor alloc_top (grant_end_page_floor below). Before amendment 10 the bound was alloc_top, but
   alloc_top <= ly_stk_lo is not what the at-main facts give: al_top (YG0n.v:614, YM05.v:50) makes the ceiling page_floor
   alloc_top, and the stack lies at or above that ceiling (the premise of stack_takes, YG0s.v:241). *)
Definition md_takes (md : Model) (e : Z * Z) : Prop :=
  (0 < snd e /\ forall a, in_zr a e -> Exists (fun q => bv_unsigned (fst q) <= a < bv_unsigned (fst q) + bv_unsigned (snd q))
                                  (vm_reserved (m_vmmaps md) ++ vm_maps (m_vmmaps md)))
  \/ page_floor (alloc_top (m_vmmaps md)) <= fst e.

(* A grant [x, x + n) with x and n page aligned that ends at or below top ends at or below page_floor top. The
   freshness step of mnr_holds (grant_misses) and of YD3h's mod_holds (mod_takes_apart) uses it on md_takes'
   second arm. *)
Lemma grant_end_page_floor : forall x n top, x mod 4096 = 0 -> n mod 4096 = 0 -> x + n <= top ->
  x + n <= page_floor top.
Proof.
intros x n top Hx Hn Hle. apply page_floor_ge; [| exact Hle].
rewrite Z.add_mod by lia. rewrite Hx, Hn. reflexivity.
Qed.

Definition md_room (md : Model) (n : Z) : Prop :=
  exists g, g mod 4096 = 0 /\ 0 < g /\ g + n <= alloc_top (m_vmmaps md) /\
    region_free (vm_reserved (m_vmmaps md) ++ vm_maps (m_vmmaps md)) (Z_to_bv 64 g) (Z_to_bv 64 n) = true.

End g.
(* S4 twin: appended by a Theorem Labs lane *)
(* The S4 twin, by a Theorem Labs lane: the asan-ubsan (lib/B) twin of the S4 part of lib/A/AD3d.v (a Theorem Labs lane,
   proved): the contract and the walk of
   __sanitizer::MmapNoReserveOrDie (0x654d8-0x655dc in fuzz_wire.asan-ubsan; the donor's 0x647b0-0x648b4, 65 insns, fuzz_knock.asan-ubsan unstripped twin sha256
   6b6e06f3...87773). Names and statements are lib/A/AD3d.v's. The A-core modules are replaced by their AU twins:
   A/AB1v -> B/YB1v (tfibsegs = AsanUbsan.M.loaded_segments), AF0m -> YF0m, AF0x -> YF0x, AB1w -> YB1w,
   AB1h -> YB1h, AB1q -> YB1q, AFek -> YFek, AFel -> YFel, AFl3 -> YFl3, AF0r -> YF0r; lib/Reusable is shared.
   md_takes and md_room, which lib/A/AD3d.v states in its Section g, are the first Section g above, word for word.
   rule 24: proves function MmapNoReserveOrDie (AU twin of the proved lib/A contract; reuse search for the A proof:
   release 2026.10.0 (tag 8f5f46768858) names MmapNoReserveOrDie only in address tables).
   NUMERALS, measured on fuzz_wire.asan-ubsan (capstone and the ELF symbol table): every code address this part
   cites lies 0x260 below fuzz_wire.asan's (lib/A/AD3d.v), and on the walked path holds the same word as there (0x654d8 65 insns, GetNamedMappingFd 0x65c7c 131,
   internal_iserror 0x638b0, internal_mmap 0x638d0 with its ecall 0x638d4 and ret 0x638d8, IncreaseTotalMmap 0x5f7b4,
   GetPageSize 0x647fc, ReportMmapFailureAndDie 0x5f11c, the entry word 0xfd010113), except the immediates of the
   pc-relative GOT loads (0x654f4, 0x65cb0, 0x5f7b8). The data addresses move:
     MNR_PSC_GOT 0x987c8 -> 0x98858, MNR_PSC (PageSizeCached) 0x130220 -> 0x1302a0,
     MNR_CF_GOT 0x987d8 -> 0x98868, MNR_CF (common_flags_dont_use) 0x1322a8 -> 0x132328,
     so decorate_proc_maps (MNR_CF + 0x104) 0x1323ac -> 0x13242c and mmap_limit_mb (MNR_CF + 0x90) 0x132338 -> 0x1323b8.
   Unchanged: MNR_STK 104, the offsets 0x104 (lbu at 0x65cb4) and 0x90 (ld at 0x5f7bc), the frame (-56, 48), the
   flags 0x4022, the size bound MNR_SZ_MAX.

   THE CODE (addresses of the donor fuzz_knock ASan+UBSan image (pin sha256 f834165f5002), not fuzz_wire.asan-ubsan's; a0 = size, a1 = name, ra = return address)
     0x647b0 addi sp,sp,-0x30; sd ra,0x28(sp); sd s0,0x20(sp); sd s1,0x18(sp); sd s2,0x10(sp)
     0x647c4 s0 := name; s2 := [0x965f8] = 0x12e020 (PageSizeCached); a1 := [s2]
     0x647d8 bnez a1 -> 0x647e8                      cached page size 4096, so GetPageSize 0x63ad4 is not called
     0x647e8 a0 := a1 & (a1 - 1); bnez a0 -> 0x64888  IsPowerOfTwo(4096): not taken (RawWrite + Die arm)
     0x647f4 s1 := (size + a1 - 1) & -a1             page round-up; size is page-aligned, so s1 = size
     0x64804 a0 := 0x4022; sw a0,0xc(sp)             flags = MAP_PRIVATE|MAP_ANONYMOUS|MAP_NORESERVE
     0x64810 a2 := sp+0xc; a0 := s0; a1 := s1; jal GetNamedMappingFd 0x64f54 (ra 0x64820)
     0x64820 a3 := [sp+0xc]; a4 := a0 (= -1); a2 := 3; a0 := 0; a1 := s1; a5 := 0
     0x64838 jal internal_mmap 0x62ba8 (li a7,222; ecall; ret)     THE ECALL
     0x6483c s2 := a0; a1 := 0; jal internal_iserror 0x62b88       no error store (a1 = 0)
     0x64848 a0 := 0xaaaaaaaa; sw a0,8(sp); a1 := sp+8; a0 := s2; jal internal_iserror 0x62b88
     0x64860 bnez a0 -> 0x64898                      the granted address is not an errno: not taken
     0x64864 a0 := s1; jal IncreaseTotalMmap 0x5ea8c  mmap_limit_mb = 0, so it returns at once (beqz 0x5ea98)
     0x6486c a0 := s2; restore ra/s0/s1/s2; addi sp,sp,0x30; ret
   GetNamedMappingFd 0x64f54 on this path: frame -0x110, 7 callee saves at sp+0xd8..0x108, a0 := -1, then either
   [name = 0] beqz s2 -> 0x650a4 or [name <> 0] the decorate_proc_maps byte at 0x1301ac has low bit 0, so
   beqz a2 -> 0x650a4; both restore and return -1, and neither touches the flags word. The /dev/shm arm that
   clears MAP_ANONYMOUS at 0x65094-0x6509c is unreachable from mnr_cells.
   TOUCHED STACK: MmapNoReserveOrDie writes [sp-40, sp) (its 4 saves and the two 4-byte slots at sp+8 and sp+0xc
   of its own frame) and GetNamedMappingFd writes [sp-104, sp-48) (7 saves at (sp-320)+0xd8 .. +0x108). So every
   byte written or read below the entry sp lies in [sp - 104, sp): MNR_STK = 104. The rest of the 320-byte sp
   drop is never read or written. *)
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require Import YF0m YF0x.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require YK0x.

(* The stack band this file proves: the touched bytes below the entry sp, not the sp drop (320). *)
Definition MNR_STK : Z := 104.

Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* ===== Verbatim from the consumer's draft of lib/A/AD3c.v: the
   definitions mnr_contract shares with tfib_blockinfo_create_spec. Kept word for word so that AD3c's
   [Hypothesis mnr_contract : tfib_mnr_spec] is closed by [exact mnr_holds] up to delta. In this twin md_takes and
   md_room, which lib/A/AD3d.v states here, are the first Section g above, word for word. ===== *)

(* The refused arm, in the form amreal gives a refusable kernel ask (lib/Reusable/YG0d.v:76-88): the run
   reaches an event-free node; the children marked [sp] (the mmap refusal, ReportMmapFailureAndDie 0x5f11c) end in
   the halt form [AIw -> srealizes c t_nil] and carry no post; at least one child [i0] is unmarked, and every unmarked
   child goes on to Q. *)
Definition SRr_refusable (W : world tfibsegs) (c : config) (Q : world tfibsegs -> config -> Prop) : Prop :=
  SRr tfibsegs W c (fun W1 c1 =>
    exists (I : Type) (nx : I -> config) (sp : I -> bool) (i0 : I),
      node_ok tfibsegs c1 I (fun _ => []) nx /\
      (forall i, AI tfibsegs (w_H W1) (w_A W1) (cfg_model c1) -> AI tfibsegs (w_H W1) (w_A W1) (cfg_model (nx i))) /\
      sp i0 = false /\
      (forall i, sp i = true -> AI tfibsegs (w_H W1) (w_A W1) (cfg_model (nx i)) -> srealizes tfibsegs (nx i) t_nil) /\
      (forall i, sp i = false -> SRr tfibsegs W1 (nx i) Q)).

(* A caller SRr_binds through the node: the refused children are absorbed by SRr_node_tnil (YG0d.v:42). *)
Lemma SRr_refusable_SRr : forall W c Q, SRr_refusable W c Q -> SRr tfibsegs W c Q.
Proof.
  intros W c Q H. eapply SRr_bind; [exact H|].
  intros W1 c1 _ (I & nx & sp & i0 & Hn & Ht & Hs & Hz & Hk).
  exact (SRr_node_tnil tfibsegs W1 c1 I nx sp i0 Q Hn Ht Hs Hz Hk).
Qed.

(* The cells MmapNoReserveOrDie and its callees read (0x654f0 GetPageSizeCached through the GOT slot 0x98858;
   GetNamedMappingFd 0x65cac and IncreaseTotalMmap 0x5f7b4 read common_flags through the GOT slot 0x98868): the cached
   page size is 4096, decorate_proc_maps (common_flags + 0x104) has its low bit clear, mmap_limit_mb
   (common_flags + 0x90) is 0. With them it writes no global, only its frame. *)
Definition MNR_PSC_GOT : Z := 0x98858.
Definition MNR_PSC : Z := 0x1302a0.
Definition MNR_CF_GOT : Z := 0x98868.
Definition MNR_CF : Z := 0x132328.
Definition mnr_cells (m : word -> option byte) : Prop :=
  val_mem tfibsegs m MNR_PSC_GOT 8 MNR_PSC /\ val_mem tfibsegs m MNR_PSC 8 4096 /\
  val_mem tfibsegs m MNR_CF_GOT 8 MNR_CF /\
  (exists f, val_mem tfibsegs m (MNR_CF + 0x104) 1 f /\ Z.land f 1 = 0) /\
  val_mem tfibsegs m (MNR_CF + 0x90) 8 0.

(* ===== End of the shared text. ===== *)

(* The extents the grant must miss, beyond what md_room already asks: the two image cells
   IncreaseTotalMmap reads AFTER the ecall (0x5f7b4-0x5f7bc: the common_flags GOT slot, then mmap_limit_mb at
   common_flags + 0x90). A grant landing on either one would be zero-filled by the ecall and the run would then
   load a null common_flags pointer. The caller's own stack band is the third such extent: the function restores
   ra, s0, s1 and s2 from it after the ecall. md_takes + the grant's region_free give the disjointness. *)
Definition mnr_cell_extents : list (Z * Z) := [(MNR_CF_GOT, 8); (MNR_CF + 0x90, 8)].

Section kd.
(* The stack band: the caller instantiates it with MNR_STK = 104 (see the header's TOUCHED STACK note). *)
Variable mnr_stk : Z.

(* S4, MmapNoReserveOrDie (0x654d8): a0 = size, a1 = name pointer, return to ra.
   PRE: the size is a positive page multiple; the cells the chain reads (mnr_cells); room for the grant
   (md_room, which makes every mmap refusal SPURIOUS at the ecall, so the node has no refused child, as
   mnr_ecall_step (line 366) proves); the VM budget allow_expose asks for
   (YG0b.v:423, charged ONCE: a 0x4022 grant is entirely lazy and adds nothing eager); and a 16-aligned sp whose
   touched band [sp - mnr_stk, sp) is present and lies in high memory, above the image, and which (with the two
   cells read after the ecall) the model already takes, so the grant cannot land on it.
   POST, normal exit only, with x the granted address:
     P1 a0 = x, callee-saved registers and sp restored;
     P2 x is page aligned, 4096 <= x, and grant_ok_na_pin md x size = true -- the exact input of
        lib/B/YFia.v:70-77 grant_facts, from which a caller holding ARm / ALedger derives [in_app x size]. [in_app]
        itself is NOT in this post: on this base it is not a model fact (grant_facts derives it from ARm and ALedger, YFia.v:60-61, 70-72);
     P3 [x, x+size) is fresh against every reserved or mapped area of md, and ends below alloc_top;
     P4 every byte of [x, x+size) is present in the reader and reads 0 (zfill at the ecall, exposed by
        allow_expose YG0b.v:421-427);
     world: w_A grows by exactly the new block and w_H changes ONLY inside [x, x+size) (wallow, YG0b.v:419-420);
     P5 memory is unchanged outside [x, x+size) and the touched band -- no shadow byte is written, no global is
        written -- presence only grows, the I/O state is untouched, and the model now takes [x, x+size) and still
        takes everything it took. *)
Definition mnr_contract : Prop :=
  forall (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (size : Z),
  let H := w_H W in let m := mrestrict H mem in let sp := spZ regs in
  argZ regs 0 = size -> 0 < size -> YG0f.page_aligned size -> YK0s.ret_ok (getr regs 1) ->
  mnr_cells m -> md_room md size ->
  (* the model's own map list is well formed: every (base, size) ends below 2^64. The post's budget bookkeeping
     (MInv for the granted model) is read off eager_used, and eager_used only has its byte-counting form
     (eager_used_sem_brk, YA08.v:127-129; live_msa, YK0g.v:292-295) under this. It is the weakest part of
     amwf / MWF (YG0b.v:129, amwf_MWF YG0b.v:148) and is implied by either. *)
  YK0g.ivs_wf (vm_maps (m_vmmaps md)) ->
  eager_used md + A_bytes (w_A W) + size <= vm_limit (m_vmmaps md) ->
  sp mod 16 = 0 -> kHighMemBeg <= sp - mnr_stk -> sp <= kHighMemEnd ->
  (forall a, sp - mnr_stk <= a < sp -> apresent H mem a) ->
  Forall (md_takes md) ((sp - mnr_stk, mnr_stk) :: mnr_cell_extents) ->
  SRr_refusable W (mkCfg (mkst regs (Z_to_bv 64 tfib_A_MmapNoReserveOrDie) mem (seg_rom tfibsegs)) md)
    (fun W' c' => exists x regs' mem' md',
      c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom tfibsegs)) md' /\
      (* P1 *) getr regs' 10 = Z_to_bv 64 x /\ regs_preserved regs regs' /\
      (* P2 *) YG0f.page_aligned x /\ 4096 <= x /\ grant_ok_na_pin md (Z_to_bv 64 x) size = true /\
      (* P3 *) Forall (fun q => zdisjoint (x, size) (bv_unsigned (fst q), bv_unsigned (snd q)))
                 (vm_reserved (m_vmmaps md) ++ vm_maps (m_vmmaps md)) /\
               x + size <= alloc_top (m_vmmaps md) /\
      (* P4 *) (forall i, 0 <= i < size ->
                 apresent (w_H W') mem' (x + i) /\ aview tfibsegs (w_H W') mem' (x + i) = Some 0) /\
      (* world *) w_A W' = (x, x + size) :: w_A W /\
                  (forall a : word, ~ (x <= bv_unsigned a < x + size) -> w_H W' a = w_H W a) /\
      (* P5 *) (forall a : word, ~ (sp - mnr_stk <= bv_unsigned a < sp) ->
                 ~ (x <= bv_unsigned a < x + size) -> mem' a = mem a) /\
               (forall a, apresent H mem a -> apresent (w_H W') mem' a) /\ same_io md md' /\
               md_takes md' (x, size) /\ (forall e, md_takes md e -> md_takes md' e) /\
      (* the new model, exactly (amendment 8 note 6): the ecall's own model
         function for 0x4022 -- with_mmap_backing flags x n (mmap_model x n md) = vm_add_lazy x n (...)
         (YA09.v:410-412 with mmap_noreserve_b 0x4022 = true, YA09.v:397) -- under the instruction steps'
         materialisation wrapper, which no walk can avoid. The three projections B2 reads off it follow. *)
               (exists mat, md' = with_vm_backing
                   (m_vm_lazy (YK0x.mmap_model_noreserve (Z_to_bv 64 x) (Z_to_bv 64 size) md)) mat
                   (YK0x.mmap_model_noreserve (Z_to_bv 64 x) (Z_to_bv 64 size) md)) /\
               m_vmmaps md' = m_vmmaps (mmap_model (Z_to_bv 64 x) (Z_to_bv 64 size) md) /\
               m_vm_lazy md' = (Z_to_bv 64 x, Z_to_bv 64 size) :: m_vm_lazy md /\
               eager_used md' = eager_used md).

End kd.
End g.

(* ===================== The proof of mnr_holds =====================
   The walk framework of lib/A/AD3b.v / YFem: the symbolic runner over a fetch table that covers MmapNoReserveOrDie
   (0x654d8, 65 insns) on top of YB1q's tfibtbl_rtC (which already covers GetNamedMappingFd 0x65c7c,
   internal_iserror 0x638b0 -- and with it internal_mmap 0x638d0 -- and IncreaseTotalMmap 0x5f7b4). The statement
   above is closed before these imports, so they cannot change how its names resolve. *)
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YP0m YP0e YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j YP0n.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YK0h YK14 YK1b YK1a YA0o YA0q.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require Import YB1h YB1q YFek YFel YFl3 YD3dEnv.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require YA05 YK0x YA09 YF05.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
Open Scope Z_scope.

Definition tfibtbl_mnr_build : ctable := build_table tfibsegs 0x654d8 65%nat tfibtbl_rtC.
Definition tfibtbl_mnr : ctable := Eval vm_compute in tfibtbl_mnr_build.
Lemma tfibtbl_mnr_eq : tfibtbl_mnr = tfibtbl_mnr_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_mnr). Qed.
Lemma tfibtbl_mnr_ok : table_ok tfibsegs tfibtbl_mnr.
Proof. rewrite tfibtbl_mnr_eq. unfold tfibtbl_mnr_build. apply build_table_ok; [cbv; discriminate | exact tfibtbl_rtC_ok]. Qed.

Definition aFB : nat := 32.
Definition MNR_SZ_MAX : Z := 2 ^ 64 - 8388608.
Definition mlit1 (a : Z) (n : nat) : YP09.region := YP09.mkRegion None a (a + 1) 0 0 [YP09.mkChunk a (CVal 1 (SOff n 0))].
Definition R_FR : YP09.region := YP09.mkRegion (Some 2%nat) (-56) 48 (-56) 48 [].
Definition R_PG : YP09.region := lit8 MNR_PSC_GOT MNR_PSC.
Definition R_PS : YP09.region := lit8 MNR_PSC 4096.
Definition R_CG : YP09.region := lit8 MNR_CF_GOT MNR_CF.
Definition R_FB : YP09.region := mlit1 (MNR_CF + 0x104) aFB.
Definition R_ML : YP09.region := lit8 (MNR_CF + 0x90) 0.
Definition MF_fix : list (nat * afact) :=
  [(2%nat, mkAF kHighMemBeg kHighMemEnd 4); (10%nat, mkAF 4096 MNR_SZ_MAX 12); (aFB, mkAF 0 255 0)].
Definition MMEM : smem := [R_FR; R_PG; R_PS; R_CG; R_FB; R_ML].
Definition SM0 : sstate := mkSS 0x654dc sr_atoms MMEM None (mkFacts MF_fix [] []).

Definition SM1 : sstate := Eval vm_compute in fst (sym_runN_sh tfibsegs tfibtbl_mnr FUEL SM0).
Definition c_n0 : acond := mkAC Instr.BC_EQ (SOff 11 0) (SLit 0).
Definition c_nn : acond := mkAC Instr.BC_NE (SOff 11 0) (SLit 0).
Definition SM2 : sstate := Eval vm_compute in fst (sym_runN_sh tfibsegs tfibtbl_mnr FUEL (add_cond SM1 c_n0)).
Definition SM1n : sstate := Eval vm_compute in fst (sym_runN_sh tfibsegs tfibtbl_mnr FUEL (add_cond SM1 c_nn)).
Definition pin12 (ss : sstate) : sstate :=
  mkSS (ss_pc ss) (sr_set (ss_regs ss) 12%bv (SLit 0)) (ss_mem ss) (ss_resv ss) (ss_facts ss).
Definition SM3 : sstate := Eval vm_compute in fst (sym_runN_sh tfibsegs tfibtbl_mnr FUEL (pin12 SM1n)).

(* ---- the model side of the grant: a MAP_NORESERVE anonymous grant is entirely lazy, so it adds nothing to
   eager_used, and AI survives it at a world that has just allowed [a, a+n). ---- *)
Section mdl. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Lemma sum_count_ext_in : forall (P Q : Z -> bool) l,
  (forall q x, In q l -> YK0g.B q <= x < YK0g.B q + YK0g.S q -> P x = Q x) ->
  YK0g.sum_count P l = YK0g.sum_count Q l.
Proof.
intros P Q l. induction l as [|q l IH]; intros HE; [reflexivity|].
cbn [YK0g.sum_count]. rewrite (IH (fun q' x Hq' Hx => HE q' x (or_intror Hq') Hx)).
unfold YK0g.iv_count. rewrite (YK0g.zcount_ext P Q (YK0g.B q) (Z.to_nat (YK0g.S q))); [reflexivity|].
intros x Hx. pose proof (YK0g.S_range q) as HS. rewrite Z2Nat.id in Hx by lia.
exact (HE q x (or_introl eq_refl) Hx).
Qed.

Lemma gnap_parts : forall md (a : word) n, grant_ok_na_pin md a n = true ->
  bv_unsigned a mod page_size = 0 /\ 0 < bv_unsigned a /\ bv_unsigned a + n <= alloc_top (m_vmmaps md) /\
  region_free (vm_reserved (m_vmmaps md) ++ vm_maps (m_vmmaps md)) a (Z_to_bv 64 n) = true.
Proof.
intros md a n H. unfold grant_ok_na_pin in H.
apply andb_prop in H as [H Hrf]. apply andb_prop in H as [H Htop]. apply andb_prop in H as [Hal Hpos].
apply Z.eqb_eq in Hal. apply Z.ltb_lt in Hpos. apply Z.leb_le in Htop. auto.
Qed.

Lemma Hcut_out : forall (Hh : word -> bool) lo hi (y : word),
  ~ (lo <= bv_unsigned y < hi) -> Hcut Hh lo hi y = Hh y.
Proof.
intros Hh lo hi y Hy. unfold Hcut.
destruct (Z.leb_spec lo (bv_unsigned y)); destruct (Z.ltb_spec (bv_unsigned y) hi); cbn [andb negb];
rewrite ?andb_true_r, ?andb_false_r; try reflexivity; exfalso; apply Hy; lia.
Qed.

Lemma eager_used_nr : forall (a n : word) md,
  YK0g.ivs_wf (vm_maps (m_vmmaps md)) ->
  bv_unsigned a mod page_size = 0 -> bv_unsigned n mod page_size = 0 ->
  0 < bv_unsigned n -> bv_unsigned a + bv_unsigned n <= 2 ^ 64 ->
  region_free (vm_reserved (m_vmmaps md) ++ vm_maps (m_vmmaps md)) a n = true ->
  eager_used (YK0x.mmap_model_noreserve a n md) = eager_used md.
Proof.
intros a n md WF Hal Hnal Hpos Hhi Hrf.
assert (Hv : vm_maps (m_vmmaps (YK0x.mmap_model_noreserve a n md)) = (a, n) :: vm_maps (m_vmmaps md)) by reflexivity.
assert (Hna : vm_noaccess (m_vmmaps (YK0x.mmap_model_noreserve a n md)) = vm_noaccess (m_vmmaps md)) by reflexivity.
assert (Hl : m_vm_lazy (YK0x.mmap_model_noreserve a n md) = (a, n) :: m_vm_lazy md).
{ rewrite YK0x.mmap_model_noreserve_lazy. rewrite (YK0g.lazy_interior_aligned a n Hal Hnal Hpos Hhi). reflexivity. }
assert (WF' : YK0g.ivs_wf (vm_maps (m_vmmaps (YK0x.mmap_model_noreserve a n md)))).
{ rewrite Hv. apply YK0g.ivs_wf_cons; [unfold YK0g.iv_wf, YK0g.B, YK0g.S; cbn [fst snd]; exact Hhi | exact WF]. }
rewrite (YA08.eager_used_sem_brk _ WF'), (YA08.eager_used_sem_brk _ WF).
rewrite Hv, Hna, Hl. cbn [YK0g.sum_count].
assert (Z0 : YK0g.iv_count (fun x => negb (YK0g.covered (vm_noaccess (m_vmmaps md) ++ (a, n) :: m_vm_lazy md) x)) (a, n) = 0).
{ unfold YK0g.iv_count. apply YK0g.zcount_false. intros x Hx.
  pose proof (YK0g.S_range (a, n)) as HS. unfold YK0g.B, YK0g.S in Hx, HS. cbn [fst snd] in Hx, HS.
  rewrite Z2Nat.id in Hx by lia.
  apply negb_false_iff. rewrite YK0g.covered_app. apply orb_true_iff. right.
  unfold YK0g.covered. cbn [existsb]. apply orb_true_iff. left.
  unfold YK0g.in_iv, YK0g.in_rng, YK0g.B, YK0g.S. cbn [fst snd].
  apply andb_true_iff. split.
  - apply Z.leb_le. lia.
  - apply Z.ltb_lt. lia. }
rewrite Z0, Z.add_0_l.
apply sum_count_ext_in. intros [b s] x Hq Hx. unfold YK0g.B, YK0g.S in Hx. cbn [fst snd] in Hx.
pose proof (YK13.region_free_In _ a n b s Hrf (in_or_app _ _ _ (or_intror Hq))) as D.
assert (HF : YK0g.in_iv (a, n) x = false).
{ unfold YK0g.in_iv, YK0g.in_rng, YK0g.B, YK0g.S. cbn [fst snd].
  apply andb_false_iff. destruct D as [D|D].
  - right. apply Z.ltb_ge. lia.
  - left. apply Z.leb_gt. lia. }
f_equal. rewrite !YK0g.covered_app. f_equal. unfold YK0g.covered. cbn [existsb]. rewrite HF. reflexivity.
Qed.

Lemma AI_nr_grant : forall (W3 : world tfibsegs) (a n : word) md,
  AI tfibsegs (w_H W3) (w_A W3) md ->
  YK0g.ivs_wf (vm_maps (m_vmmaps md)) ->
  bv_unsigned a mod page_size = 0 -> bv_unsigned n mod page_size = 0 ->
  0 < bv_unsigned n -> bv_unsigned a + bv_unsigned n <= 2 ^ 64 ->
  region_free (vm_reserved (m_vmmaps md) ++ vm_maps (m_vmmaps md)) a n = true ->
  In (bv_unsigned a, bv_unsigned a + bv_unsigned n) (w_A W3) ->
  eager_used md + A_bytes (w_A W3) <= vm_limit (m_vmmaps md) ->
  AI tfibsegs (w_H W3) (w_A W3) (YK0x.mmap_model_noreserve a n md).
Proof.
intros W3 a n md (HH & HA & HL & HM & HHt) WF Hal Hnal Hpos Hhi Hrf HIn Hbud.
assert (Hl : m_vm_lazy (YK0x.mmap_model_noreserve a n md) = (a, n) :: m_vm_lazy md).
{ rewrite YK0x.mmap_model_noreserve_lazy. rewrite (YK0g.lazy_interior_aligned a n Hal Hnal Hpos Hhi). reflexivity. }
assert (Hvl : vm_limit (m_vmmaps (YK0x.mmap_model_noreserve a n md)) = vm_limit (m_vmmaps md)) by reflexivity.
assert (Hmat : m_vm_materialized (YK0x.mmap_model_noreserve a n md) = m_vm_materialized md) by reflexivity.
assert (HE : eager_used (YK0x.mmap_model_noreserve a n md) = eager_used md)
  by (apply eager_used_nr; assumption).
split; [exact HH|]. split; [exact HA|]. split.
- intros w Hw Hwh. rewrite Hl, YA09.page_in_ranges_cons in Hw. apply orb_true_iff in Hw as [Hw|Hw].
  + apply andb_prop in Hw as [L1 L2]. cbn [fst snd] in L1, L2. apply Z.leb_le in L1. apply Z.leb_le in L2.
    unfold page_allowedb. apply existsb_exists. exists (bv_unsigned a, bv_unsigned a + bv_unsigned n).
    split; [exact HIn|]. cbn [fst snd]. apply andb_true_iff. split; apply Z.leb_le; lia.
  + exact (HL w Hw Hwh).
- split; [| rewrite YK0x.mmap_model_noreserve_halted; exact HHt].
  destruct HM as [N1 N2 N3 N4 N5]. constructor.
  + rewrite Hmat. exact N1.
  + rewrite Hmat. exact N2.
  + rewrite Hmat. exact N3.
  + rewrite Hmat, Hl. intros p Hp. rewrite YA09.page_in_ranges_cons. apply orb_true_iff. right. exact (N4 p Hp).
  + rewrite HE, Hvl. exact Hbud.
Qed.
End mdl.

(* ---- the ecall of internal_mmap (0x638d4), as an SRr step: the node has no refused child (md_room makes every
   refusal spurious), and each granted child is handed over at the world that has just allowed [x, x+len). ---- *)
Section ecl. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma mnr_ecall_step : forall (W : world tfibsegs) regs (pc : word) mem md (len : Z) Q,
  getr regs 17 = Z_to_bv 64 222 -> getr regs 10 = Z_to_bv 64 0 ->
  getr regs 11 = Z_to_bv 64 len -> 0 < len -> len < 2 ^ 64 -> len mod page_size = 0 ->
  getr regs 12 = Z_to_bv 64 3 -> getr regs 13 = Z_to_bv 64 16418 ->
  getr regs 14 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 0 ->
  YK0g.ivs_wf (vm_maps (m_vmmaps md)) ->
  (exists g, grant_ok_na_pin md g len = true) ->
  eager_used md + A_bytes (w_A W) + len <= vm_limit (m_vmmaps md) ->
  (forall (a : word) (W3 : world tfibsegs),
     grant_ok_na_pin md a len = true ->
     wle W W3 -> w_A W3 = (bv_unsigned a, bv_unsigned a + len) :: w_A W ->
     (forall y : word, bv_unsigned a <= bv_unsigned y < bv_unsigned a + len -> w_H W3 y = false) ->
     (forall y : word, w_H W y = false -> w_H W3 y = false) ->
     (forall y : word, ~ (bv_unsigned a <= bv_unsigned y < bv_unsigned a + len) -> w_H W3 y = w_H W y) ->
     AI tfibsegs (w_H W3) (w_A W3) (YK0x.mmap_model_noreserve a (Z_to_bv 64 len) md) ->
     SRr tfibsegs W3 (mkCfg (mkst (regupd regs 10 a) (v_addi pc 4) (zfill a (Z_to_bv 64 len) mem) (seg_rom tfibsegs))
                            (YK0x.mmap_model_noreserve a (Z_to_bv 64 len) md)) Q) ->
  SRr tfibsegs W (mkCfg (pend_at regs pc mem (seg_rom tfibsegs)) md) Q.
Proof.
intros W regs pc mem md len Q H17 H10 H11 Hpos Hhi Hmod H12 H13 H14 H15 WF (g0 & Hg0) Hbud HK.
intros HI T HKT.
assert (Hpru : page_round_up_Z len = len).
{ unfold page_round_up_Z. unfold page_size in Hmod. apply Z.mod_divide in Hmod as [q Hq]; [|lia].
  unfold page_size. rewrite Hq. replace (q * 4096 + 4096 - 1) with (4095 + q * 4096) by lia.
  rewrite Z.div_add by lia. change (4095 / 4096) with 0. lia. }
assert (Hnrb : mmap_noreserve_backed_ok (Z_to_bv 64 16418) md len = true).
{ unfold mmap_noreserve_backed_ok. rewrite YK0x.mmap_noreserve_b_flags. reflexivity. }
assert (Hn_un : bv_unsigned (Z_to_bv 64 len) = len) by (apply YK00.u64_lit; lia).
destruct (YF05.anon_node tfibsegs regs pc mem (seg_rom tfibsegs) md (Z_to_bv 64 16418) len
  (AI_halted _ _ _ _ HI) H17 H10 H11 ltac:(lia) H12 H13 YA09.mmap_flags_core_4022 H14 H15
  ltac:(rewrite Hpru; exists g0; exact Hg0) ltac:(rewrite Hpru; exact Hnrb))
  as (I & nx & bit & ga & i0 & NODE & Bi0 & OUT).
rewrite Hpru in OUT.
apply (YA09.srz_silent_all tfibsegs _ I nx T i0 NODE).
intros i. destruct (OUT i) as (md_i & Hh_i & Hio_i & Hbit & Hg_i & HNX & HMD).
set (a := ga i) in *.
destruct (gnap_parts md a len Hg_i) as (Hala & Hposa & Htop & Hrfa).
assert (Hlen_a : bv_unsigned a + len <= 2 ^ 64).
{ pose proof (alloc_top_room (m_vmmaps md)) as HR. unfold stack_max_size, two_pow_64 in HR. lia. }
assert (HAL : bv_unsigned a <= bv_unsigned a + len) by lia.
assert (Hhi_mod : (bv_unsigned a + len) mod page_size = 0).
{ unfold page_size in *. apply Z.mod_divide in Hala as [q Hq]; [|lia].
  apply Z.mod_divide in Hmod as [r Hr]; [|lia]. rewrite Hq, Hr.
  apply Z.mod_divide; [lia|]. exists (q + r). lia. }
destruct (allow_expose tfibsegs W md (bv_unsigned a) (bv_unsigned a + len) HAL Hala Hhi_mod HI ltac:(lia))
  as (LE & HA3 & HAB & HV1 & HV2 & HAI3).
set (W3 := wallow tfibsegs W (bv_unsigned a) (bv_unsigned a + len) HAL Hala Hhi_mod) in *.
assert (HAIg : AI tfibsegs (w_H W3) (w_A W3) (YK0x.mmap_model_noreserve a (Z_to_bv 64 len) md)).
{ apply (AI_nr_grant W3 a (Z_to_bv 64 len) md HAI3 WF Hala).
  - rewrite Hn_un. unfold page_size in *. exact Hmod.
  - rewrite Hn_un. exact Hpos.
  - rewrite Hn_un. exact Hlen_a.
  - exact Hrfa.
  - rewrite Hn_un, HA3. left. reflexivity.
  - rewrite HAB. lia. }
assert (HMDeq : md_i = YK0x.mmap_model_noreserve a (Z_to_bv 64 len) md).
{ rewrite HMD. unfold YK0x.mmap_model_noreserve.
  exact (YA09.with_mmap_backing_lazy (Z_to_bv 64 16418) a (Z_to_bv 64 len) _ YK0x.mmap_noreserve_b_flags). }
rewrite HNX, HMDeq.
pose proof (HK a W3 Hg_i LE HA3 HV1 HV2
  ltac:(intros y Hy; unfold W3, wallow; cbn [w_H]; apply Hcut_out; exact Hy) HAIg) as HS.
exact (HS HAIg T (fun W' c' le ai q => HKT W' c' (wle_trans _ _ _ _ LE le) ai q)).
Qed.
End ecl.

Definition aGR : nat := 33.
Definition R_FR2 : YP09.region := Eval vm_compute in nth 0 (ss_mem SM2) R_FR.
Definition TREGS : list sv := Eval vm_compute in sr_set (ss_regs SM2) 10%bv (SOff aGR 0).
Definition TF : list (nat * afact) :=
  [(2%nat, mkAF kHighMemBeg kHighMemEnd 4); (10%nat, mkAF 4096 MNR_SZ_MAX 12);
   (aGR, mkAF 4096 MNR_SZ_MAX 12)].
Definition SMT : sstate := mkSS 0x638d8 TREGS [R_FR2; R_CG; R_ML] None (mkFacts TF [] []).
Definition SMF : sstate := Eval vm_compute in fst (sym_runN_sh tfibsegs tfibtbl_mnr FUEL SMT).

Ltac red_sr :=
  lazymatch goal with
  | |- sv_denot _ (sr_get ?rs ?r) = _ =>
      let e := eval vm_compute in (sr_get rs r) in change (sr_get rs r) with e
  | |- _ = U _ (sr_get ?rs ?r) =>
      let e := eval vm_compute in (sr_get rs r) in change (sr_get rs r) with e
  end.

Section mdl2. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* the materialisation wrapper commutes with the NORESERVE grant *)
Lemma nr_wvb : forall (m : Model) X (a n : word),
  YK0x.mmap_model_noreserve a n (with_vm_backing (m_vm_lazy m) X m)
  = with_vm_backing (m_vm_lazy (YK0x.mmap_model_noreserve a n m)) X (YK0x.mmap_model_noreserve a n m).
Proof. intros [fd [maps lazy mt] io fs proc lim tm] X a n. reflexivity. Qed.
Lemma nr_io : forall (m : Model) (a n : word), same_io m (YK0x.mmap_model_noreserve a n m).
Proof.
intros m a n. unfold YK0x.mmap_model_noreserve.
eapply same_io_trans; [apply same_io_with_vmmaps | apply same_io_with_vm_backing].
Qed.
End mdl2.
Lemma TREGS_eq : TREGS = sr_set (ss_regs SM2) 10%bv (SOff aGR 0).
Proof. vm_cast_no_check (@eq_refl (list sv) TREGS). Qed.
Lemma R_FR2_base : YP09.r_base R_FR2 = Some 2%nat. Proof. vm_compute. reflexivity. Qed.
Lemma R_FR2_lo : YP09.r_lo R_FR2 = -56. Proof. vm_compute. reflexivity. Qed.
Lemma R_FR2_hi : YP09.r_hi R_FR2 = 48. Proof. vm_compute. reflexivity. Qed.
Lemma R_FR2_wlo : YP09.r_wlo R_FR2 = -56. Proof. vm_compute. reflexivity. Qed.
Lemma R_FR2_whi : YP09.r_whi R_FR2 = 48. Proof. vm_compute. reflexivity. Qed.
Section mdl3. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma mb_eq : forall (m m' : word -> option byte) y,
  m' (Z_to_bv 64 y) = m (Z_to_bv 64 y) -> mbyte tfibsegs m' y = mbyte tfibsegs m y.
Proof. intros m m' y He. unfold mbyte. rewrite He. reflexivity. Qed.
Lemma wr_eq : forall (m m' : word -> option byte) y,
  m' (Z_to_bv 64 y) = m (Z_to_bv 64 y) -> writable_at tfibsegs m y -> writable_at tfibsegs m' y.
Proof. intros m m' y He Hw. unfold writable_at, wview in *. rewrite He. exact Hw. Qed.
Lemma denot_off0 : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof. intros E n. cbn [sv_denot]. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.
Lemma apresent_hmono2 : forall (Ha Hb : word -> bool) m y,
  (forall z, Ha z = false -> Hb z = false) -> apresent Ha m y -> apresent Hb m y.
Proof. intros Ha Hb m y HM [Hh Hx]. split; [apply HM; exact Hh | exact Hx]. Qed.
Lemma apresent_zfill : forall (H : word -> bool) (m : word -> option byte) (b n : word) y,
  apresent H m y -> apresent H (zfill b n m) y.
Proof.
intros H m b n y [Hh [c Hc]]. split; [exact Hh|].
destruct (Z_le_dec (bv_unsigned b) (bv_unsigned (Z_to_bv 64 y))) as [L1|L1];
  [destruct (Z_lt_dec (bv_unsigned (Z_to_bv 64 y)) (bv_unsigned b + bv_unsigned n)) as [L2|L2]|].
- exists (Z_to_bv 8 0). apply YA09.zfill_in. lia.
- exists c. rewrite (YK0v.zfill_out b n m (Z_to_bv 64 y) ltac:(lia)). exact Hc.
- exists c. rewrite (YK0v.zfill_out b n m (Z_to_bv 64 y) ltac:(lia)). exact Hc.
Qed.
End mdl3.
(* ---- the walk ---- *)
Section walk. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma AFo2 : forall E k X lo hi al, ew E k = Z_to_bv 64 X -> 0 <= X < 2 ^ 64 -> lo <= X <= hi ->
  X mod 2 ^ al = 0 -> 0 <= al <= 64 -> afact_ok E k (mkAF lo hi al).
Proof.
intros E k X lo hi al HE HX HBd HM HA. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite HE, unsigned_lit_small by exact HX. repeat split; lia.
Qed.
Lemma atoms_ok_of_Forall2 : forall E l,
  Forall (fun nf : nat * afact => afact_ok E (fst nf) (snd nf)) l -> atoms_ok E l.
Proof. intros E l H. induction H as [| [k f] l Hh Ht IH]; cbn; [exact I | split; [exact Hh | exact IH]]. Qed.
Lemma sp_less48 : forall x : word,
  alu64 ALU_ADD x (sext 64 (4048%bv : bv 12)) = Z_to_bv 64 (bv_unsigned x - 48).
Proof.
intros x. rewrite alu_add. unfold v_add. apply Z_to_bv64_eq_mod.
assert (S48 : bv_unsigned (sext 64 (4048%bv : bv 12)) = 2 ^ 64 - 48) by (vm_compute; reflexivity).
rewrite S48. replace (bv_unsigned x + (2 ^ 64 - 48)) with (bv_unsigned x - 48 + 1 * 2 ^ 64) by lia.
apply Z.mod_add. lia.
Qed.
(* The node SRr_refusable asks for: MmapNoReserveOrDie's first instruction, addi sp,sp,-0x30 (no memory
   access), as an event-free node with one child; the walk after it is a plain SRr, because md_room excludes
   the refusal at the only kernel ask on the path. *)
Lemma mnr_entry_node : forall (W : world tfibsegs) regs mem md Q,
  SRr tfibsegs W (mkCfg (mkst (regupd regs 2%bv (Z_to_bv 64 (bv_unsigned (getr regs 2%bv) - 48)))
                              (Z_to_bv 64 0x654dc) mem (seg_rom tfibsegs)) md) Q ->
  SRr_refusable W (mkCfg (mkst regs (Z_to_bv 64 tfib_A_MmapNoReserveOrDie) mem (seg_rom tfibsegs)) md) Q.
Proof.
intros W regs mem md Q H. unfold SRr_refusable. apply SRr_use_AI. intros HI. apply SRr_ret.
exists unit, (fun _ => mkCfg (mkst (regupd regs 2%bv (Z_to_bv 64 (bv_unsigned (getr regs 2%bv) - 48)))
   (Z_to_bv 64 0x654dc) mem (seg_rom tfibsegs)) md), (fun _ => false), tt.
split; [|split; [|split; [|split]]].
- apply YA05.node_instr_noacc; [exact (AI_halted _ _ _ _ HI) | reflexivity |].
  rewrite (YK0x.stepacc_opimm_gen tfibsegs regs (Z_to_bv 64 tfib_A_MmapNoReserveOrDie) mem
    (seg_rom tfibsegs) (Z_to_bv 32 0xfd010113) ALU_ADD 2%bv 2%bv (4048%bv : bv 12)).
  + rewrite sp_less48.
    replace (v_addi (Z_to_bv 64 tfib_A_MmapNoReserveOrDie) 4) with (Z_to_bv 64 0x654dc)
      by (apply bv_eq; reflexivity).
    reflexivity.
  + apply tfibtbl_mnr_ok. vm_compute. reflexivity.
  + vm_compute. reflexivity.
  + lazymatch goal with |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true) end.
- intros i HA. exact HA.
- reflexivity.
- intros i Hi. discriminate Hi.
- intros i _. exact H.
Qed.
(* every byte the entry seed's symbolic memory may write lies in the touched band *)
Lemma inw_MMEM : forall (E : env) (b : Z), base_val E (Some 2%nat) = b ->
  forall y, in_wrange E MMEM y -> b - 56 <= y < b + 48.
Proof.
intros E b Hb y (r & Hin & Hy). vm_compute in Hin.
destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]].
- cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hy. rewrite Hb in Hy. lia.
- cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hy. lia.
- cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hy. lia.
- cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hy. lia.
- cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hy. lia.
- cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hy. lia.
Qed.

Section call.
Variables (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (size fb : Z).
Hypotheses (Harg : argZ regs 0 = size) (Hpos : 0 < size) (Hpal : YG0f.page_aligned size)
  (Hra : YK0s.ret_ok (getr regs 1)).
Hypotheses (HPG : val_mem tfibsegs (mrestrict (w_H W) mem) MNR_PSC_GOT 8 MNR_PSC)
  (HPS : val_mem tfibsegs (mrestrict (w_H W) mem) MNR_PSC 8 4096)
  (HCG : val_mem tfibsegs (mrestrict (w_H W) mem) MNR_CF_GOT 8 MNR_CF)
  (HFB : val_mem tfibsegs (mrestrict (w_H W) mem) (MNR_CF + 0x104) 1 fb)
  (HFBr : 0 <= fb < 256) (HFBl : Z.land fb 1 = 0)
  (HML : val_mem tfibsegs (mrestrict (w_H W) mem) (MNR_CF + 0x90) 8 0).
Hypotheses (Hroom : md_room md size) (Hwf : YK0g.ivs_wf (vm_maps (m_vmmaps md)))
  (Hbud : eager_used md + A_bytes (w_A W) + size <= vm_limit (m_vmmaps md)).
Hypotheses (Hsp16 : spZ regs mod 16 = 0) (Hslo : kHighMemBeg <= spZ regs - MNR_STK)
  (Hshi : spZ regs <= kHighMemEnd)
  (Hpres : forall a, spZ regs - MNR_STK <= a < spZ regs -> apresent (w_H W) mem a)
  (Htakes : Forall (md_takes md) ((spZ regs - MNR_STK, MNR_STK) :: mnr_cell_extents)).

Definition sp1 : Z := spZ regs - 48.
Definition regs1 : bvmap 5 word := regupd regs 2%bv (Z_to_bv 64 (bv_unsigned (getr regs 2%bv) - 48)).
Definition E0 : env := Ereg regs1 [Z_to_bv 64 fb].
Definition ms0 : machine_state := mkst regs1 (Z_to_bv 64 0x654dc) mem (seg_rom tfibsegs).

Lemma geo : 4096 <= size /\ size + 8388608 < 2 ^ 64 /\ 0 <= spZ regs < 2 ^ 64 /\ sp1 mod 16 = 0
  /\ kHighMemBeg + 56 <= sp1 /\ sp1 + 48 <= kHighMemEnd.
Proof.
destruct Hroom as (g & Hg4 & Hgp & Hgt & _).
pose proof (alloc_top_room (m_vmmaps md)) as HR. unfold stack_max_size, two_pow_64 in HR.
pose proof (u64_range (getr regs 2%bv)) as UR.
unfold YG0f.page_aligned in Hpal.
assert (H4 : 4096 <= size).
{ pose proof Hpal as HP. apply Z.mod_divide in HP as [q Hq]; [|lia]. nia. }
unfold sp1, spZ, MNR_STK, kHighMemBeg, kHighMemEnd in *.
repeat split; try lia.
all: replace (bv_unsigned (getr regs 2%bv) - 48) with (bv_unsigned (getr regs 2%bv) + (-3) * 16) by lia;
     rewrite Z_mod_plus_full; exact Hsp16.
Qed.

Lemma HA10 : getr regs 10%bv = Z_to_bv 64 size.
Proof.
unfold argZ in Harg.
assert (Hix : (Z_to_bv 5 (10 + 0) : bv 5) = 10%bv) by (apply bv_eq; reflexivity).
rewrite Hix in Harg. rewrite <- Harg. symmetry. apply Z_to_bv_bv_unsigned.
Qed.
Lemma EW2 : bv_unsigned (ew E0 2) = sp1.
Proof.
pose proof geo as (_ & _ & UR & _ & G5 & G6).
unfold E0. rewrite (ew_Ereg_nat regs1 _ 2 2%bv eq_refl). unfold regs1.
rewrite getr_same by (intros X; discriminate). apply unsigned_lit_small.
unfold sp1, spZ, kHighMemBeg, kHighMemEnd in *. lia.
Qed.
Lemma EW10 : bv_unsigned (ew E0 10) = size.
Proof.
pose proof geo as (G1 & G2 & _).
unfold E0. rewrite (ew_Ereg_nat regs1 _ 10 10%bv eq_refl). unfold regs1.
rewrite getr_other by (intros X; discriminate). rewrite HA10. apply unsigned_lit_small. lia.
Qed.
Lemma EWFB : bv_unsigned (ew E0 aFB) = fb.
Proof. change (ew E0 aFB) with (Z_to_bv 64 fb). apply unsigned_lit_small. lia. Qed.

Lemma seed_regs : regs_ok E0 sr_atoms regs1.
Proof. unfold E0. apply regs_ok_Ereg. Qed.
Lemma rgn_FR : region_ok tfibsegs E0 (mrestrict (w_H W) mem) R_FR.
Proof.
pose proof geo as (G1 & G2 & G3 & G4 & G5 & G6).
apply (region_ok_window E0 _ 2 sp1 (-56) 48 (-56) 48 EW2);
  unfold kHighMemBeg, kHighMemEnd in *; try lia.
intros a Ha. apply apresent_writable; [unfold TFIB_IMG_END; lia|].
apply Hpres. unfold MNR_STK, sp1, spZ in *. lia.
Qed.
Lemma rgn_PG : region_ok tfibsegs E0 (mrestrict (w_H W) mem) R_PG.
Proof. apply (region_ok_lit E0 _ MNR_PSC_GOT 8 MNR_PSC HPG); unfold MNR_PSC, MNR_PSC_GOT; lia. Qed.
Lemma rgn_PS : region_ok tfibsegs E0 (mrestrict (w_H W) mem) R_PS.
Proof. apply (region_ok_lit E0 _ MNR_PSC 8 4096 HPS); unfold MNR_PSC; lia. Qed.
Lemma rgn_CG : region_ok tfibsegs E0 (mrestrict (w_H W) mem) R_CG.
Proof. apply (region_ok_lit E0 _ MNR_CF_GOT 8 MNR_CF HCG); unfold MNR_CF, MNR_CF_GOT; lia. Qed.
Lemma rgn_ML : region_ok tfibsegs E0 (mrestrict (w_H W) mem) R_ML.
Proof. apply (region_ok_lit E0 _ (MNR_CF + 0x90) 8 0 HML); unfold MNR_CF; lia. Qed.
Lemma rgn_FB : region_ok tfibsegs E0 (mrestrict (w_H W) mem) R_FB.
Proof.
unfold R_FB, mlit1, region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
split; [unfold MNR_CF; lia|]. split; [unfold MNR_CF; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
eapply (chunk_ok_val tfibsegs E0 _ 0 (MNR_CF + 0x104) 1 (SOff aFB 0) fb).
- cbn [sv_denot]. rewrite EWFB, Z.add_0_r. reflexivity.
- cbn. lia.
- cbn. lia.
- rewrite Z.add_0_l. exact HFB.
Qed.
Lemma seed_pairs : pairwise_disjoint E0 MMEM.
Proof.
pose proof geo as (G1 & G2 & G3 & G4 & G5 & G6).
apply pairwise_disjoint_of_extents.
unfold MMEM, R_FR, R_PG, R_PS, R_CG, R_FB, R_ML, lit8, mlit1, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite EW2.
unfold MNR_PSC_GOT, MNR_PSC, MNR_CF_GOT, MNR_CF.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
unfold kHighMemBeg, kHighMemEnd in *. repeat split; lia.
Qed.
Lemma seed_atoms : Forall (fun nf : nat * afact => afact_ok E0 (fst nf) (snd nf)) MF_fix.
Proof.
pose proof geo as (G1 & G2 & G3 & G4 & G5 & G6).
unfold MF_fix. apply Forall_cons.
{ apply (AFo2 E0 2%nat sp1); [| | | |lia].
  - unfold E0. rewrite (ew_Ereg_nat regs1 _ 2 2%bv eq_refl). unfold regs1, sp1, spZ.
    rewrite getr_same by (intros X; discriminate). reflexivity.
  - unfold sp1, spZ, kHighMemBeg, kHighMemEnd in *. lia.
  - unfold kHighMemBeg, kHighMemEnd in *. lia.
  - change (2 ^ 4) with 16. exact G4. }
apply Forall_cons.
{ apply (AFo2 E0 10%nat size).
  - unfold E0. rewrite (ew_Ereg_nat regs1 _ 10 10%bv eq_refl). unfold regs1.
    rewrite getr_other by (intros X; discriminate). exact HA10.
  - lia.
  - unfold MNR_SZ_MAX. lia.
  - change (2 ^ 12) with 4096. exact Hpal.
  - lia. }
apply Forall_cons; [| apply Forall_nil].
apply (AFo2 E0 aFB fb); [reflexivity | lia | lia | apply Z.mod_1_r | lia].
Qed.
Lemma seed_ok : st_ok tfibsegs E0 SM0 (restrict (w_H W) ms0).
Proof.
unfold ms0. rewrite restrict_mkst_fx. unfold SM0, E0. apply (entry_st_ok_full tfibsegs).
- exact seed_regs.
- vm_compute. reflexivity.
- apply Forall_cons; [exact rgn_FR|]. apply Forall_cons; [exact rgn_PG|].
  apply Forall_cons; [exact rgn_PS|]. apply Forall_cons; [exact rgn_CG|].
  apply Forall_cons; [exact rgn_FB|]. apply Forall_cons; [exact rgn_ML | apply Forall_nil].
- exact seed_pairs.
- split; [| split; exact I]. cbn [f_atoms]. apply atoms_ok_of_Forall2. exact seed_atoms.
Qed.

(* The two name arms of GetNamedMappingFd converge: at the ecall they have the same registers and the same
   symbolic memory, and differ only in the branch condition they carry. So one tail serves both. *)
Lemma arms_converge : ss_regs SM3 = ss_regs SM2 /\ ss_mem SM3 = ss_mem SM2
  /\ ss_pc SM2 = 0x638d4 /\ ss_pc SM3 = 0x638d4 /\ ss_resv SM2 = None /\ ss_resv SM3 = None.
Proof. repeat split; vm_compute; reflexivity. Qed.

Definition POST : world tfibsegs -> config -> Prop := fun W' c' =>
  exists x regs' mem' md',
    c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom tfibsegs)) md' /\
    getr regs' 10 = Z_to_bv 64 x /\ regs_preserved regs regs' /\
    YG0f.page_aligned x /\ 4096 <= x /\ grant_ok_na_pin md (Z_to_bv 64 x) size = true /\
    Forall (fun q => zdisjoint (x, size) (bv_unsigned (fst q), bv_unsigned (snd q)))
      (vm_reserved (m_vmmaps md) ++ vm_maps (m_vmmaps md)) /\
    x + size <= alloc_top (m_vmmaps md) /\
    (forall i, 0 <= i < size ->
       apresent (w_H W') mem' (x + i) /\ aview tfibsegs (w_H W') mem' (x + i) = Some 0) /\
    w_A W' = (x, x + size) :: w_A W /\
    (forall a : word, ~ (x <= bv_unsigned a < x + size) -> w_H W' a = w_H W a) /\
    (forall a : word, ~ (spZ regs - MNR_STK <= bv_unsigned a < spZ regs) ->
       ~ (x <= bv_unsigned a < x + size) -> mem' a = mem a) /\
    (forall a, apresent (w_H W) mem a -> apresent (w_H W') mem' a) /\ same_io md md' /\
    md_takes md' (x, size) /\ (forall e, md_takes md e -> md_takes md' e) /\
    (exists mat, md' = with_vm_backing
         (m_vm_lazy (YK0x.mmap_model_noreserve (Z_to_bv 64 x) (Z_to_bv 64 size) md)) mat
         (YK0x.mmap_model_noreserve (Z_to_bv 64 x) (Z_to_bv 64 size) md)) /\
    m_vmmaps md' = m_vmmaps (mmap_model (Z_to_bv 64 x) (Z_to_bv 64 size) md) /\
    m_vm_lazy md' = (Z_to_bv 64 x, Z_to_bv 64 size) :: m_vm_lazy md /\
    eager_used md' = eager_used md.

(* ---- after the ecall: one tail serves both name arms (arms_converge) ---- *)
Definition E1 (a : word) : env := Ereg regs1 ([Z_to_bv 64 fb] ++ [a]).
Lemma HEA : forall a, env_agree 33 E0 (E1 a).
Proof. intros a. unfold E0, E1. apply env_agree_Ereg_app. cbn [length]. lia. Qed.

Lemma mr_out : forall (W3 : world tfibsegs) (a : word) (m : word -> option byte) (y : Z),
  (forall z : word, ~ (bv_unsigned a <= bv_unsigned z < bv_unsigned a + size) -> w_H W3 z = w_H W z) ->
  bv_unsigned (Z_to_bv 64 size) = size ->
  0 <= y < 2 ^ 64 -> ~ (bv_unsigned a <= y < bv_unsigned a + size) ->
  mrestrict (w_H W3) (zfill a (Z_to_bv 64 size) m) (Z_to_bv 64 y) = mrestrict (w_H W) m (Z_to_bv 64 y).
Proof.
intros W3 a m y HH Hn Hy Hout. unfold mrestrict.
rewrite (HH (Z_to_bv 64 y) ltac:(rewrite YK00.u64_lit by lia; exact Hout)).
rewrite (YK0v.zfill_out a (Z_to_bv 64 size) m (Z_to_bv 64 y)
  ltac:(rewrite YK00.u64_lit by lia; rewrite Hn; lia)).
reflexivity.
Qed.

Lemma grant_misses : forall (a : word) e, grant_ok_na_pin md a size = true -> md_takes md e ->
  forall y, fst e <= y < fst e + snd e -> ~ (bv_unsigned a <= y < bv_unsigned a + size).
Proof.
intros a e Hg Ht y Hy Hin.
pose proof geo as (G1 & G2 & _).
destruct (gnap_parts md a size Hg) as (Hal & _ & Htop & Hrf).
pose proof (alloc_top_room (m_vmmaps md)) as HR. unfold stack_max_size, two_pow_64 in HR.
assert (Hnun : bv_unsigned (Z_to_bv 64 size) = size) by (apply YK00.u64_lit; lia).
destruct Ht as [[Hsz Hcov] | Hat].
- specialize (Hcov y ltac:(unfold in_zr; exact Hy)).
  apply Exists_exists in Hcov as ([b s] & Hq & Hb). cbn [fst snd] in Hb.
  destruct (YK13.region_free_In _ a (Z_to_bv 64 size) b s Hrf Hq) as [D|D]; lia.
- pose proof (grant_end_page_floor (bv_unsigned a) size (alloc_top (m_vmmaps md)) Hal Hpal Htop) as Hpf. lia.
Qed.

(* every byte the tail's symbolic memory may write lies in the touched band *)
Lemma inw_SMT : forall (E : env), base_val E (Some 2%nat) = sp1 ->
  forall y, in_wrange E (ss_mem SMT) y -> sp1 - 56 <= y < sp1 + 48.
Proof.
intros E Hb y (r & Hin & Hy). vm_compute in Hin.
destruct Hin as [<-|[<-|[<-|[]]]].
- cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hy. rewrite Hb in Hy. lia.
- cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hy. lia.
- cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hy. lia.
Qed.

Lemma ecall_and_tail : forall (ss : sstate) (ms : machine_state) (model : Model),
  ss_regs ss = ss_regs SM2 -> ss_mem ss = ss_mem SM2 -> ss_pc ss = 0x638d4 -> ss_resv ss = None ->
  st_ok_ecall tfibsegs E0 ss (restrict (w_H W) ms) ->
  (forall y : word, ~ (spZ regs - MNR_STK <= bv_unsigned y < spZ regs) -> ms_mem ms y = mem y) ->
  mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) (ms_mem ms)) ->
  (exists mt, model = with_vm_backing (m_vm_lazy md) mt md) ->
  SRr tfibsegs W (mkCfg ms model) POST.
Proof.
intros ss ms model HRG HMM HPC HRV HS HFR HGR (mt & Hmodel).
pose proof geo as (G1 & G2 & G3 & G4 & G5 & G6).
pose proof (alloc_top_room (m_vmmaps md)) as HR. unfold stack_max_size, two_pow_64 in HR.
assert (Hnun : bv_unsigned (Z_to_bv 64 size) = size) by (apply YK00.u64_lit; lia).
pose proof (Forall_inv Htakes) as HTband.
pose proof (Forall_inv_tail Htakes) as HTc. unfold mnr_cell_extents in HTc.
pose proof (Forall_inv HTc) as HTcg.
pose proof (Forall_inv (Forall_inv_tail HTc)) as HTml.
destruct (st_ok_ecall_shape_r tfibsegs (w_H W) E0 ss ms HS HRV) as (regs_e & mem_e & Hms & HRE & HME & HFA).
assert (Hmse : ms_mem ms = mem_e) by (rewrite Hms; reflexivity).
rewrite Hmse in HFR, HGR.
assert (R10 : getr regs_e 10%bv = Z_to_bv 64 0) by (rewrite (HRE 10%bv), HRG; red_sr; reflexivity).
assert (R12 : getr regs_e 12%bv = Z_to_bv 64 3) by (rewrite (HRE 12%bv), HRG; red_sr; reflexivity).
assert (R13 : getr regs_e 13%bv = Z_to_bv 64 16418) by (rewrite (HRE 13%bv), HRG; red_sr; reflexivity).
assert (R15 : getr regs_e 15%bv = Z_to_bv 64 0) by (rewrite (HRE 15%bv), HRG; red_sr; reflexivity).
assert (R17 : getr regs_e 17%bv = Z_to_bv 64 222) by (rewrite (HRE 17%bv), HRG; red_sr; reflexivity).
assert (R14 : getr regs_e 14%bv = Z_to_bv 64 (-1)).
{ rewrite (HRE 14%bv), HRG. red_sr. apply bv_eq. reflexivity. }
assert (R11 : getr regs_e 11%bv = Z_to_bv 64 size).
{ rewrite (HRE 11%bv), HRG. red_sr. rewrite denot_off0, <- EW10. symmetry. apply Z_to_bv_bv_unsigned. }
assert (Hvm : m_vmmaps (with_vm_backing (m_vm_lazy md) mt md) = m_vmmaps md) by apply m_vmmaps_wvb.
assert (Heg : eager_used (with_vm_backing (m_vm_lazy md) mt md) = eager_used md) by apply eager_used_wvb.
assert (Hgrant : exists g, grant_ok_na_pin (with_vm_backing (m_vm_lazy md) mt md) g size = true).
{ destruct Hroom as (g & Hg4 & Hgp & Hgt & Hgf). exists (Z_to_bv 64 g).
  assert (Hgu : bv_unsigned (Z_to_bv 64 g) = g) by (apply YK00.u64_lit; lia).
  unfold grant_ok_na_pin. rewrite Hvm, Hgu.
  repeat (apply andb_true_iff; split).
  - apply Z.eqb_eq. exact Hg4.
  - apply Z.ltb_lt. exact Hgp.
  - apply Z.leb_le. exact Hgt.
  - exact Hgf. }
rewrite Hms, HPC, Hmodel.
apply (mnr_ecall_step W regs_e (Z_to_bv 64 0x638d4) mem_e (with_vm_backing (m_vm_lazy md) mt md) size POST
  R17 R10 R11 Hpos ltac:(lia) Hpal R12 R13 R14 R15
  ltac:(rewrite Hvm; exact Hwf) Hgrant ltac:(rewrite Hvm, Heg; exact Hbud)).
intros a W3 Hg HLE HA3 HV1 HV2 HVout HAI3.
destruct (gnap_parts _ a size Hg) as (Hxal & Hxpos & Hxtop & Hxrf).
rewrite Hvm in Hxtop, Hxrf.
assert (Hx4096 : 4096 <= bv_unsigned a).
{ pose proof Hxal as Hq. apply Z.mod_divide in Hq as [q Hq]; [|unfold page_size; lia].
  unfold page_size in Hq. nia. }
assert (Hgmd : grant_ok_na_pin md a size = true).
{ unfold grant_ok_na_pin. repeat (apply andb_true_iff; split).
  - apply Z.eqb_eq. exact Hxal.
  - apply Z.ltb_lt. exact Hxpos.
  - apply Z.leb_le. exact Hxtop.
  - exact Hxrf. }
assert (MissB : forall y, spZ regs - MNR_STK <= y < spZ regs -> ~ (bv_unsigned a <= y < bv_unsigned a + size)).
{ intros y Hy. apply (grant_misses a _ Hgmd HTband y). cbn [fst snd]. unfold MNR_STK in *. lia. }
assert (MissCG : forall y, MNR_CF_GOT <= y < MNR_CF_GOT + 8 -> ~ (bv_unsigned a <= y < bv_unsigned a + size)).
{ intros y Hy. apply (grant_misses a _ Hgmd HTcg y). cbn [fst snd]. lia. }
assert (MissML : forall y, MNR_CF + 0x90 <= y < MNR_CF + 0x90 + 8 -> ~ (bv_unsigned a <= y < bv_unsigned a + size)).
{ intros y Hy. apply (grant_misses a _ Hgmd HTml y). cbn [fst snd]. lia. }
assert (Hpc4 : v_addi (Z_to_bv 64 0x638d4) 4 = Z_to_bv 64 0x638d8) by (apply bv_eq; reflexivity).
rewrite Hpc4.
assert (HbaseE : base_val (E1 a) (Some 2%nat) = base_val E0 (Some 2%nat))
  by (apply (base_val_agree 33%nat E0 (E1 a) (Some 2%nat) (HEA a)); reflexivity).
assert (HEW2' : base_val E0 (Some 2%nat) = sp1) by (cbn [base_val]; exact EW2).
rewrite HMM in HME. destruct HME as (HWf0 & HAll0 & HPd0).
assert (InFR : In R_FR2 (ss_mem SM2)) by (vm_compute; left; reflexivity).
assert (InCG : In R_CG (ss_mem SM2)) by (vm_compute; right; right; right; left; reflexivity).
assert (InML : In R_ML (ss_mem SM2)) by (vm_compute; right; right; right; right; right; left; reflexivity).
pose proof (proj1 (Forall_forall _ _) HAll0 R_FR2 InFR) as HrFR.
pose proof (proj1 (Forall_forall _ _) HAll0 R_CG InCG) as HrCG.
pose proof (proj1 (Forall_forall _ _) HAll0 R_ML InML) as HrML.
assert (HT : st_ok tfibsegs (E1 a) SMT
   (restrict (w_H W3) (mkst (regupd regs_e 10%bv a) (Z_to_bv 64 0x638d8)
       (zfill a (Z_to_bv 64 size) mem_e) (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold st_ok, SMT.
  cbn [ss_pc ss_regs ss_mem ss_resv ss_facts mkst ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr
       ms_rom ms_regs ms_mem].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split.
  - rewrite TREGS_eq.
    pose proof (regs_ok_agree 33%nat E0 (E1 a) (ss_regs SM2) regs_e (HEA a)
                  ltac:(vm_compute; reflexivity) ltac:(rewrite <- HRG; exact HRE)) as HR1.
    pose proof (regs_ok_set (E1 a) (ss_regs SM2) regs_e 10%bv a (SOff aGR 0) HR1
                  ltac:(rewrite denot_off0; reflexivity)) as HR2.
    cbn [bv_eqb] in HR2. exact HR2.
  - split.
    + unfold mem_ok. split; [vm_compute; reflexivity|]. split.
      * apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]].
        -- apply (region_ok_transport tfibsegs E0 (E1 a) (mrestrict (w_H W) mem_e)
                    (mrestrict (w_H W3) (zfill a (Z_to_bv 64 size) mem_e)) R_FR2 HrFR).
           ++ rewrite R_FR2_base. exact HbaseE.
           ++ intros c Hc. vm_compute in Hc.
              repeat (destruct Hc as [<-|Hc];
                [ cbn [YP09.c_val]; apply (sv_denot_agree 33%nat E0 (E1 a) _ (HEA a)); reflexivity |]).
              destruct Hc.
           ++ intros y Hy. rewrite R_FR2_base, R_FR2_lo, R_FR2_hi, HEW2' in Hy.
              apply mb_eq. apply (mr_out W3 a mem_e y HVout Hnun);
                [unfold sp1, spZ, kHighMemBeg, kHighMemEnd in *; lia
                | apply MissB; unfold MNR_STK, sp1, spZ in *; lia].
           ++ intros y Hy Hw. rewrite R_FR2_base, R_FR2_wlo, R_FR2_whi, HEW2' in Hy.
              apply (wr_eq (mrestrict (w_H W) mem_e)
                (mrestrict (w_H W3) (zfill a (Z_to_bv 64 size) mem_e)) y); [| exact Hw].
              apply (mr_out W3 a mem_e y HVout Hnun);
                [unfold sp1, spZ, kHighMemBeg, kHighMemEnd in *; lia
                | apply MissB; unfold MNR_STK, sp1, spZ in *; lia].
           ++ vm_compute. reflexivity.
        -- apply (region_ok_transport tfibsegs E0 (E1 a) (mrestrict (w_H W) mem_e)
                    (mrestrict (w_H W3) (zfill a (Z_to_bv 64 size) mem_e)) R_CG HrCG).
           ++ reflexivity.
           ++ intros c Hc. vm_compute in Hc. destruct Hc as [<-|Hc]; [reflexivity | destruct Hc].
           ++ intros y Hy. cbn [YP09.r_base YP09.r_lo YP09.r_hi R_CG lit8 base_val] in Hy.
              apply mb_eq. apply (mr_out W3 a mem_e y HVout Hnun);
                [unfold MNR_CF_GOT in *; lia | apply MissCG; unfold MNR_CF_GOT in *; lia].
           ++ intros y Hy Hw. cbn [YP09.r_base YP09.r_wlo YP09.r_whi R_CG lit8 base_val] in Hy. lia.
           ++ vm_compute. reflexivity.
        -- apply (region_ok_transport tfibsegs E0 (E1 a) (mrestrict (w_H W) mem_e)
                    (mrestrict (w_H W3) (zfill a (Z_to_bv 64 size) mem_e)) R_ML HrML).
           ++ reflexivity.
           ++ intros c Hc. vm_compute in Hc. destruct Hc as [<-|Hc]; [reflexivity | destruct Hc].
           ++ intros y Hy. cbn [YP09.r_base YP09.r_lo YP09.r_hi R_ML lit8 base_val] in Hy.
              apply mb_eq. apply (mr_out W3 a mem_e y HVout Hnun);
                [unfold MNR_CF in *; lia | apply MissML; unfold MNR_CF in *; lia].
           ++ intros y Hy Hw. cbn [YP09.r_base YP09.r_wlo YP09.r_whi R_ML lit8 base_val] in Hy. lia.
           ++ vm_compute. reflexivity.
      * apply pairwise_disjoint_of_extents.
        unfold R_CG, R_ML, lit8, extent_of_region.
        cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite R_FR2_base, R_FR2_lo, R_FR2_hi.
        cbn [base_val]. rewrite (proj1 (HEA a) 2%nat ltac:(lia)), EW2.
        unfold MNR_CF_GOT, MNR_CF. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
        unfold sp1, spZ, kHighMemBeg, kHighMemEnd in *. repeat split; lia.
    + split; [| split; exact I]. cbn [f_atoms]. apply atoms_ok_of_Forall2.
      unfold TF. apply Forall_cons.
      { apply (AFo2 (E1 a) 2%nat sp1); [| | | |lia].
        - rewrite (proj1 (HEA a) 2%nat ltac:(lia)). unfold E0.
          rewrite (ew_Ereg_nat regs1 _ 2 2%bv eq_refl). unfold regs1, sp1, spZ.
          rewrite getr_same by (intros X; discriminate). reflexivity.
        - unfold sp1, spZ, kHighMemBeg, kHighMemEnd in *. lia.
        - unfold kHighMemBeg, kHighMemEnd in *. lia.
        - change (2 ^ 4) with 16. exact G4. }
      apply Forall_cons.
      { apply (AFo2 (E1 a) 10%nat size).
        - rewrite (proj1 (HEA a) 10%nat ltac:(lia)). unfold E0.
          rewrite (ew_Ereg_nat regs1 _ 10 10%bv eq_refl). unfold regs1.
          rewrite getr_other by (intros X; discriminate). exact HA10.
        - lia.
        - unfold MNR_SZ_MAX. lia.
        - change (2 ^ 12) with 4096. exact Hpal.
        - lia. }
      apply Forall_cons; [| apply Forall_nil].
      apply (AFo2 (E1 a) aGR (bv_unsigned a)).
      { change (ew (E1 a) aGR) with a. symmetry. apply Z_to_bv_bv_unsigned. }
      { pose proof (u64_range a). lia. }
      { unfold MNR_SZ_MAX. lia. }
      { change (2 ^ 12) with 4096. unfold page_size in Hxal. exact Hxal. }
      { lia. } }
pose proof (inw_SMT (E1 a) ltac:(rewrite HbaseE; exact HEW2')) as INW.
assert (Hrun : sym_runN_sh tfibsegs tfibtbl_mnr FUEL SMT = (SMF, RS_stopped (SR_jalr (SOff 1 0))))
  by (vm_compute; reflexivity).
eapply (SRr_run_shG tfibtbl_mnr tfibtbl_mnr_ok W3 FUEL (E1 a) SMT SMF _ _ _ POST HT Hrun).
intros msF matF HTF HFF HGF.
eapply (SRr_ret_at tfibsegs tfibtbl_mnr tfibtbl_mnr_ok Hwx_tfa W3 (E1 a) SMF msF _ POST HTF eq_refl
          ltac:(vm_compute; reflexivity)).
intros matG. rewrite wvb_collapse.
(* ---- the post ---- *)
assert (HRf : regs_ok (E1 a) (ss_regs SMF) (ms_regs msF))
  by (destruct HTF as (_ & _ & _ & _ & _ & _ & HX & _); cbn [restrict ms_regs] in HX; exact HX).
assert (RF : forall (r : bv 5) (n : nat), sr_get (ss_regs SMF) r = SOff n 0 ->
   getr (ms_regs msF) r = ew (E1 a) n).
{ intros r n Hr. rewrite (HRf r), Hr. apply denot_off0. }
assert (RPres : forall (r : bv 5) (n : nat), (n < 33)%nat -> Z.of_nat n = bv_unsigned r -> r <> 2%bv ->
   sr_get (ss_regs SMF) r = SOff n 0 -> getr (ms_regs msF) r = getr regs r).
{ intros r n Hn33 Hn Hr2 Hr. rewrite (RF r n Hr), (proj1 (HEA a) n Hn33). unfold E0.
  rewrite (ew_Ereg_nat regs1 _ n r Hn). unfold regs1. rewrite getr_other by exact Hr2. reflexivity. }
assert (R1F : getr (ms_regs msF) 1%bv = getr regs 1%bv)
  by (apply (RPres 1%bv 1%nat); [lia | reflexivity | intros X; discriminate | vm_compute; reflexivity]).
assert (R10F : getr (ms_regs msF) 10%bv = a)
  by (rewrite (RF 10%bv aGR ltac:(vm_compute; reflexivity)); reflexivity).
assert (R2F : getr (ms_regs msF) 2%bv = getr regs 2%bv).
{ rewrite (HRf 2%bv). red_sr. cbn [sv_denot].
  rewrite (proj1 (HEA a) 2%nat ltac:(lia)), EW2. unfold sp1, spZ.
  replace (bv_unsigned (getr regs 2%bv) - 48 + 48) with (bv_unsigned (getr regs 2%bv)) by lia.
  apply Z_to_bv_bv_unsigned. }
assert (MF : forall y : word, ~ (sp1 - 56 <= bv_unsigned y < sp1 + 48) ->
   ms_mem msF y = zfill a (Z_to_bv 64 size) mem_e y).
{ intros y Hy. apply HFF. intros Hin. apply Hy. exact (INW _ Hin). }
assert (MissBand : forall y, sp1 - 56 <= y < sp1 + 48 -> ~ (bv_unsigned a <= y < bv_unsigned a + size)).
{ intros y Hy. apply MissB. unfold sp1, spZ, MNR_STK in *. lia. }
unfold POST.
exists (bv_unsigned a), (ms_regs msF), (ms_mem msF),
  (with_vm_backing (m_vm_lazy (YK0x.mmap_model_noreserve a (Z_to_bv 64 size)
      (with_vm_backing (m_vm_lazy md) mt md))) matG
   (YK0x.mmap_model_noreserve a (Z_to_bv 64 size) (with_vm_backing (m_vm_lazy md) mt md))).
assert (Hazb : Z_to_bv 64 (bv_unsigned a) = a) by apply Z_to_bv_bv_unsigned.
split.
{ rewrite R1F. unfold YK0s.ret_ok in Hra. rewrite Hra. reflexivity. }
split; [rewrite R10F, Hazb; reflexivity|].
split.
{ apply regs_preserved_intro; try exact R2F;
  solve [ apply (RPres 3%bv 3%nat); [lia | reflexivity | intros X; discriminate | vm_compute; reflexivity]
        | apply (RPres 4%bv 4%nat); [lia | reflexivity | intros X; discriminate | vm_compute; reflexivity]
        | apply (RPres 8%bv 8%nat); [lia | reflexivity | intros X; discriminate | vm_compute; reflexivity]
        | apply (RPres 9%bv 9%nat); [lia | reflexivity | intros X; discriminate | vm_compute; reflexivity]
        | apply (RPres 18%bv 18%nat); [lia | reflexivity | intros X; discriminate | vm_compute; reflexivity]
        | apply (RPres 19%bv 19%nat); [lia | reflexivity | intros X; discriminate | vm_compute; reflexivity]
        | apply (RPres 20%bv 20%nat); [lia | reflexivity | intros X; discriminate | vm_compute; reflexivity]
        | apply (RPres 21%bv 21%nat); [lia | reflexivity | intros X; discriminate | vm_compute; reflexivity]
        | apply (RPres 22%bv 22%nat); [lia | reflexivity | intros X; discriminate | vm_compute; reflexivity]
        | apply (RPres 23%bv 23%nat); [lia | reflexivity | intros X; discriminate | vm_compute; reflexivity]
        | apply (RPres 24%bv 24%nat); [lia | reflexivity | intros X; discriminate | vm_compute; reflexivity]
        | apply (RPres 25%bv 25%nat); [lia | reflexivity | intros X; discriminate | vm_compute; reflexivity]
        | apply (RPres 26%bv 26%nat); [lia | reflexivity | intros X; discriminate | vm_compute; reflexivity]
        | apply (RPres 27%bv 27%nat); [lia | reflexivity | intros X; discriminate | vm_compute; reflexivity] ]. }
split; [unfold YG0f.page_aligned; unfold page_size in Hxal; exact Hxal|].
split; [exact Hx4096|].
split; [rewrite Hazb; exact Hgmd|].
split.
{ apply Forall_forall. intros [b s] Hq. unfold zdisjoint. cbn [fst snd].
  destruct (YK13.region_free_In _ a (Z_to_bv 64 size) b s Hxrf Hq) as [D|D]; lia. }
split; [exact Hxtop|].
split.
{ intros i Hi.
  assert (Hyr : bv_unsigned (Z_to_bv 64 (bv_unsigned a + i)) = bv_unsigned a + i)
    by (apply YK00.u64_lit; pose proof (u64_range a); lia).
  assert (Hh : w_H W3 (Z_to_bv 64 (bv_unsigned a + i)) = false) by (apply HV1; rewrite Hyr; lia).
  assert (Hb0 : ms_mem msF (Z_to_bv 64 (bv_unsigned a + i)) = Some (Z_to_bv 8 0)).
  { rewrite (MF (Z_to_bv 64 (bv_unsigned a + i))
      ltac:(rewrite Hyr; intros Hband; exact (MissBand _ Hband ltac:(lia)))).
    apply YA09.zfill_in. rewrite Hyr, Hnun. lia. }
  split.
  - split; [exact Hh | exists (Z_to_bv 8 0); exact Hb0].
  - unfold aview, mbyte, mrestrict. rewrite Hh, Hb0. reflexivity. }
split; [rewrite HA3; reflexivity|].
split; [intros y Hy; apply HVout; exact Hy|].
split.
{ intros y H1 H2. rewrite (MF y ltac:(unfold sp1, spZ, MNR_STK in *; lia)).
  rewrite (YK0v.zfill_out a (Z_to_bv 64 size) mem_e y ltac:(lia)). exact (HFR y H1). }
split.
{ intros y Hp.
  apply (apresent_grows (w_H W3) (zfill a (Z_to_bv 64 size) mem_e) (ms_mem msF) y HGF).
  apply (apresent_hmono2 (w_H W) (w_H W3) _ y HV2).
  apply apresent_zfill.
  apply (apresent_grows (w_H W) mem mem_e y HGR). exact Hp. }
assert (HVMT : vm_maps (m_vmmaps (YK0x.mmap_model_noreserve a (Z_to_bv 64 size)
                 (with_vm_backing (m_vm_lazy md) mt md)))
             = (a, Z_to_bv 64 size) :: vm_maps (m_vmmaps md)) by reflexivity.
assert (HATT : alloc_top (m_vmmaps (YK0x.mmap_model_noreserve a (Z_to_bv 64 size)
                 (with_vm_backing (m_vm_lazy md) mt md))) = alloc_top (m_vmmaps md)) by reflexivity.
assert (HRES : vm_reserved (m_vmmaps (YK0x.mmap_model_noreserve a (Z_to_bv 64 size)
                 (with_vm_backing (m_vm_lazy md) mt md))) = vm_reserved (m_vmmaps md)) by reflexivity.
split.
{ eapply same_io_trans; [| apply same_io_with_vm_backing].
  eapply same_io_trans; [apply same_io_with_vm_backing | apply nr_io]. }
split.
{ left. split; [cbn [snd]; lia|]. intros y Hy. unfold in_zr in Hy. cbn [fst snd] in Hy.
  apply Exists_exists. exists (a, Z_to_bv 64 size). split.
  - apply in_or_app. right. rewrite m_vmmaps_wvb, HVMT. left. reflexivity.
  - cbn [fst snd]. lia. }
split.
{ intros e He. destruct He as [[Hsz Hcov] | Hat].
  - left. split; [exact Hsz|]. intros y Hy. apply Exists_exists.
    destruct (Exists_exists (fun q => bv_unsigned (fst q) <= y < bv_unsigned (fst q) + bv_unsigned (snd q))
      (vm_reserved (m_vmmaps md) ++ vm_maps (m_vmmaps md))) as [HEx _].
    destruct (HEx (Hcov y Hy)) as (q & Hq & Hqy). exists q. split; [| exact Hqy].
    rewrite m_vmmaps_wvb, HRES, HVMT. apply in_app_iff in Hq as [Hq|Hq];
      [apply in_or_app; left; exact Hq | apply in_or_app; right; right; exact Hq].
  - right. rewrite m_vmmaps_wvb, HATT. exact Hat. }
split.
{ exists matG. rewrite Hazb, nr_wvb, m_vm_lazy_wvb, wvb_wvb. reflexivity. }
split.
{ rewrite Hazb, m_vmmaps_wvb. reflexivity. }
split.
{ rewrite Hazb, m_vm_lazy_wvb, YK0x.mmap_model_noreserve_lazy, m_vm_lazy_wvb.
  rewrite (YK0g.lazy_interior_aligned a (Z_to_bv 64 size) Hxal
    ltac:(rewrite Hnun; exact Hpal) ltac:(rewrite Hnun; lia) ltac:(rewrite Hnun; lia)). reflexivity. }
rewrite eager_used_wvb.
rewrite (eager_used_nr a (Z_to_bv 64 size) (with_vm_backing (m_vm_lazy md) mt md)
  ltac:(rewrite m_vmmaps_wvb; exact Hwf) Hxal
  ltac:(rewrite Hnun; exact Hpal) ltac:(rewrite Hnun; lia) ltac:(rewrite Hnun; lia)
  ltac:(rewrite m_vmmaps_wvb; exact Hxrf)).
exact Heg.
Qed.

Lemma tail_glue : forall (ss' : sstate) (ms1 msx : machine_state),
  windows (ss_mem ss') = windows MMEM ->
  (forall y : word, ~ (spZ regs - MNR_STK <= bv_unsigned y < spZ regs) -> ms_mem ms1 y = mem y) ->
  mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) (ms_mem ms1)) ->
  frame_of E0 (ss_mem ss') (ms_mem ms1) (ms_mem msx) ->
  mem_grows (mrestrict (w_H W) (ms_mem ms1)) (mrestrict (w_H W) (ms_mem msx)) ->
  (forall y : word, ~ (spZ regs - MNR_STK <= bv_unsigned y < spZ regs) -> ms_mem msx y = mem y)
  /\ mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) (ms_mem msx)).
Proof.
intros ss' ms1 msx HW HFR HGR HF HG.
pose proof geo as (G1 & G2 & G3 & G4 & G5 & G6).
split; [| exact (mem_grows_trans' _ _ _ HGR HG)].
intros y Hy. rewrite (HF y); [exact (HFR y Hy)|].
intros Hin.
pose proof (inw_MMEM E0 sp1 ltac:(cbn [base_val]; exact EW2) _
  (in_wrange_of_windows E0 (ss_mem ss') MMEM _ (eq_sym HW) Hin)) as HBd.
apply Hy. unfold sp1, spZ, MNR_STK in *. lia.
Qed.

Lemma mnr_walk : SRr_refusable W
  (mkCfg (mkst regs (Z_to_bv 64 tfib_A_MmapNoReserveOrDie) mem (seg_rom tfibsegs)) md) POST.
Proof using All.
apply mnr_entry_node.
change (mkst (regupd regs 2%bv (Z_to_bv 64 (bv_unsigned (getr regs 2%bv) - 48)))
          (Z_to_bv 64 0x654dc) mem (seg_rom tfibsegs)) with ms0.
assert (Hrun0 : sym_runN_sh tfibsegs tfibtbl_mnr FUEL SM0
                = (SM1, RS_stopped (SR_branch BC_EQ (SOff 11 0) (SLit 0)))) by (vm_compute; reflexivity).
eapply (SRr_run_shG tfibtbl_mnr tfibtbl_mnr_ok W FUEL E0 SM0 SM1 _ _ _ POST seed_ok Hrun0).
intros ms1 mat1 HS1 HF1 HG1.
cbn [ms_mem ms0 mkst] in HF1, HG1.
assert (HFR1 : forall y : word, ~ (spZ regs - MNR_STK <= bv_unsigned y < spZ regs) -> ms_mem ms1 y = mem y
               /\ True).
{ intros y Hy. split; [| exact I]. apply (HF1 y). intros Hin.
  pose proof geo as (G1 & G2 & G3 & G4 & G5 & G6).
  pose proof (inw_MMEM E0 sp1 ltac:(cbn [base_val]; exact EW2) _ Hin) as HBd.
  apply Hy. unfold sp1, spZ, MNR_STK in *. lia. }
assert (HFR1' : forall y : word, ~ (spZ regs - MNR_STK <= bv_unsigned y < spZ regs) -> ms_mem ms1 y = mem y)
  by (intros y Hy; exact (proj1 (HFR1 y Hy))).
apply (SRr_sym_branch tfibsegs W E0 SM1 ms1 _ POST BC_EQ (SOff 11 0) (SLit 0) HS1).
- intros Hbt HSa.
  assert (Hruna : sym_runN_sh tfibsegs tfibtbl_mnr FUEL (add_cond SM1 c_n0) = (SM2, RS_ecall))
    by (vm_compute; reflexivity).
  eapply (SRr_run_shG tfibtbl_mnr tfibtbl_mnr_ok W FUEL E0 (add_cond SM1 c_n0) SM2 _ _ _ POST HSa Hruna).
  intros msa mata HSa2 HFa HGa.
  destruct (tail_glue (add_cond SM1 c_n0) ms1 msa ltac:(vm_compute; reflexivity) HFR1' HG1 HFa HGa)
    as [HFRa HGRa].
  rewrite wvb_collapse.
  exact (ecall_and_tail SM2 msa _ eq_refl eq_refl ltac:(vm_compute; reflexivity)
           ltac:(vm_compute; reflexivity) HSa2 HFRa HGRa (ex_intro _ mata eq_refl)).
- intros Hbf HSb.
  assert (Hrunb : sym_runN_sh tfibsegs tfibtbl_mnr FUEL (add_cond SM1 c_nn)
          = (SM1n, RS_stopped (SR_branch BC_EQ (SAlu ALU_AND (SOff aFB 0) (SLit 1)) (SLit 0))))
    by (vm_compute; reflexivity).
  eapply (SRr_run_shG tfibtbl_mnr tfibtbl_mnr_ok W FUEL E0 (add_cond SM1 c_nn) SM1n _ _ _ POST HSb Hrunb).
  intros msb matb HSb2 HFb HGb.
  apply (st_ok_pin_regU E0 _ _ 12%bv (SLit 0)) in HSb2; [| intros X; discriminate |].
  2:{ pose proof EWFB as HFBv. unfold aFB in HFBv.
      red_sr. rewrite !U_zev by reflexivity. cbn [zev svpure]. unfold rho_of. rewrite HFBv.
      unfold zcanon, M64. cbn [zalu_raw]. rewrite Z.add_0_r, (Z.mod_small fb) by lia.
      rewrite (Z.mod_small 1) by lia. rewrite HFBl. reflexivity. }
  assert (Hrunc : sym_runN_sh tfibsegs tfibtbl_mnr FUEL (pin12 SM1n) = (SM3, RS_ecall))
    by (vm_compute; reflexivity).
  eapply (SRr_run_shG tfibtbl_mnr tfibtbl_mnr_ok W FUEL E0 (pin12 SM1n) SM3 _ _ _ POST HSb2 Hrunc).
  intros msc matc HSc HFc HGc.
  destruct (tail_glue (add_cond SM1 c_nn) ms1 msb ltac:(vm_compute; reflexivity) HFR1' HG1 HFb HGb)
    as [HFRb HGRb].
  destruct (tail_glue (pin12 SM1n) msb msc ltac:(vm_compute; reflexivity) HFRb HGRb HFc HGc)
    as [HFRc HGRc].
  rewrite wvb_collapse, wvb_collapse.
  pose proof arms_converge as (AC1 & AC2 & AC3 & AC4 & AC5 & AC6).
  exact (ecall_and_tail SM3 msc _ AC1 AC2 AC4 AC6 HSc HFRc HGRc (ex_intro _ matc eq_refl)).
Qed.
End call.

Theorem mnr_holds : mnr_contract MNR_STK.
Proof.
intros W regs mem md size. cbn zeta.
intros Harg Hpos Hpal Hra Hcells Hroom Hwf Hbud Hsp16 Hslo Hshi Hpres Htakes.
destruct Hcells as (HPG & HPS & HCG & (f & HFBf & HFBl) & HML).
assert (Hf2 : f mod 2 = 0).
{ replace 1 with (Z.ones 1) in HFBl by reflexivity. rewrite Z.land_ones in HFBl by lia.
  change (2 ^ 1) with 2 in HFBl. exact HFBl. }
assert (HFBr : 0 <= f mod 256 < 256) by (apply Z.mod_pos_bound; lia).
assert (Hmm : (f mod 256) mod 2 = f mod 2).
{ pose proof (Z.div_mod f 256 ltac:(lia)) as D.
  replace f with (f mod 256 + (128 * (f / 256)) * 2) at 2 by lia.
  rewrite Z_mod_plus_full. reflexivity. }
assert (HFBl' : Z.land (f mod 256) 1 = 0).
{ replace 1 with (Z.ones 1) by reflexivity. rewrite Z.land_ones by lia. change (2 ^ 1) with 2.
  rewrite Hmm. exact Hf2. }
assert (HFB' : val_mem tfibsegs (mrestrict (w_H W) mem) (MNR_CF + 0x104) 1 (f mod 256)).
{ assert (HL : forall k, le_byte (f mod 256) 1 k = le_byte f 1 k).
  { intros k. unfold le_byte. f_equal. f_equal.
    change (2 ^ (8 * Z.of_nat 1)) with 256. apply Zmod_mod. }
  intros k Hk. rewrite HL. exact (HFBf k Hk). }
exact (mnr_walk W regs mem md size (f mod 256) Harg Hpos Hpal Hra HPG HPS HCG HFB' HFBr HFBl' HML
         Hroom Hwf Hbud Hsp16 Hslo Hshi Hpres Htakes).
Qed.
End walk.

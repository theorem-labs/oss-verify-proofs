(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BW_0Gc.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FMapPositive.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BImage BZBridge BSysStep BSFModel BellsX BArr BacX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BothAllocModel.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BllocWf.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Section HCW.
  Context {HCEIL : HeapCeil}.

Definition AINST       : Z := 0x18d9d8.
Definition AFLAGS      : Z := 0x18e838.
Definition ACFLAGS     : Z := 0x222b68.
Definition ASHBASE_CELL: Z := 0x191038.
Definition AHIGHMEMEND : Z := 0x191d20.
Definition AMIDBEG     : Z := 0x191d28.
Definition AMIDEND     : Z := 0x191d30.
Definition ACANPOISON  : Z := 0x19089c.
Definition AINITED     : Z := 0x191d18.
Definition ACTXSIZE    : Z := 0x191d3c.
Definition ATSDINIT    : Z := 0x1908a0.
Definition AALLOCFLAGS : Z := 0x2132a0.
Definition AIAINIT     : Z := 0x220ac8.
Definition AIAINST     : Z := 0x192240.
Definition AHOOKS      : Z := 0x222b00.
Definition ADYING      : Z := 0x222b5c.
Definition APAGESZ     : Z := 0x220ae0.
Definition AREALMEMSET : Z := 0x187148.
Definition ASECNAME    : Z := 0x187180.
Definition APRIMNAME   : Z := 0x187190.
Definition ATP         : Z := 0x6c5858.
Definition ATLSSLOT    : Z := 0x6c5800.
Definition ATSD        : Z := 0x6e6d10.
Definition ALSANDIS    : Z := 0x6c5868.
Definition AGOT2       : Z := 0x185d00.

Definition AGOT_LO     : Z := 0x185080.
Definition AGOT_VALS   : list Z :=
  [0x220ae0; 0x187180; 0x222b68; 0x18e838; 0x191038; 0x191d28; 0x191d30; 0x191d20; 0x187148; 0x187140; 0x187178; 0x187190; 1; 0x222b5c; 0x220ad8].
Definition AMEMSET     : Z := 0x176ea4.

Definition AGOT_FLAGS : Z := 0x185098.  Definition AGOT_SHBASE : Z := 0x1850a0. Definition AGOT_MIDBEG : Z := 0x1850a8.
Definition AGOT_MIDEND : Z := 0x1850b0. Definition AGOT_HIGHEND : Z := 0x1850b8. Definition AGOT_MEMSET : Z := 0x1850c0.
Definition AGOT_CFLAGS : Z := 0x185090. Definition AGOT_PAGESZ : Z := 0x185080. Definition AGOT_TOTALMMAP : Z := 0x1850d8.
Definition AGOT_SEALED : Z := 0x1850e0. Definition AGOT_DYING : Z := 0x1850e8.

Definition OI_SPACEBEG := 32.   Definition OI_RELEASEMS := 40.  Definition OI_REGIONINFO := 48. Definition OI_PREMAPPED := 56.
Definition OI_PAGESIZE := 64.   Definition OI_CHUNKS := 72.     Definition OI_PTRBASE := 80.    Definition OI_PTRSIZE := 88.
Definition OI_NRESERVED := 112. Definition OI_NCHUNKS := 120.   Definition OI_SORTED := 128.    Definition OI_SECMUTEX := 680.
Definition OI_GSTATS := 688.    Definition OI_Q := 728.         Definition OI_QMAX := 792.       Definition OI_QMIN := 800.
Definition OI_QCACHE := 808.    Definition OI_QMUTEX := 880.    Definition OI_GQ := 888.         Definition OI_FBMUTEX := 984.
Definition OI_MAXUSER := 3616.  Definition OI_MINRZ := 3624.    Definition OI_MISMATCH := 3628.

Definition OT_CTX := 0.   Definition OT_STACKTOP := 8.  Definition OT_STACKBOT := 16. Definition OT_SWITCHING := 40.
Definition OT_TQ := 80.   Definition OT_CACHE := 208.   Definition OT_STATS := 2800.   Definition OT_UNWINDING := 3168.
Definition PCLASS_SIZE := 80. Definition CACHE_STATS := 2560.
Definition AFS_SIZE : Z := 0xb09000.
Definition REGIONINFO_SIZE := 128.

Record ast := mkAst {
  a_st  : astate;
  a_thr : Z;
  a_ctx : Z;
  a_fsb : Z;
  a_L   : list (word * word);
  a_S   : list (word * word);
  a_Zr  : list (word * word);
  a_AL  : Z;
  a_top : Z;
  a_bot : Z
}.

Definition a_sb (s : ast) : Z := as_space_beg (a_st s).
Definition a_pa (s : ast) : Z := as_ptr_array (a_st s).
Definition a_ri (s : ast) : Z := a_sb s + kSpaceSize.
Definition a_cache (s : ast) : Z := a_thr s + OT_CACHE.
Definition RB (s : ast) (c : Z) : Z := region_beg (a_st s) c.
Definition FA (s : ast) (c : Z) : Z := free_array_base (a_st s) c.

Definition wlist (l : list Z) : list word := map wz l.
Definition zbool (b : bool) : Z := if b then 1 else 0.

Definition junk (m : mem) (lo n : Z) : Prop := 0 < n -> stk asegs m lo (lo + n).

Definition alow1 (X k : Z) : Prop := 4096 <= X /\ X + k <= AIMG_LO.
Definition akobj (X k : Z) : Prop := alow1 X k \/ aapp X k.

Lemma aapp_of_akobj_big : forall X k, akobj X k -> 0xF000 < k -> aapp X k.
Proof. intros X k [H|H] Hk; [| exact H]. exfalso. unfold alow1, AIMG_LO in H. lia. Qed.
Lemma akobj_sub : forall X k X' k', akobj X k -> X <= X' -> X' + k' <= X + k -> akobj X' k'.
Proof.
  intros X k X' k' [H|H] L1 L2.
  - left. unfold alow1 in *. lia.
  - right. eapply aapp_sub; [exact H| exact L1| exact L2].
Qed.

Lemma akobj_env : forall X k, akobj X k -> 0 <= k -> 4096 <= X /\ X + k <= aceil.
Proof. intros X k [H|H] Hk; acb; unfold alow1, aapp, aapp_lo, aapp_hi, AIMG_LO, AIMG_TOP, ALOWSH_LO, AHI_LO in *; lia. Qed.
Lemma aapp_env : forall X k, aapp X k -> 0 <= k -> 7241728 <= X /\ X + k <= aceil.
Proof. intros X k H Hk; acb; unfold aapp, aapp_lo, aapp_hi, AIMG_TOP, ALOWSH_LO, AHI_LO in *; lia. Qed.
Lemma aapp_sh_env : forall X k, aapp X k -> 0 <= k ->
  2148356096 <= sh X /\ sh X + nsh k <= sh aceil /\ sh aceil <= 17594332446720.
Proof.
  intros X k H Hk. pose proof (sh_aapp_range X k H Hk) as (A & B & C). acb.
  unfold sh, AIMG_TOP, ASHADOW_BASE in *. Z.div_mod_to_equations. lia.
Qed.
Lemma aapp_sh_env_div : forall X k, aapp X k -> 0 <= k ->
  2148356096 <= sh X /\ sh X + k / 8 <= sh aceil /\ sh aceil <= 17594332446720.
Proof. intros X k H Hk. pose proof (aapp_sh_env X k H Hk). unfold nsh in *. Z.div_mod_to_equations. lia. Qed.

Lemma akobj_lit : forall X k, akobj X k ->
  X + k <= 65536 \/ (7241728 <= X /\ X + k <= 2147446784) \/ 17594333495296 <= X.
Proof. intros X k [H|[H|H]]; unfold alow1, aapp_lo, aapp_hi, AIMG_LO, AIMG_TOP, ALOWSH_LO, AHI_LO in *; lia. Qed.
Lemma aapp_lit : forall X k, aapp X k -> X + k <= 2147446784 \/ 17594333495296 <= X.
Proof. intros X k [H|H]; unfold aapp_lo, aapp_hi, AIMG_TOP, ALOWSH_LO, AHI_LO in *; lia. Qed.
Lemma aapp_sh_lit : forall X k, aapp X k -> 0 <= k -> sh X + nsh k <= 2415881728 \/ 2201439137792 <= sh X.
Proof.
  intros X k [H|H] Hk.
  - left. exact (proj2 (sh_aapp_lo_range X k H Hk)).
  - right. exact (proj1 (sh_aapp_hi_range X k H Hk)).
Qed.
Lemma aapp_sh_lit_div : forall X k, aapp X k -> 0 <= k -> sh X + k / 8 <= 2415881728 \/ 2201439137792 <= sh X.
Proof. intros X k H Hk. pose proof (aapp_sh_lit X k H Hk). unfold nsh in *. Z.div_mod_to_equations. lia. Qed.

Lemma akobj_intro_sep : forall X k, 4096 <= X -> X + k <= aceil ->
  (X + k <= AIMG_LO \/ AIMG_TOP <= X) -> (X + k <= ALOWSH_LO \/ AHI_LO <= X) -> akobj X k.
Proof.
  intros X k G2 G3 G4 G5. unfold akobj, alow1, aapp, aapp_lo, aapp_hi, AIMG_LO, AIMG_TOP, ALOWSH_LO, AHI_LO in *. lia.
Qed.

Section Rep.
  Variable s : ast.
  Let st := a_st s.
  Let SB := a_sb s.
  Let T := a_thr s.

  Definition inst_rep (m : mem) : Prop :=
       rw_cells asegs m (AINST + OI_SPACEBEG)
         [C8 (wz SB); C4 (wz 0xffffffff)  ; C4 (wz 0)  ;
          C8 (wz (a_ri s)); C8 (wz 0)  ;
          C8 (wz 4096)  ; C8 (wz (a_pa s))  ; C8 (wz (a_pa s))  ;
          C8 (wz kPtrArrayReserve)  ]
    /\ junk m (AINST + 96) 16
    /\ rw_cells asegs m (AINST + OI_NRESERVED) [C8 (wz (as_n_reserved st)); C8 (wz (zlen (as_sec st))); C8 (wz 0)  ]
    /\ junk m (AINST + 136) (OI_SECMUTEX - 136)
    /\ rw_cells asegs m (AINST + OI_SECMUTEX) [C8 (wz 0)]
    /\ junk m (AINST + OI_GSTATS) (OI_Q - OI_GSTATS)
    /\ junk m (AINST + OI_Q) (OI_QMAX - OI_Q)
    /\ rw_cells asegs m (AINST + OI_QMAX) [C8 (wz (as_qmax st)); C8 (wz (as_qmin st)); C8 (wz (as_qcache st))]
    /\ junk m (AINST + 816) (OI_QMUTEX - 816)
    /\ rw_cells asegs m (AINST + OI_QMUTEX) [C8 (wz 0)]
    /\ rw_cells asegs m (AINST + OI_GQ)
         [C8 (wz (zlen (qc_list (as_gq st)))); C8 (wz (hd 0 (map qb_addr (qc_list (as_gq st)))));
          C8 (wz (last (map qb_addr (qc_list (as_gq st))) 0)); C8 (wz (qc_bytes (as_gq st)))]
    /\ junk m (AINST + 920) (OI_FBMUTEX - 920)
    /\ rw_cells asegs m (AINST + OI_FBMUTEX) [C8 (wz 0)]
    /\ junk m (AINST + 992) (OI_MAXUSER - 992)
    /\ rw_cells asegs m (AINST + OI_MAXUSER) [C8 (wz (2^40)); C2 (wz 16); C2 (wz 2048); C1 (b8 1); CB 3 [b8 0; b8 0; b8 0]].

  Definition flags_rep (m : mem) : Prop :=
       rw_cells asegs m (AFLAGS + 44) [C4 (wz 4096); C4 (wz 0); C4 (wz 0xbe)]
    /\ rw_cells asegs m (AFLAGS + 78) [C1 (b8 1)]
    /\ rw_cells asegs m (AFLAGS + 85) [C1 (b8 1)]
    /\ rw_cells asegs m (AFLAGS + 88) [C1 (b8 1)]
    /\ rw_cells asegs m (ACFLAGS + 34) [C1 (b8 1)]
    /\ rw_cells asegs m (ACFLAGS + 120) [C8 (wz 0xffffffffffffffff)]
    /\ rw_cells asegs m (ACFLAGS + 144) [C8 (wz 0)]
    /\ rw_cells asegs m (ACFLAGS + 260) [C1 (b8 0)]
    /\ rw_cells asegs m ASHBASE_CELL [C8 (wz ASHADOW_BASE)]
    /\ rw_cells asegs m AHIGHMEMEND [C8 (wz (2^47 - 1)); C8 (wz 0); C8 (wz 0)]
    /\ rw_cells asegs m ACANPOISON [C1 (b8 1)]
    /\ rw_cells asegs m AINITED [C1 (b8 1)]
    /\ rw_cells asegs m ACTXSIZE [C4 (wz 30)]
    /\ rw_cells asegs m ATSDINIT [C1 (b8 1); CB 3 [b8 0; b8 0; b8 0]; C4 (wz 0)]
    /\ rw_cells asegs m AALLOCFLAGS [C1 (b8 0); C1 (b8 1); C1 (b8 0)]
    /\ rw_cells asegs m AIAINIT [C1 (b8 (zbool (as_internal_init st))); C1 (b8 0); C2 (wz 0)]
    /\ rw_cells asegs m AHOOKS (repeat (C8 (wz 0)) 10)
    /\ rw_cells asegs m ADYING [C4 (wz 0)]
    /\ rw_cells asegs m AREALMEMSET [C8 (wz AMEMSET)]
    /\ rw_cells asegs m AGOT_LO (map (fun v => C8 (wz v)) AGOT_VALS)
    /\ rw_cells asegs m APAGESZ [C8 (wz 4096)]
    /\ rw_cells asegs m ASECNAME [C8 (wz 0x1ae42)]
    /\ rw_cells asegs m APRIMNAME [C8 (wz 0x23106)]

    /\ rw_cells asegs m ATLSSLOT [C8 (wz ATSD)] /\ rw_cells asegs m ATSD [C8 (wz (a_ctx s))]
    /\ rw_cells asegs m ALSANDIS [C4 (wz 0)] /\ rw_cells asegs m AGOT2 [C8 (wz 0x10)].

  Definition region_rep (m : mem) (c : Z) : Prop :=
    let r := get_region st c in
       rw_cells asegs m (a_ri s + REGIONINFO_SIZE * c)
         [C8 (wz 0)  ; C4 (wz 0); C4 (wz 0)  ;
          C8 (wz (rg_num_freed r)); C8 (wz (rg_mapped_free_array r)); C8 (wz (rg_allocated_user r)); C8 (wz 0);
          C8 (wz (rg_mapped_user r)); C8 (wz 0)]
    /\ junk m (a_ri s + REGIONINFO_SIZE * c + 64) 4
    /\ rw_cells asegs m (a_ri s + REGIONINFO_SIZE * c + 68) [C1 (b8 0)]
    /\ junk m (a_ri s + REGIONINFO_SIZE * c + 69) 59
    /\ u32arr asegs m (FA s c) (wlist (rev (rg_free_array r)))
    /\ junk m (FA s c + 4 * rg_num_freed r) (rg_mapped_free_array r - 4 * rg_num_freed r)
    /\ junk m (RB s c + rg_allocated_user r) (rg_mapped_user r - rg_allocated_user r).

  Definition pclass_rep (m : mem) (c : Z) : Prop :=
    let pc := get_pc st c in
    let A := a_cache s + PCLASS_SIZE * c in
       rw_cells asegs m A [C4 (wz (pc_count pc));
                          C4 (wz (if as_cache_inited st && negb (c =? 0) then max_count c else 0))]
    /\ rw_cells asegs m (A + 8) [C8 (wz (if as_cache_inited st && negb (c =? 0) then class_size c else 0))]
    /\ u32arr asegs m (A + 16) (wlist (rev (pc_chunks pc)))
    /\ junk m (A + 16 + 4 * pc_count pc) (64 - 4 * pc_count pc).

  Definition thread_rep (m : mem) : Prop :=
       rw_cells asegs m T [C8 (wz (a_ctx s))] /\ rw_cells asegs m (a_ctx s + 8) [C4 (wz 0)]
    /\ rw_cells asegs m (a_ctx s + 152) [C8 (wz T)]
    /\ rw_cells asegs m (T + 8) [C8 (wz (a_top s)); C8 (wz (a_bot s))]
    /\ rw_cells asegs m (T + 40) [C1 (b8 0)]
    /\ rw_cells asegs m (T + OT_SWITCHING) [C1 (b8 0)]
    /\ rw_cells asegs m (T + OT_TQ)
         [C8 (wz (zlen (qc_list (as_tq st)))); C8 (wz (hd 0 (map qb_addr (qc_list (as_tq st)))));
          C8 (wz (last (map qb_addr (qc_list (as_tq st))) 0)); C8 (wz (qc_bytes (as_tq st)))]
    /\ junk m (T + OT_TQ + 32) (OT_CACHE - OT_TQ - 32)
    /\ junk m (a_cache s + CACHE_STATS) (OT_STATS - OT_CACHE - CACHE_STATS)
    /\ junk m (T + OT_STATS) (OT_UNWINDING - OT_STATS)
    /\ rw_cells asegs m (T + OT_UNWINDING) [C1 (b8 0)].

  Definition sec_rep (m : mem) : Prop :=
       u64arr asegs m (a_pa s) (wlist (map sc_map_beg (as_sec st)))
    /\ junk m (a_pa s + 8 * zlen (as_sec st)) (8 * (as_n_reserved st - zlen (as_sec st)))
    /\ (forall i h, nth_error (as_sec st) i = Some h ->
           rw_cells asegs m (sc_map_beg h) [C8 (wz (sc_map_beg h)); C8 (wz (sc_map_size h)); C8 (wz (sc_size h)); C8 (wz (Z.of_nat i))]
        /\ junk m (sc_map_beg h + 32) (kPageSize - 32)).

  Definition ch_end (ch : chunk) : Z :=
    if ch_primary ch then ch_alloc_beg ch + class_size (ch_class ch)
    else ch_alloc_beg ch + round_up (rq_needed (compute_req (ch_used ch))) kPageSize.

  Definition chunk_rep (m : mem) (ch : chunk) : Prop :=
    let u := ch_user_beg ch in let n := ch_used ch in let mhdr := u - kChunkHeaderSize in
       (exists (b1 actx : Z), rw_cells asegs m mhdr
            [C1 (b8 (match ch_state ch with CAllocated => 2 | CQuarantine => 3 end));
             C1 (b8 b1); C2 (wz 0); C4 (wz n); C8 (wz actx)]
          /\ 0 <= b1 < 256 /\ b1 mod 128 = 0x11)
    /\ (ch_rz ch = 16 \/ (rw_cells asegs m (ch_alloc_beg ch) [C8 (wz 0xCC6E96B9CC6E96B9); C8 (wz mhdr)]
                          /\ junk m (ch_alloc_beg ch + 16) (ch_rz ch - 32)))
    /\ match ch_state ch with
       | CAllocated => wr_at asegs m u n /\ wr_at asegs m (sh u) (nsh n)
       | CQuarantine => junk m u n /\ poisoned m u (Z.to_nat (nsh n)) kAsanHeapFreeMagic
       end
    /\ junk m (u + n) (ch_end ch - (u + n))

    /\ poisoned m (ch_alloc_beg ch) (Z.to_nat (ch_rz ch / 8)) kAsanHeapLeftRedzoneMagic
    /\ poisoned m (u + round_up n 8) (Z.to_nat ((ch_end ch - (u + round_up n 8)) / 8)) kAsanHeapLeftRedzoneMagic

    /\ (if ch_primary ch then True else poisoned m (ch_alloc_beg ch - kPageSize) 512%nat kAsanHeapLeftRedzoneMagic).

  Definition region_shadow_rep (m : mem) (c : Z) : Prop :=
    let r := get_region st c in let pc := get_pc st c in let size := class_size c in
       (forall cp, In cp (rg_free_array r) -> poisoned m (compact_to_addr st c cp) (Z.to_nat (size / 8)) kAsanHeapLeftRedzoneMagic)
    /\ (forall cp, In cp (pc_chunks pc) -> poisoned m (compact_to_addr st c cp) (Z.to_nat (size / 8)) kAsanHeapLeftRedzoneMagic)
    /\ poisoned m (RB s c + rg_allocated_user r) (Z.to_nat ((rg_mapped_user r - rg_allocated_user r) / 8)) kAsanHeapLeftRedzoneMagic
    /\ poisoned m (FA s c) (Z.to_nat (rg_mapped_free_array r / 8)) kAsanHeapLeftRedzoneMagic.

  Definition region_junk_rep (m : mem) (c : Z) : Prop :=
    let r := get_region st c in let pc := get_pc st c in let size := class_size c in
       (forall cp, In cp (rg_free_array r) -> junk m (compact_to_addr st c cp) size)
    /\ (forall cp, In cp (pc_chunks pc) -> junk m (compact_to_addr st c cp) size).

  Definition batch_rep (m : mem) (b : qbatch) (nx : Z) : Prop :=
       rw_cells asegs m (qb_addr b) [C8 (wz nx); C8 (wz (qb_size b)); C8 (wz (qb_count b))]
    /\ u64arr asegs m (qb_addr b + 24) (wlist (qb_chunks b))
    /\ junk m (qb_addr b + 24 + 8 * qb_count b) (kBatchSize - 24 - 8 * qb_count b)
    /\ poisoned m (qb_addr b) (Z.to_nat (kBatchSize / 8)) kAsanHeapLeftRedzoneMagic.

  Fixpoint batches_rep (m : mem) (l : list qbatch) : Prop :=
    match l with
    | [] => True
    | b :: r => batch_rep m b (hd 0 (map qb_addr r)) /\ batches_rep m r
    end.

  Definition ia_rep (m : mem) : Prop :=
    if as_internal_init st
    then u8arr asegs m AIAINST (repeat (b8 0) (Z.to_nat 0x40dc0))
         /\ rw_cells asegs m (AIAINST + 0x40dc0) [C8 (wz 4096); C8 (wz (AIAINST + 0x40dd0))]
         /\ u8arr asegs m (AIAINST + 0x40dd0) (repeat (b8 0) (Z.to_nat (0x81030 - 0x40dd0)))
    else u8arr asegs m AIAINST (repeat (b8 0) (Z.to_nat 0x81030)).

  Definition disj (a n b k : Z) : Prop := a + n <= b \/ b + k <= a.

  Definition placed_ok : Prop :=
       SB mod 0x10000 = 0 /\ AHI_LO <= SB /\ SB + kSpaceSize + kPageSize <= aceil
    /\ a_pa s mod kPageSize = 0 /\ aapp (a_pa s) kPtrArrayReserve /\ a_pa s + kPtrArrayReserve <= aceil
    /\ T mod kPageSize = 0 /\ akobj T kPageSize /\ T + kPageSize <= aceil
    /\ a_ctx s mod 8 = 0 /\ aapp (a_ctx s) 160 /\ a_ctx s + 160 <= aceil
    /\ disj SB (kSpaceSize + kPageSize) (a_pa s) kPtrArrayReserve
    /\ disj SB (kSpaceSize + kPageSize) T kPageSize /\ disj SB (kSpaceSize + kPageSize) (a_ctx s) 160
    /\ disj (a_pa s) kPtrArrayReserve T kPageSize /\ disj (a_pa s) kPtrArrayReserve (a_ctx s) 160
    /\ aapp (a_fsb s) AFS_SIZE /\ a_fsb s + AFS_SIZE <= aceil
    /\ disj SB (kSpaceSize + kPageSize) (a_fsb s) AFS_SIZE /\ disj (a_pa s) kPtrArrayReserve (a_fsb s) AFS_SIZE
    /\ disj T kPageSize (a_fsb s) AFS_SIZE /\ disj (a_ctx s) 160 (a_fsb s) AFS_SIZE
    /\ (forall sc, In sc (as_sec st) ->
           sc_map_beg sc mod kPageSize = 0 /\ aapp (sc_map_beg sc) (sc_map_size sc) /\ sc_map_beg sc + sc_map_size sc <= aceil
        /\ 2 * kPageSize <= sc_map_size sc
        /\ disj (sc_map_beg sc) (sc_map_size sc) SB (kSpaceSize + kPageSize)
        /\ disj (sc_map_beg sc) (sc_map_size sc) (a_pa s) kPtrArrayReserve
        /\ disj (sc_map_beg sc) (sc_map_size sc) T kPageSize
        /\ disj (sc_map_beg sc) (sc_map_size sc) (a_ctx s) 160
        /\ disj (sc_map_beg sc) (sc_map_size sc) (a_fsb s) AFS_SIZE)
    /\ (forall sc sc', In sc (as_sec st) -> In sc' (as_sec st) -> sc_map_beg sc <> sc_map_beg sc' ->
           disj (sc_map_beg sc) (sc_map_size sc) (sc_map_beg sc') (sc_map_size sc'))
    /\ (disj T kPageSize (a_ctx s) 160 /\ kPageSize <= a_top s <= 2^47 /\ 0 <= a_bot s < a_top s).

  Definition ast_ok : Prop := placed_ok /\ WF st.

  Definition AREP (m : mem) : Prop :=
       ast_ok
    /\ inst_rep m /\ flags_rep m /\ thread_rep m /\ sec_rep m /\ ia_rep m
    /\ (forall c, 0 <= c < kNumClasses -> region_rep m c /\ pclass_rep m c /\ region_shadow_rep m c /\ region_junk_rep m c)
    /\ (forall ch, In ch (chunk_list st) -> chunk_rep m ch)
    /\ batches_rep m (qc_list (as_tq st)) /\ batches_rep m (qc_list (as_gq st)).

  Inductive afoot (a : Z) : Prop :=
  | af_inst   : AINST <= a < AINST + OI_MISMATCH + 4 -> afoot a
  | af_flags  : (AFLAGS + 44 <= a < AFLAGS + 89) \/ (ACFLAGS + 34 <= a < ACFLAGS + 261) \/ (ASHBASE_CELL <= a < ASHBASE_CELL + 8)
                \/ (AHIGHMEMEND <= a < AHIGHMEMEND + 24) \/ (ACANPOISON <= a < ACANPOISON + 1) \/ (AINITED <= a < AINITED + 1)
                \/ (ACTXSIZE <= a < ACTXSIZE + 4) \/ (ATSDINIT <= a < ATSDINIT + 8) \/ (AALLOCFLAGS <= a < AALLOCFLAGS + 3)
                \/ (AIAINIT <= a < AIAINIT + 4) \/ (AHOOKS <= a < AHOOKS + 80) \/ (ADYING <= a < ADYING + 4)
                \/ (AREALMEMSET <= a < AREALMEMSET + 8) \/ (AIAINST <= a < AIAINST + 0x81030)
                \/ (AGOT_LO <= a < AGOT_LO + 120) \/ (APAGESZ <= a < APAGESZ + 8) \/ (ASECNAME <= a < ASECNAME + 8)
                \/ (APRIMNAME <= a < APRIMNAME + 8) \/ (ATLSSLOT <= a < ATLSSLOT + 8) \/ (ATSD <= a < ATSD + 8)
                \/ (ALSANDIS <= a < ALSANDIS + 4) \/ (AGOT2 <= a < AGOT2 + 8) -> afoot a
  | af_thread : (T <= a < T + OT_UNWINDING + 1) \/ (a_ctx s + 8 <= a < a_ctx s + 12) \/ (a_ctx s + 152 <= a < a_ctx s + 160) -> afoot a
  | af_rinfo  : a_ri s <= a < a_ri s + kPageSize -> afoot a
  | af_farray : forall c, 0 <= c < kNumClasses -> FA s c <= a < FA s c + rg_mapped_free_array (get_region st c) -> afoot a
  | af_tail   : forall c, 0 <= c < kNumClasses ->
                RB s c + rg_allocated_user (get_region st c) <= a < RB s c + rg_mapped_user (get_region st c) -> afoot a
  | af_freech : forall c cp, 0 <= c < kNumClasses -> In cp (rg_free_array (get_region st c)) \/ In cp (pc_chunks (get_pc st c)) ->
                compact_to_addr st c cp <= a < compact_to_addr st c cp + class_size c -> afoot a
  | af_ptrarr : a_pa s <= a < a_pa s + 8 * as_n_reserved st -> afoot a
  | af_sechdr : forall h, In h (as_sec st) -> sc_map_beg h <= a < sc_map_beg h + kPageSize -> afoot a
  | af_chleft : forall ch, In ch (chunk_list st) -> ch_alloc_beg ch <= a < ch_user_beg ch -> afoot a
  | af_chright: forall ch, In ch (chunk_list st) -> ch_user_beg ch + ch_used ch <= a < ch_end ch -> afoot a
  | af_chquar : forall ch, In ch (chunk_list st) -> ch_state ch = CQuarantine -> ch_user_beg ch <= a < ch_user_beg ch + ch_used ch -> afoot a
  | af_batch  : forall b, In b (qc_list (as_tq st) ++ qc_list (as_gq st)) -> qb_addr b <= a < qb_addr b + kBatchSize -> afoot a

  | af_sh_farray : forall c, 0 <= c < kNumClasses -> sh (FA s c) <= a < sh (FA s c) + rg_mapped_free_array (get_region st c) / 8 -> afoot a
  | af_sh_tail   : forall c, 0 <= c < kNumClasses ->
                   sh (RB s c + rg_allocated_user (get_region st c)) <= a < sh (RB s c + rg_allocated_user (get_region st c)) + (rg_mapped_user (get_region st c) - rg_allocated_user (get_region st c)) / 8 -> afoot a
  | af_sh_freech : forall c cp, 0 <= c < kNumClasses -> In cp (rg_free_array (get_region st c)) \/ In cp (pc_chunks (get_pc st c)) ->
                   sh (compact_to_addr st c cp) <= a < sh (compact_to_addr st c cp) + class_size c / 8 -> afoot a
  | af_sh_chleft : forall ch, In ch (chunk_list st) -> sh (ch_alloc_beg ch) <= a < sh (ch_alloc_beg ch) + ch_rz ch / 8 -> afoot a
  | af_sh_chright: forall ch, In ch (chunk_list st) ->
                   sh (ch_user_beg ch + round_up (ch_used ch) 8) <= a < sh (ch_user_beg ch + round_up (ch_used ch) 8) + (ch_end ch - (ch_user_beg ch + round_up (ch_used ch) 8)) / 8 -> afoot a
  | af_sh_chquar : forall ch, In ch (chunk_list st) -> ch_state ch = CQuarantine ->
                   sh (ch_user_beg ch) <= a < sh (ch_user_beg ch) + nsh (ch_used ch) -> afoot a
  | af_sh_sechdr : forall ch, In ch (chunk_list st) -> ch_primary ch = false ->
                   sh (ch_alloc_beg ch - kPageSize) <= a < sh (ch_alloc_beg ch - kPageSize) + 512 -> afoot a
  | af_sh_batch  : forall b, In b (qc_list (as_tq st) ++ qc_list (as_gq st)) -> sh (qb_addr b) <= a < sh (qb_addr b) + kBatchSize / 8 -> afoot a.

  Definition awin_ok (W : list ivl) : Prop :=
    Forall (fun iv : ivl => forall a, fst iv <= a < snd iv -> ~ afoot a) W.

End Rep.

Definition agree_on (P : Z -> Prop) (m m' : mem) : Prop :=
  forall x, P x -> 0 <= x < 2^64 -> m' (wa x) = m (wa x).

Lemma awin_agree : forall s W m m',
  awin_ok s W -> munch W m m' -> agree_on (afoot s) m m'.
Proof.
  intros s W m m' AW MU x Hx Hr. apply MU. rewrite wa_unsigned by lia.
  clear MU. revert AW. induction W as [|[lo hi] W IH]; intros AW; [exact I|]. cbn. split.
  - intros Hin. exact (Forall_inv AW x Hin Hx).
  - apply IH. exact (Forall_inv_tail AW).
Qed.

Section Transport.
  Variable P : Z -> Prop.
  Variables m m' : mem.
  Hypothesis AG : agree_on P m m'.
  Hypothesis WM : wmono asegs m m'.

  Lemma bytes_at_transport_pt : forall A bs,
    bytes_at asegs m A bs -> (forall a, A <= a < A + Z.of_nat (length bs) -> P a) -> bytes_at asegs m' A bs.
  Proof.
    intros A bs (Ha & Hl & H) HR. split; [lia|]. split; [lia|].
    intros i Hi. unfold mrd. rewrite AG; [apply H; exact Hi| apply HR; lia| lia].
  Qed.
  Lemma stk_transport_pt : forall lo hi,
    stk asegs m lo hi -> (forall a, lo <= a < hi -> P a) -> stk asegs m' lo hi.
  Proof.
    intros lo hi (H1 & H2 & H) HR. split; [lia|]. split; [lia|]. intros a Ha.
    destruct (H a Ha) as [Hw (b & Hb)]. split; [apply WM; exact Hw|]. exists b.
    unfold mrd in *. rewrite AG; [exact Hb| apply HR; lia| lia].
  Qed.
  Lemma junk_transport_pt : forall lo n,
    junk m lo n -> (forall a, lo <= a < lo + n -> P a) -> junk m' lo n.
  Proof. intros lo n J HR Hn. eapply stk_transport_pt; [apply J; exact Hn| exact HR]. Qed.
  Lemma rw_cells_transport_pt : forall A cs,
    rw_cells asegs m A cs -> (forall a, A <= a < A + Z.of_nat (cells_size cs) -> P a) -> rw_cells asegs m' A cs.
  Proof.
    intros A cs [[Hwf Hb] Hw] HR. split; [split; [exact Hwf|]| eapply wr_at_transport; eauto].
    eapply bytes_at_transport_pt; [exact Hb|]. rewrite cells_bytes_length by assumption. exact HR.
  Qed.
  Lemma u32arr_transport_pt : forall A ws,
    u32arr asegs m A ws -> (forall a, A <= a < A + 4 * Z.of_nat (length ws) -> P a) -> u32arr asegs m' A ws.
  Proof.
    intros A ws [Hb Hw] HR. split; [| eapply wr_at_transport; eauto].
    eapply bytes_at_transport_pt; [exact Hb|]. rewrite u32s_length, Nat2Z.inj_mul. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. intros a Ha. apply HR. lia.
  Qed.
  Lemma u8arr_transport_pt : forall A bs,
    u8arr asegs m A bs -> (forall a, A <= a < A + Z.of_nat (length bs) -> P a) -> u8arr asegs m' A bs.
  Proof.
    intros A bs [Hb Hw] HR. split; [| eapply wr_at_transport; eauto].
    eapply bytes_at_transport_pt; [exact Hb| exact HR].
  Qed.
  Lemma u64arr_transport_pt : forall A ws,
    u64arr asegs m A ws -> (forall a, A <= a < A + 8 * Z.of_nat (length ws) -> P a) -> u64arr asegs m' A ws.
  Proof.
    intros A ws [Hb Hw] HR. split; [| eapply wr_at_transport; eauto].
    eapply bytes_at_transport_pt; [exact Hb|]. rewrite u64s_length, Nat2Z.inj_mul. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. intros a Ha. apply HR. lia.
  Qed.
  Lemma SHAD_transport_pt : forall A sbs,
    SHAD m A sbs -> (forall a, sh A <= a < sh A + Z.of_nat (length sbs) -> P a) -> SHAD m' A sbs.
  Proof.
    intros A sbs (A0 & HA & [Hb Hw]) HR. split; [exact A0|]. split; [exact HA|].
    split; [eapply bytes_at_transport_pt; eauto| eapply wr_at_transport; eauto].
  Qed.
  Lemma poisoned_transport_pt : forall A k v,
    poisoned m A k v -> (forall a, sh A <= a < sh A + Z.of_nat k -> P a) -> poisoned m' A k v.
  Proof.
    intros A k v H HR. eapply SHAD_transport_pt; [exact H|]. unfold poison_bytes. rewrite repeat_length. exact HR.
  Qed.
End Transport.

End HCW.

Ltac aunf := try acb; unfold akobj, alow1, aapp, aapp_lo, aapp_hi, AIMG_LO, AIMG_TOP, ALOWSH_LO, AHI_LO in *.

Ltac af_tac := intros ? ?; solve [ econstructor; eauto; cbn -[Z.add Z.mul Z.sub Z.div] in *; unfold OI_MISMATCH, OT_UNWINDING, kNumClasses, kPageSize, kBatchSize in *; lia ].

Section HCW2.
  Context {HCEIL : HeapCeil}.

Lemma batches_rep_transport : forall P m m' l,
  agree_on P m m' -> wmono asegs m m' ->
  (forall b a, In b l -> (qb_addr b <= a < qb_addr b + kBatchSize \/ sh (qb_addr b) <= a < sh (qb_addr b) + kBatchSize / 8) -> P a) ->
  (forall b, In b l -> 0 <= qb_count b /\ 24 + 8 * qb_count b <= kBatchSize /\ qb_count b = zlen (qb_chunks b)) ->
  batches_rep m l -> batches_rep m' l.
Proof.
  intros P m m' l AG WM HP HC. induction l as [|b l IH]; [exact (fun x => x)|].
  cbn [batches_rep hd map]. intros (HB & HR). split; [| apply IH; [intros; eapply HP; [right; eassumption| eassumption] | intros; apply HC; right; assumption | exact HR]].
  destruct HB as (B1 & B2 & B3 & B4). pose proof (HC b (or_introl eq_refl)) as (C1 & C2 & C3).
  unfold zlen in C3. unfold kBatchSize in *.
  split; [|split; [|split]].
  - eapply (rw_cells_transport_pt P m m' AG WM); [exact B1|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. intros a Ha. eapply HP; [left; reflexivity| left; lia].
  - eapply (u64arr_transport_pt P m m' AG WM); [exact B2|]. unfold wlist. rewrite length_map. intros a Ha. eapply HP; [left; reflexivity| left; lia].
  - eapply (junk_transport_pt P m m' AG WM); [exact B3|]. intros a Ha. unfold kBatchSize in Ha. eapply HP; [left; reflexivity| left; lia].
  - eapply (poisoned_transport_pt P m m' AG WM); [exact B4|]. intros a Ha. unfold kBatchSize in Ha. eapply HP; [left; reflexivity| ]. right.
    change (Z.of_nat (Z.to_nat (8192 / 8))) with 1024 in Ha. change (8192 / 8) with 1024. lia.
Qed.

Section Frame.
  Variable s : ast.
  Variables m m' : mem.

  Variable P : Z -> Prop.
  Hypothesis AG : agree_on P m m'.
  Hypothesis WM : wmono asegs m m'.

  Ltac tr_cells H := eapply (rw_cells_transport_pt P m m' AG WM); [exact H|];
                     cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ length repeat].
  Ltac tr_junk H := eapply (junk_transport_pt P m m' AG WM); [exact H|].
  Ltac tr_u32 H := eapply (u32arr_transport_pt P m m' AG WM); [exact H|]; unfold wlist; rewrite ?length_map, ?length_rev.
  Ltac tr_u64 H := eapply (u64arr_transport_pt P m m' AG WM); [exact H|]; unfold wlist; rewrite ?length_map, ?length_rev.
  Ltac tr_poi H := eapply (poisoned_transport_pt P m m' AG WM); [exact H|].
  Ltac af C := intros ? ?; eapply C; eauto; unfold OI_MISMATCH, OT_UNWINDING, OI_SPACEBEG, OI_NRESERVED, OI_SECMUTEX, OI_GSTATS, OI_Q, OI_QMAX,
               OI_QMUTEX, OI_GQ, OI_FBMUTEX, OI_MAXUSER, OT_SWITCHING, OT_TQ, OT_CACHE, OT_STATS, CACHE_STATS, PCLASS_SIZE, REGIONINFO_SIZE,
               kNumClasses, kPageSize, kBatchSize, kSpaceSize, kPtrArrayReserve in *; try lia.

  Lemma inst_rep_frame : (forall a, AINST <= a < AINST + OI_MISMATCH + 4 -> P a) -> inst_rep s m -> inst_rep s m'.
  Proof.
    intros HP H. destruct H as (A1 & J1 & A2 & J2 & A3 & J3 & J4 & A5 & J5 & A6 & A7 & J6 & A8 & J7 & A9).
    split; [tr_cells A1; af HP|].
    split; [tr_junk J1; af HP|].
    split; [tr_cells A2; af HP|].
    split; [tr_junk J2; af HP|].
    split; [tr_cells A3; af HP|].
    split; [tr_junk J3; af HP|].
    split; [tr_junk J4; af HP|].
    split; [tr_cells A5; af HP|].
    split; [tr_junk J5; af HP|].
    split; [tr_cells A6; af HP|].
    split; [tr_cells A7; af HP|].
    split; [tr_junk J6; af HP|].
    split; [tr_cells A8; af HP|].
    split; [tr_junk J7; af HP|].
    tr_cells A9; af HP.
  Qed.

  Ltac pick n := lazymatch n with O => left | S ?k => right; pick k end.

  Definition aflags_range (a : Z) : Prop :=
    (AFLAGS + 44 <= a < AFLAGS + 89) \/ (ACFLAGS + 34 <= a < ACFLAGS + 261) \/ (ASHBASE_CELL <= a < ASHBASE_CELL + 8)
    \/ (AHIGHMEMEND <= a < AHIGHMEMEND + 24) \/ (ACANPOISON <= a < ACANPOISON + 1) \/ (AINITED <= a < AINITED + 1)
    \/ (ACTXSIZE <= a < ACTXSIZE + 4) \/ (ATSDINIT <= a < ATSDINIT + 8) \/ (AALLOCFLAGS <= a < AALLOCFLAGS + 3)
    \/ (AIAINIT <= a < AIAINIT + 4) \/ (AHOOKS <= a < AHOOKS + 80) \/ (ADYING <= a < ADYING + 4)
    \/ (AREALMEMSET <= a < AREALMEMSET + 8) \/ (AIAINST <= a < AIAINST + 0x81030)
    \/ (AGOT_LO <= a < AGOT_LO + 120) \/ (APAGESZ <= a < APAGESZ + 8) \/ (ASECNAME <= a < ASECNAME + 8)
    \/ (APRIMNAME <= a < APRIMNAME + 8) \/ (ATLSSLOT <= a < ATLSSLOT + 8) \/ (ATSD <= a < ATSD + 8)
    \/ (ALSANDIS <= a < ALSANDIS + 4) \/ (AGOT2 <= a < AGOT2 + 8).

  Ltac trf HP H n := tr_cells H; intros ? ?; eapply HP; unfold aflags_range; pick n;
                  unfold AFLAGS, ACFLAGS, ASHBASE_CELL, AHIGHMEMEND, ACANPOISON, AINITED, ACTXSIZE, ATSDINIT, AALLOCFLAGS, AIAINIT, AHOOKS,
                         ADYING, AREALMEMSET, AIAINST, AGOT_LO, APAGESZ, ASECNAME, APRIMNAME, ATLSSLOT, ATSD, ALSANDIS, AGOT2 in *; lia.
  Lemma flags_rep_frame : (forall a, aflags_range a -> P a) -> flags_rep s m -> flags_rep s m'.
  Proof.
    intros HP H. destruct H as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16 & F17 & F18 & F19 & F20 & F21 & F22 & F23 & F24 & F25 & F26 & F27).
    unfold flags_rep.
    split; [trf HP F1 0%nat|]. split; [trf HP F2 0%nat|]. split; [trf HP F3 0%nat|]. split; [trf HP F4 0%nat|].
    split; [trf HP F5 1%nat|]. split; [trf HP F6 1%nat|]. split; [trf HP F7 1%nat|]. split; [trf HP F8 1%nat|].
    split; [trf HP F9 2%nat|]. split; [trf HP F10 3%nat|]. split; [trf HP F11 4%nat|]. split; [trf HP F12 5%nat|]. split; [trf HP F13 6%nat|]. split; [trf HP F14 7%nat|].
    split; [trf HP F15 8%nat|]. split; [trf HP F16 9%nat|]. split; [trf HP F17 10%nat|]. split; [trf HP F18 11%nat|]. split; [trf HP F19 12%nat|].
    split; [eapply (rw_cells_transport_pt P m m' AG WM); [exact F20|]; change (Z.of_nat _) with 120;
           intros ? ?; eapply HP; unfold aflags_range; pick 14%nat; unfold AGOT_LO in *; lia|].
    split; [trf HP F21 15%nat|]. split; [trf HP F22 16%nat|].
    split; [tr_cells F23; intros ? ?; eapply HP; unfold aflags_range; pick 17%nat; unfold APRIMNAME in *; lia|].
    split; [tr_cells F24; intros ? ?; eapply HP; unfold aflags_range; pick 18%nat; unfold ATLSSLOT in *; lia|].
    split; [tr_cells F25; intros ? ?; eapply HP; unfold aflags_range; pick 19%nat; unfold ATSD in *; lia|].
    split; [tr_cells F26; intros ? ?; eapply HP; unfold aflags_range; pick 20%nat; unfold ALSANDIS in *; lia|].
    tr_cells F27; intros ? ?; eapply HP; unfold aflags_range; do 21 right; unfold AGOT2 in *; lia.
  Qed.

  Hypothesis OK : ast_ok s.
  Let W : WF (a_st s).
  Proof. exact (proj2 OK). Qed.

  Definition athread_range (a : Z) : Prop :=
    (a_thr s <= a < a_thr s + OT_UNWINDING + 1) \/ (a_ctx s + 8 <= a < a_ctx s + 12) \/ (a_ctx s + 152 <= a < a_ctx s + 160).
  Lemma thread_rep_frame : (forall a, athread_range a -> P a) -> thread_rep s m -> thread_rep s m'.
  Proof.
    intros HP H. unfold athread_range in HP. destruct H as (T1 & T2 & T2b & T2c & T2d & T3 & T4 & J1 & J2 & J3 & T5). unfold thread_rep.
    split; [tr_cells T1; af HP|].
    split; [tr_cells T2; af HP|].
    split; [tr_cells T2b; af HP|].
    split; [tr_cells T2c; af HP|].
    split; [tr_cells T2d; af HP|].
    split; [tr_cells T3; af HP|].
    split; [tr_cells T4; af HP|].
    split; [tr_junk J1; af HP|].
    split; [tr_junk J2; unfold a_cache; af HP|].
    split; [tr_junk J3; af HP|].
    tr_cells T5; af HP.
  Qed.

  Lemma region_rep_frame : forall c, 0 <= c < kNumClasses ->
    (forall a, a_ri s <= a < a_ri s + kPageSize -> P a) ->
    (forall a, FA s c <= a < FA s c + rg_mapped_free_array (get_region (a_st s) c) -> P a) ->
    (forall a, RB s c + rg_allocated_user (get_region (a_st s) c) <= a < RB s c + rg_mapped_user (get_region (a_st s) c) -> P a) ->
    region_rep s m c -> region_rep s m' c.
  Proof.
    intros c Hc HP1 HP2 HP3 H. pose proof (WF_region _ c W Hc) as RO.
    destruct H as (R1 & J1 & R2 & J2 & U & J3 & J4). unfold region_rep.
    pose proof (ro_numfreed _ _ RO) as N1. pose proof (ro_fa_le _ _ RO) as N2. pose proof (ro_alloc_nonneg _ _ RO) as N3.
    pose proof (ro_alloc_le _ _ RO) as N4. unfold zlen in N1.
    split; [tr_cells R1; af HP1|].
    split; [tr_junk J1; af HP1|].
    split; [tr_cells R2; af HP1|].
    split; [tr_junk J2; af HP1|].
    split; [tr_u32 U; af HP2|].
    split; [tr_junk J3; af HP2|].
    tr_junk J4; af HP3.
  Qed.

  Lemma pclass_rep_frame : forall c, 0 <= c < kNumClasses ->
    (forall a, a_cache s + PCLASS_SIZE * c <= a < a_cache s + PCLASS_SIZE * c + PCLASS_SIZE -> P a) ->
    pclass_rep s m c -> pclass_rep s m' c.
  Proof.
    intros c Hc HP H. pose proof (WF_cache _ c W Hc) as CO.
    destruct H as (P1 & P2 & U & J). unfold pclass_rep.
    pose proof (co_count _ _ CO) as N1. unfold zlen in N1.
    assert (N2 : 0 <= pc_count (get_pc (a_st s) c) <= 16).
    { pose proof (co_bound _ _ CO) as B. pose proof (class_size_table_facts c Hc) as T.
      destruct (as_cache_inited (a_st s)); lia. }
    split; [tr_cells P1; af HP|].
    split; [tr_cells P2; af HP|].
    split; [tr_u32 U; af HP|].
    tr_junk J; af HP.
  Qed.

  Lemma sec_rep_frame :
    (forall a, a_pa s <= a < a_pa s + 8 * as_n_reserved (a_st s) -> P a) ->
    (forall h a, In h (as_sec (a_st s)) -> sc_map_beg h <= a < sc_map_beg h + kPageSize -> P a) ->
    sec_rep s m -> sec_rep s m'.
  Proof.
    intros HP1 HP2 (U & J & H). unfold sec_rep.
    destruct W as (_ & _ & _ & _ & Wn & _ & Wres & _).
    assert (N0 : 0 <= zlen (as_sec (a_st s))) by (unfold zlen; lia).
    split; [tr_u64 U; unfold zlen in *; af HP1|].
    split; [tr_junk J; unfold zlen in *; af HP1|].
    intros i h Hi. destruct (H i h Hi) as [C1 J1]. pose proof (nth_error_In _ _ Hi) as IN.
    split; [tr_cells C1; af HP2| tr_junk J1; af HP2].
  Qed.

  Lemma ia_rep_frame : (forall a, AIAINST <= a < AIAINST + 0x81030 -> P a) -> ia_rep s m -> ia_rep s m'.
  Proof.
    intros HP. unfold ia_rep. destruct (as_internal_init (a_st s)).
    - intros (C1 & C2 & C3).
      split; [eapply (u8arr_transport_pt P m m' AG WM); [exact C1|]; rewrite repeat_length, Z2Nat.id by lia;
             intros ? ?; eapply HP; unfold AIAINST in *; lia|].
      split; [tr_cells C2; intros ? ?; eapply HP; unfold AIAINST in *; lia|].
      eapply (u8arr_transport_pt P m m' AG WM); [exact C3|]. rewrite repeat_length, Z2Nat.id by lia.
      intros ? ?; eapply HP; unfold AIAINST in *; lia.
    - intros C. eapply (u8arr_transport_pt P m m' AG WM); [exact C|]. rewrite repeat_length, Z2Nat.id by lia.
      intros ? ?; eapply HP; lia.
  Qed.

  Lemma region_shadow_rep_frame : forall c, 0 <= c < kNumClasses ->
    (forall cp a, In cp (rg_free_array (get_region (a_st s) c)) \/ In cp (pc_chunks (get_pc (a_st s) c)) ->
                  sh (compact_to_addr (a_st s) c cp) <= a < sh (compact_to_addr (a_st s) c cp) + class_size c / 8 -> P a) ->
    (forall a, sh (RB s c + rg_allocated_user (get_region (a_st s) c)) <= a
               < sh (RB s c + rg_allocated_user (get_region (a_st s) c)) + (rg_mapped_user (get_region (a_st s) c) - rg_allocated_user (get_region (a_st s) c)) / 8 -> P a) ->
    (forall a, sh (FA s c) <= a < sh (FA s c) + rg_mapped_free_array (get_region (a_st s) c) / 8 -> P a) ->
    region_shadow_rep s m c -> region_shadow_rep s m' c.
  Proof.
    intros c Hc HP1 HP2 HP3 (H1 & H2 & H3 & H4). pose proof (WF_region _ c W Hc) as RO. pose proof (class_size_table_facts c Hc) as CS.
    pose proof (ro_alloc_nonneg _ _ RO). pose proof (ro_alloc_le _ _ RO). pose proof (ro_fa_le _ _ RO). pose proof (ro_numfreed _ _ RO).
    unfold zlen in *. unfold region_shadow_rep.
    split; [| split; [| split]].
    - intros cp Hin. specialize (H1 cp Hin). tr_poi H1. rewrite Z2Nat.id by (Z.div_mod_to_equations; lia). af (HP1 cp).
    - intros cp Hin. specialize (H2 cp Hin). tr_poi H2. rewrite Z2Nat.id by (Z.div_mod_to_equations; lia). af (HP1 cp).
    - tr_poi H3. rewrite Z2Nat.id by (Z.div_mod_to_equations; lia). af HP2.
    - tr_poi H4. rewrite Z2Nat.id by (Z.div_mod_to_equations; lia). af HP3.
  Qed.

  Lemma region_junk_rep_frame : forall c, 0 <= c < kNumClasses ->
    (forall cp a, In cp (rg_free_array (get_region (a_st s) c)) \/ In cp (pc_chunks (get_pc (a_st s) c)) ->
                  compact_to_addr (a_st s) c cp <= a < compact_to_addr (a_st s) c cp + class_size c -> P a) ->
    region_junk_rep s m c -> region_junk_rep s m' c.
  Proof.
    intros c Hc HP (H1 & H2). unfold region_junk_rep. split.
    - intros cp Hin. specialize (H1 cp Hin). tr_junk H1. af (HP cp).
    - intros cp Hin. specialize (H2 cp Hin). tr_junk H2. af (HP cp).
  Qed.

  Definition achunk_range (ch : chunk) (a : Z) : Prop :=
       (ch_alloc_beg ch <= a < ch_user_beg ch)
    \/ (ch_user_beg ch + ch_used ch <= a < ch_end ch)
    \/ (ch_state ch = CQuarantine /\ ch_user_beg ch <= a < ch_user_beg ch + ch_used ch)
    \/ (sh (ch_alloc_beg ch) <= a < sh (ch_alloc_beg ch) + ch_rz ch / 8)
    \/ (sh (ch_user_beg ch + round_up (ch_used ch) 8) <= a < sh (ch_user_beg ch + round_up (ch_used ch) 8) + (ch_end ch - (ch_user_beg ch + round_up (ch_used ch) 8)) / 8)
    \/ (ch_state ch = CQuarantine /\ sh (ch_user_beg ch) <= a < sh (ch_user_beg ch) + nsh (ch_used ch))
    \/ (ch_primary ch = false /\ sh (ch_alloc_beg ch - kPageSize) <= a < sh (ch_alloc_beg ch - kPageSize) + 512).
  Lemma chunk_rep_frame : forall ch, In ch (chunk_list (a_st s)) -> (forall a, achunk_range ch a -> P a) -> chunk_rep m ch -> chunk_rep m' ch.
  Proof.
    intros ch Hin HP H. pose proof (WF_chunk _ ch W Hin) as CO. unfold achunk_range in HP.
    destruct CO as (U1 & U2 & U3 & U4 & _).
    pose proof (rz_size_facts (ch_used ch)) as RZ. rewrite <- (eq_refl : rq_rz (compute_req (ch_used ch)) = rz_size (ch_used ch)) in RZ.
    rewrite <- U3 in RZ. destruct RZ as (RZ1 & RZ2 & _).
    destruct H as ((b1 & actx & HD & Hb1 & Hb1') & LC & ST & JR & PL & PR & PH). unfold chunk_rep.
    assert (NS : 0 <= nsh (ch_used ch) /\ 8 * nsh (ch_used ch) = round_up (ch_used ch) 8 /\ ch_used ch <= round_up (ch_used ch) 8 < ch_used ch + 8).
    { unfold nsh, round_up. Z.div_mod_to_equations. lia. }
    split.
    { exists b1, actx. split; [|split; [exact Hb1| exact Hb1']]. tr_cells HD. unfold kChunkHeaderSize. intros ? ?; eapply HP; left; lia. }
    split.
    { destruct LC as [LC|[LC1 LC2]]; [left; exact LC| right]. split; [tr_cells LC1; intros ? ?; eapply HP; left; lia| tr_junk LC2; intros ? ?; eapply HP; left; lia]. }
    split.
    { destruct (ch_state ch) eqn:E.
      - destruct ST as [ST1 ST2]. split; eapply wr_at_transport; eauto.
      - destruct ST as [ST1 ST2]. split; [tr_junk ST1; intros ? ?; eapply HP; do 2 right; left; split; [first [exact E | reflexivity]| lia]
                                          | tr_poi ST2; rewrite Z2Nat.id by lia; intros ? ?; eapply HP; do 5 right; left; split; [first [exact E | reflexivity]| lia]]. }
    split; [tr_junk JR; intros ? ?; eapply HP; right; left; lia|].
    split; [tr_poi PL; rewrite Z2Nat.id by (Z.div_mod_to_equations; lia); intros ? ?; eapply HP; do 3 right; left; lia|].
    split.
    { tr_poi PR. destruct (Z.le_gt_cases 0 ((ch_end ch - (ch_user_beg ch + round_up (ch_used ch) 8)) / 8)).
      - rewrite Z2Nat.id by lia. intros ? ?; eapply HP; do 4 right; left; lia.
      - rewrite (Z2Nat.nonpos _) by lia. intros a Ha. cbn in Ha. lia. }
    destruct (ch_primary ch) eqn:E; [exact I|]. tr_poi PH. intros ? ?; eapply HP. do 6 right. split; [reflexivity| lia].
  Qed.
End Frame.

Theorem AREP_frame_pt : forall s m m',
  AREP s m -> agree_on (afoot s) m m' -> wmono asegs m m' -> AREP s m'.
Proof.
  intros s m m' H AG WM.
  destruct H as (OK & I & F & T & SC & IA & RC & CH & BT & BG).
  assert (W : WF (a_st s)) by exact (proj2 OK).
  split; [exact OK|].
  split; [apply (inst_rep_frame s m m' _ AG WM (af_inst s) I)|].
  split; [apply (flags_rep_frame s m m' _ AG WM (af_flags s) F)|].
  split; [apply (thread_rep_frame s m m' _ AG WM (af_thread s) T)|].
  split; [apply (sec_rep_frame s m m' _ AG WM OK (af_ptrarr s) (fun h a Hh Ha => af_sechdr s a h Hh Ha) SC)|].
  split; [apply (ia_rep_frame s m m' _ AG WM); [intros a Ha; eapply af_flags; do 13 right; left; exact Ha| exact IA]|].
  split.
  { intros c Hc. destruct (RC c Hc) as (R1 & R2 & R3 & R4).
    split; [apply (region_rep_frame s m m' _ AG WM OK c Hc (af_rinfo s) (fun a Ha => af_farray s a c Hc Ha) (fun a Ha => af_tail s a c Hc Ha) R1)|].
    split.
    { apply (pclass_rep_frame s m m' _ AG WM OK c Hc); [| exact R2]. intros a Ha. apply af_thread. left.
      unfold a_cache, OT_CACHE, PCLASS_SIZE, OT_UNWINDING, kNumClasses in *. lia. }
    split; [apply (region_shadow_rep_frame s m m' _ AG WM OK c Hc (fun cp a Hin Ha => af_sh_freech s a c cp Hc Hin Ha) (fun a Ha => af_sh_tail s a c Hc Ha) (fun a Ha => af_sh_farray s a c Hc Ha) R3)
          | apply (region_junk_rep_frame s m m' _ AG WM c Hc (fun cp a Hin Ha => af_freech s a c cp Hc Hin Ha) R4)]. }
  split.
  { intros ch Hin. apply (chunk_rep_frame s m m' _ AG WM OK ch Hin); [| exact (CH ch Hin)].
    intros a Ha. destruct Ha as [Ha|[Ha|[[Q Ha]|[Ha|[Ha|[[Q Ha]|[NP Ha]]]]]]].
    - eapply af_chleft; eauto. - eapply af_chright; eauto. - eapply af_chquar; eauto. - eapply af_sh_chleft; eauto.
    - eapply af_sh_chright; eauto. - eapply af_sh_chquar; eauto. - eapply af_sh_sechdr; eauto. }
  assert (BOK : forall b, In b (qc_list (as_tq (a_st s)) ++ qc_list (as_gq (a_st s))) ->
            0 <= qb_count b /\ 24 + 8 * qb_count b <= kBatchSize /\ qb_count b = zlen (qb_chunks b)).
  { intros b Hb. pose proof (WF_batch _ b W Hb) as (B1 & B2 & _). unfold kBatchSize, kBatchCount in *. lia. }
  split.
  - eapply (batches_rep_transport (afoot s) m m'); [exact AG| exact WM| | | exact BT].
    + intros b a Hb Hr. destruct Hr as [Hr|Hr]; [eapply af_batch| eapply af_sh_batch]; eauto; apply in_app_iff; left; exact Hb.
    + intros b Hb. apply BOK. apply in_app_iff. left. exact Hb.
  - eapply (batches_rep_transport (afoot s) m m'); [exact AG| exact WM| | | exact BG].
    + intros b a Hb Hr. destruct Hr as [Hr|Hr]; [eapply af_batch| eapply af_sh_batch]; eauto; apply in_app_iff; right; exact Hb.
    + intros b Hb. apply BOK. apply in_app_iff. right. exact Hb.
Qed.

Theorem AREP_frame : forall s W m m',
  AREP s m -> munch W m m' -> wmono asegs m m' -> awin_ok s W -> AREP s m'.
Proof. intros s W m m' H MU WM AW. eapply AREP_frame_pt; [exact H| eapply awin_agree; eauto| exact WM]. Qed.

Definition is_alloc (ch : chunk) : bool := match ch_state ch with CAllocated => true | _ => false end.
Definition alb (s : ast) : list (Z * Z) :=
  map (fun ch => (ch_user_beg ch, ch_used ch)) (List.filter is_alloc (chunk_list (a_st s))).

Definition ARHEAP (s : ast) (LB : list (Z * Z)) (m : mem) : Prop :=
  AREP s m /\ List.NoDup LB /\ (forall b, In b LB <-> In b (alb s)).

Definition arblock_range (A n : Z) : Prop :=
  AIMG_TOP <= A /\ A mod 16 = 0 /\ 1 <= n /\ A + n <= aceil /\ aapp A n.

Definition astatic (a : Z) : Prop :=
  AINST <= a < AINST + OI_MISMATCH + 4 \/ AFLAGS <= a < AFLAGS + 96 \/ ACFLAGS <= a < ACFLAGS + 300
  \/ ASHBASE_CELL <= a < ASHBASE_CELL + 8 \/ AHIGHMEMEND <= a < AHIGHMEMEND + 24 \/ ACANPOISON <= a < ACANPOISON + 16
  \/ AINITED <= a < AINITED + 40 \/ AALLOCFLAGS <= a < AALLOCFLAGS + 3 \/ AIAINIT <= a < AIAINIT + 4
  \/ AHOOKS <= a < AHOOKS + 96 \/ AREALMEMSET <= a < AREALMEMSET + 8 \/ AIAINST <= a < AIAINST + 0x81030
  \/ AGOT_LO <= a < AGOT_LO + 120 \/ APAGESZ <= a < APAGESZ + 8 \/ ASECNAME <= a < ASECNAME + 8 \/ APRIMNAME <= a < APRIMNAME + 8
  \/ ATLSSLOT <= a < ATLSSLOT + 8 \/ ATSD <= a < ATSD + 8 \/ ALSANDIS <= a < ALSANDIS + 4 \/ AGOT2 <= a < AGOT2 + 8.

Definition aclient_write_ok (s : ast) (LB : list (Z * Z)) (iv : ivl) : Prop :=
     aceil <= fst iv
  \/ (exists b, In b LB /\ fst b <= fst iv /\ snd iv <= fst b + snd b)
  \/ (exists b, In b LB /\ sh (fst b) <= fst iv /\ snd iv <= sh (fst b) + nsh (snd b))
  \/ (ARW_LO <= fst iv /\ snd iv <= AIMG_TOP /\ forall a, fst iv <= a < snd iv -> ~ astatic a)
  \/ (forall a, fst iv <= a < snd iv -> ~ afoot s a).

Definition ARHEAP_block_range_stmt : Prop :=
  forall s LB m A n, ARHEAP s LB m -> In (A, n) LB -> arblock_range A n.
Definition ARHEAP_blocks_disjoint_stmt : Prop :=
  forall s LB m A1 n1 A2 n2, ARHEAP s LB m -> In (A1, n1) LB -> In (A2, n2) LB -> A1 <> A2 ->
    A1 + round_up n1 8 + 16 <= A2 \/ A2 + round_up n2 8 + 16 <= A1.
Definition stack_not_afoot_stmt : Prop :=
  forall s m a, AREP s m -> aceil <= a -> ~ afoot s a.
Definition block_not_afoot_stmt : Prop :=
  forall s LB m A n a, ARHEAP s LB m -> In (A, n) LB -> A <= a < A + n -> ~ afoot s a.
Definition block_shadow_not_afoot_stmt : Prop :=
  forall s LB m A n a, ARHEAP s LB m -> In (A, n) LB -> sh A <= a < sh A + nsh n -> ~ afoot s a.
Definition image_not_afoot_stmt : Prop :=
  forall s m a, AREP s m -> ARW_LO <= a < AIMG_TOP -> ~ astatic a -> ~ afoot s a.
Definition ARHEAP_frame_stmt : Prop :=
  forall s LB m m' W, ARHEAP s LB m -> munch W m m' -> wmono asegs m m' -> Forall (aclient_write_ok s LB) W -> ARHEAP s LB m'.

End HCW2.

From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BazyRestrict BazyLedger BazySR.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BllocBudget.

Section HCW3.
  Context {HCEIL : HeapCeil}.

Definition amaps_in_ledger (s : ast) (mo : Model) : Prop :=
  let h := m_vmmaps mo in let st := a_st s in

     (forall mp, In mp (as_maps st) -> mp_kind mp <> MkRegionInfo -> (forall c, mp_kind mp <> MkUserMap c /\ mp_kind mp <> MkFreeArrayMap c) ->
        mp_kind mp <> MkPtrArrayCommit -> mp_kind mp <> MkShadowRemap ->
        In (Z_to_bv 64 (mp_base mp), Z_to_bv 64 (mp_size mp)) (vm_maps h) /\ 0 <= mp_base mp < 2^64)
  /\
     (forall mp, In mp (as_maps st) ->
        (mp_kind mp = MkRegionInfo \/ (exists c, mp_kind mp = MkUserMap c \/ mp_kind mp = MkFreeArrayMap c) \/ mp_kind mp = MkPtrArrayCommit) ->
        forall x : word, mp_base mp <= bv_unsigned x < mp_base mp + mp_size mp ->
          in_rangesb x (vm_noaccess h) = false /\ in_rangesb x (a_L s) = false)
  /\
     (forall sc x, In sc (as_sec st) -> sc_map_beg sc <= bv_unsigned x < sc_map_beg sc + sc_map_size sc -> in_rangesb x (a_L s) = false)
  /\ nooverlap (vm_maps h) /\ entries_nowrap (vm_maps h) /\ entries_nowrap (vm_noaccess h).

Definition ashadow_visible (s : ast) : Prop :=
  let st := a_st s in
     (forall c x, 0 <= c < kNumClasses ->
        sh (RB s c) <= bv_unsigned x < sh (RB s c) + rg_mapped_user (get_region st c) / 8 -> in_rangesb x (a_S s) = true)
  /\ (forall sc x, In sc (as_sec st) ->
        sh (sc_map_beg sc) <= bv_unsigned x < sh (sc_map_beg sc) + sc_map_size sc / 8 -> in_rangesb x (a_S s) = true).

Definition aPhi (s : ast) : Z := B_PRIM - pusage (a_st s).

Lemma aPhi_regions : forall s s', as_regions (a_st s') = as_regions (a_st s) -> aPhi s' = aPhi s.
Proof. intros s s' E. unfold aPhi. rewrite (pusage_regions (a_st s') (a_st s) E). reflexivity. Qed.

Definition ABUDGET (s : ast) (mo : Model) : Prop :=
  0 <= a_AL s /\ eager_used mo + pages_total (a_S s) * page_size + aPhi s + a_AL s <= vm_limit (m_vmmaps mo).

Definition AMODEL (s : ast) (mo : Model) : Prop := amaps_in_ledger s mo /\ ashadow_visible s /\ ABUDGET s mo.

Lemma AMODEL_mat : forall s mo mo', AMODEL s mo -> same_but_materialized mo mo' -> AMODEL s mo'.
Proof.
  intros s mo mo' (A & V & B) SB.
  pose proof (same_but_materialized_fields mo mo' SB) as (Ffd & Fmaps & Flazy & _).
  split; [| split; [exact V|]].
  - unfold amaps_in_ledger in *. rewrite Fmaps. exact A.
  - destruct B as [B0 B1]. split; [exact B0|]. unfold eager_used in *. rewrite Fmaps, Flazy. exact B1.
Qed.

End HCW3.


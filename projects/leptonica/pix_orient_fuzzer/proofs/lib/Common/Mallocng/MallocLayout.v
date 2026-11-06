(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec Hoare.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_MallocLayout () := "C47Corelib7Classes?RelationClasses9ReflexiveI47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes6option00C4ELinuxProcessSemantics?LinuxProcessSem<MemImageType8seg_baseC56Stdlib6ZArith6BinInt1Z4of_NC56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z3addC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType8seg_sizeC47Corelib4Init9Datatypes4andbK47Corelib4Init9Datatypes6option01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<find_segmentK47Corelib4Init5Logic2eq01I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes4bool00c69OSSVerify5KrLib6Common8Mallocng<MallocLayout:seg_missesC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option02I47Corelib4Init5Logic2eq00K47Corelib4Init9Datatypes4list01C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic9False_indC47Corelib4Init5Logic7f_equalC56Stdlib6ZArith6BinInt1Z9leb_spec0C56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init9Datatypes7reflect00C56Stdlib6ZArith4Znat3N2Z9is_nonnegK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K47Corelib7Numbers7BinNums8positive02K46Stdlib9micromega7EnvRing5PExpr03K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega5Tauto8GFormula03C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic2or00C47Corelib4Init5Logic3notC47Corelib4Init5Logic8eq_ind_rc69OSSVerify5KrLib6Common8Mallocng<MallocLayoutAfind_segment_consC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes8list_indI47Corelib5Lists7ListDef6Forall00K47Corelib4Init9Datatypes4list02K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib4Init5Logic4True00I47Corelib4Init5Logic5False00K47Corelib4Init5Logic4True01K47Corelib4Init9Datatypes4bool01K47Corelib7Numbers7BinNums1Z01I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib7Numbers7BinNums8positive03K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init9Datatypes4bool02C56Stdlib6ZArith6BinInt1Z6leb_leC47Corelib4Init5Logic5proj2C47Corelib4Init9Datatypes3appK47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C45stdpp9bitvector;definitions;bv_unsignedK47Corelib7Numbers7BinNums1Z02C4ELinuxProcessSemantics?LinuxProcessSem<MemImageType<seg_readableC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType9seg_bytesC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z4to_NC56Stdlib6NArith6BinNat1N6to_natC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsBsegment_read_bytesK47Corelib4Init9Datatypes3nat02C59OSSVerify5KrLib6Common8PropExec7seg_romC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01c69OSSVerify5KrLib6Common8Mallocng<MallocLayout>seg_rom_unfoldC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics?segment_byte_atC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType<seg_writableC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewC56Stdlib6ZArith6BinInt1Z6of_natc69OSSVerify5KrLib6Common8Mallocng<MallocLayout4ZseqC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00C47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses7rew_iffK46Stdlib9micromega7EnvRing5PExpr01C56Stdlib6ZArith6BinInt1Z6eq_decI47Corelib4Init6Specif7sumbool00K47Corelib4Init5Logic2or01C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega5Tauto8GFormula07K47Corelib4Init5Logic2or02C47Corelib4Init9Datatypes7nat_indC46Stdlib5Lists4List2InC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega5Tauto8GFormula05I47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith4Znat5Nat2Z8inj_succC46Stdlib9micromega8ZifyInst7Inj_Z_ZK46Stdlib9micromega=RingMicromega3Op201c69OSSVerify5KrLib6Common8Mallocng<MallocLayout9chk_rangeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulC47Corelib4Init5Logic3iffC47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib5Lists4List>forallb_forallC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z6moduloC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega7EnvRing5PExpr04C56Stdlib6ZArith6BinInt1Z7div_posK46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1ZBdiv_lt_upper_boundK47Corelib4Init5Logic3and01C46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02c69OSSVerify5KrLib6Common8Mallocng<MallocLayout7Zseq_InC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses6eq_iffC46Stdlib9micromega;ZifyClasses;rew_iff_revC46Stdlib5Lists4List7forallbK46Stdlib9micromega:ZMicromega;ZArithProof01c69OSSVerify5KrLib6Common8Mallocng<MallocLayout8chk_listC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common8Mallocng<MallocLayout=chk_rom_bytesC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common8Mallocng<MallocLayout9rom_bytesC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvC56Stdlib6ZArith6BinInt1Z3eqbC47Corelib4Init9Datatypes9andb_propC56Stdlib6ZArith6BinInt1Z6eqb_eqC56Stdlib6ZArith6BinInt1Z9mod_smallC35stdpp7tactics<f_equal_helpC45stdpp9bitvector;definitionsCZ_to_bv_bv_unsigned".
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

Class MallocLayout := {
  (* [comment removed for export] *)
  ml_segs : list Segment;          (* [comment removed for export] *)
  IMG_LO : Z;                      (* [comment removed for export] *)
  RW_LO  : Z;                      (* [comment removed for export] *)
  IMG_HI : Z;                      (* [comment removed for export] *)

  (* [comment removed for export] *)
  A_LOCK : word;                   (* [comment removed for export] *)
  A_CTX : word;                    (* [comment removed for export] *)
  A_INIT_DONE : word;              (* [comment removed for export] *)
  A_MMAP_CTR : word;               (* [comment removed for export] *)
  A_FREE_META_HEAD : word;         (* [comment removed for export] *)
  A_AVAIL_META : word;             (* [comment removed for export] *)
  A_AVAIL_META_CNT : word;         (* [comment removed for export] *)
  A_AVAIL_AREA_CNT : word;         (* [comment removed for export] *)
  A_META_SHIFT : word;             (* [comment removed for export] *)
  A_AREA_HEAD : word;              (* [comment removed for export] *)
  A_AREA_TAIL : word;              (* [comment removed for export] *)
  A_AVAIL_AREAS : word;            (* [comment removed for export] *)
                                   (* [comment removed for export] *)
                                   (* [comment removed for export] *)
  Z_UNMAP_SEQ : Z;                 (* [comment removed for export] *)
  Z_BOUNCES : Z;                   (* [comment removed for export] *)
  A_SEQ : word;                    (* [comment removed for export] *)
  A_BRK : word;                    (* [comment removed for export] *)
  A_MALLOC_REPLACED : word;        (* [comment removed for export] *)

  (* [comment removed for export] *)
  A_LIBC : word;                   (* [comment removed for export] *)
  A_NEED_LOCKS : word;             (* [comment removed for export] *)
  A_PAGE_SIZE : word;              (* [comment removed for export] *)
  A_TP : word;                     (* [comment removed for export] *)
  A_ERRNO : word;                  (* [comment removed for export] *)
  A_GOT_SSP : word;                (* [comment removed for export] *)
  A_SSP : word;                    (* [comment removed for export] *)

  (* [comment removed for export] *)
  A_SIZE_CLASSES : word;           (* [comment removed for export] *)
  A_SMALL_CNT_TAB : word;          (* [comment removed for export] *)
  A_MED_CNT_TAB : word;            (* [comment removed for export] *)
  A_DEBRUIJN : word;               (* [comment removed for export] *)

  (* [comment removed for export] *)
  PC_MALLOC : word;                   (* [comment removed for export] *)
  PC_FREE : word;                     (* [comment removed for export] *)
  PC_CALLOC : word;
  PC_LIBC_FREE : word;                (* [comment removed for export] *)
  PC_MALLOC_IMPL : word;              (* [comment removed for export] *)
  PC_GET_META : word;
  PC_NTFREE : word;                   (* [comment removed for export] *)
  PC_ALLOC_META : word;               (* [comment removed for export] *)
  PC_ALLOC_SLOT : word;
  PC_ENFRAME : word;
  PC_ALLZEROP : word;                 (* [comment removed for export] *)
  PC_MMAP : word;                     (* [comment removed for export] *)
  PC_MPROTECT : word;                 (* [comment removed for export] *)
  PC_MUNMAP : word;                   (* [comment removed for export] *)
  PC_VM_WAIT : word;                  (* [comment removed for export] *)
  PC_SYSCALL_RET : word;              (* [comment removed for export] *)
  PC_ERRNO_LOC : word;                (* [comment removed for export] *)
  PC_LOCK : word;                     (* [comment removed for export] *)
  PC_UNLOCK : word;                   (* [comment removed for export] *)
  PC_MEMCPY : word;
  PC_MEMSET : word
}.

(* [comment removed for export] *)
Definition ml_rom {ML : MallocLayout} : word -> option byte := seg_rom ml_segs.

(* [comment removed for export] *)
Definition CTX_SIZE : Z := 928.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition size_classes_tab : list Z :=
  [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 12; 15; 18; 20; 25; 31; 36; 42; 50; 63;
   72; 84; 102; 127; 146; 170; 204; 255; 292; 340; 409; 511; 584; 682; 818;
   1023; 1169; 1364; 1637; 2047; 2340; 2730; 3276; 4095; 4680; 5460; 6552; 8191].
Definition size_class (i : Z) : Z := nth (Z.to_nat i) size_classes_tab 0.

Definition debruijn32_tab : list Z :=
  [0; 1; 28; 2; 29; 14; 24; 3; 30; 22; 20; 15; 25; 17; 4; 8;
   31; 27; 13; 23; 21; 19; 16; 7; 26; 12; 18; 6; 11; 5; 10; 9].
Definition debruijn (k : Z) : Z := nth (Z.to_nat k) debruijn32_tab 0.

Definition small_cnt_tab : list Z :=
  [30; 30; 30;  31; 15; 15;  20; 10; 10;  31; 15; 7;  25; 12; 6;
   21; 10; 5;  18; 8; 4;  31; 15; 7;  28; 14; 6].
Definition small_cnt (j : Z) : Z := nth (Z.to_nat j) small_cnt_tab 0.   (* [comment removed for export] *)

Definition med_cnt_tab : list Z := [28; 24; 20; 32].
Definition med_cnt (j : Z) : Z := nth (Z.to_nat j) med_cnt_tab 0.

(* [comment removed for export] *)
Fixpoint rom_bytes (rom : word -> option byte) (a : Z) (bs : list Z) : Prop :=
  match bs with
  | [] => True
  | b :: bs' => rom (Z_to_bv 64 a) = Some (Z_to_bv 8 b) /\ rom_bytes rom (a + 1) bs'
  end.

Class MallocLayoutOk (ML : MallocLayout) := {
  (* [comment removed for export] *)
  mlo_hull : 0 < IMG_LO /\ IMG_LO <= RW_LO /\ RW_LO <= IMG_HI /\ IMG_HI <= 2^32
             /\ IMG_LO mod 4096 = 0 /\ RW_LO mod 4096 = 0 /\ IMG_HI mod 4096 = 0;
  (* [comment removed for export] *)
  mlo_rom_out : forall a : word, (bv_unsigned a < IMG_LO \/ IMG_HI <= bv_unsigned a) -> seg_rom ml_segs a = None;
  mlo_wview_out : forall (m : word -> option byte) (a : word),
      (bv_unsigned a < IMG_LO \/ IMG_HI <= bv_unsigned a) -> wview ml_segs m a = m a;
  (* [comment removed for export] *)
  mlo_wview_ro : forall (m : word -> option byte) (a : word),
      IMG_LO <= bv_unsigned a < RW_LO -> wview ml_segs m a = m a;
  (* [comment removed for export] *)
  mlo_wview_rw : forall (m : word -> option byte) (a : word),
      RW_LO <= bv_unsigned a < IMG_HI -> wview ml_segs m a <> None;
  (* [comment removed for export] *)
  mlo_rom_in : forall a : word, IMG_LO <= bv_unsigned a < IMG_HI -> seg_rom ml_segs a <> None;

  (* [comment removed for export] *)
  mlo_reserved_in : forall b sz, In (b, sz) (segments_reserved ml_segs) ->
      IMG_LO <= bv_unsigned b /\ bv_unsigned b + bv_unsigned sz <= IMG_HI /\ 0 < bv_unsigned sz;
  mlo_reserved_cover : forall a : Z, IMG_LO <= a < IMG_HI ->
      exists b sz, In (b, sz) (segments_reserved ml_segs) /\ bv_unsigned b <= a < bv_unsigned b + bv_unsigned sz;
  mlo_reserved_top : reserved_top (segments_reserved ml_segs) = IMG_HI;

  (* [comment removed for export] *)
  mlo_ctx : bv_unsigned A_CTX = bv_unsigned A_LOCK + 8;
  mlo_init_done : bv_unsigned A_INIT_DONE = bv_unsigned A_CTX + 8;
  mlo_mmap_ctr : bv_unsigned A_MMAP_CTR = bv_unsigned A_CTX + 12;
  mlo_free_meta_head : bv_unsigned A_FREE_META_HEAD = bv_unsigned A_CTX + 16;
  mlo_avail_meta : bv_unsigned A_AVAIL_META = bv_unsigned A_CTX + 24;
  mlo_avail_meta_cnt : bv_unsigned A_AVAIL_META_CNT = bv_unsigned A_CTX + 32;
  mlo_avail_area_cnt : bv_unsigned A_AVAIL_AREA_CNT = bv_unsigned A_CTX + 40;
  mlo_meta_shift : bv_unsigned A_META_SHIFT = bv_unsigned A_CTX + 48;
  mlo_area_head : bv_unsigned A_AREA_HEAD = bv_unsigned A_CTX + 56;
  mlo_area_tail : bv_unsigned A_AREA_TAIL = bv_unsigned A_CTX + 64;
  mlo_avail_areas : bv_unsigned A_AVAIL_AREAS = bv_unsigned A_CTX + 72;
  mlo_unmap_seq : Z_UNMAP_SEQ = bv_unsigned A_CTX + 848;
  mlo_bounces : Z_BOUNCES = bv_unsigned A_CTX + 880;
  mlo_seq : bv_unsigned A_SEQ = bv_unsigned A_CTX + 912;
  mlo_brk : bv_unsigned A_BRK = bv_unsigned A_CTX + 920;
  mlo_ctx_align : bv_unsigned A_CTX mod 8 = 0;          (* [comment removed for export] *)
  (* [comment removed for export] *)
  mlo_need_locks : bv_unsigned A_NEED_LOCKS = bv_unsigned A_LIBC + 3;
  mlo_page_size : bv_unsigned A_PAGE_SIZE = bv_unsigned A_LIBC + 48;
  mlo_libc_align : bv_unsigned A_LIBC mod 8 = 0;
  (* [comment removed for export] *)
  mlo_errno : bv_unsigned A_ERRNO = bv_unsigned A_TP - 164;
  mlo_tp_align : bv_unsigned A_TP mod 8 = 0;
  mlo_ssp_align : bv_unsigned A_SSP mod 8 = 0;
  mlo_got_ssp_align : bv_unsigned A_GOT_SSP mod 8 = 0;
  (* [comment removed for export] *)
  mlo_order_got : RW_LO <= bv_unsigned A_GOT_SSP /\ bv_unsigned A_GOT_SSP + 8 <= bv_unsigned A_ERRNO;
  mlo_order_errno : bv_unsigned A_ERRNO + 4 <= bv_unsigned A_TP;
  mlo_order_tp : bv_unsigned A_TP <= bv_unsigned A_SSP;
  mlo_order_ssp : bv_unsigned A_SSP + 8 <= bv_unsigned A_LIBC;
  mlo_order_libc : bv_unsigned A_LIBC + 56 <= bv_unsigned A_LOCK;
  mlo_order_ctx : bv_unsigned A_CTX + CTX_SIZE <= bv_unsigned A_MALLOC_REPLACED;
  mlo_order_replaced : bv_unsigned A_MALLOC_REPLACED + 4 <= IMG_HI;
  (* [comment removed for export] *)
  mlo_got_ssp : rom_bytes (seg_rom ml_segs) (bv_unsigned A_GOT_SSP)
                  (map (fun i => (bv_unsigned A_SSP / 2^(8*i)) mod 256) [0;1;2;3;4;5;6;7]);
  (* [comment removed for export] *)
  mlo_ctx_zero : forall a : word, bv_unsigned A_LOCK <= bv_unsigned a < bv_unsigned A_MALLOC_REPLACED + 4 ->
                 seg_rom ml_segs a = Some (Z_to_bv 8 0);

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  mlo_tables_ro : (IMG_LO <= bv_unsigned A_DEBRUIJN /\ bv_unsigned A_DEBRUIJN + 32 <= RW_LO)
                  /\ (IMG_LO <= bv_unsigned A_SIZE_CLASSES /\ bv_unsigned A_SIZE_CLASSES + 96 <= RW_LO)
                  /\ (IMG_LO <= bv_unsigned A_SMALL_CNT_TAB /\ bv_unsigned A_SMALL_CNT_TAB + 27 <= RW_LO)
                  /\ (IMG_LO <= bv_unsigned A_MED_CNT_TAB /\ bv_unsigned A_MED_CNT_TAB + 4 <= RW_LO);
  mlo_size_classes_align : bv_unsigned A_SIZE_CLASSES mod 2 = 0;
  mlo_size_classes : rom_bytes (seg_rom ml_segs) (bv_unsigned A_SIZE_CLASSES)
                       (flat_map (fun c => [c mod 256; c / 256]) size_classes_tab);
  mlo_debruijn : rom_bytes (seg_rom ml_segs) (bv_unsigned A_DEBRUIJN) debruijn32_tab;
  mlo_small_cnt : rom_bytes (seg_rom ml_segs) (bv_unsigned A_SMALL_CNT_TAB) small_cnt_tab;
  mlo_med_cnt : rom_bytes (seg_rom ml_segs) (bv_unsigned A_MED_CNT_TAB) med_cnt_tab;

  (* [comment removed for export] *)
  mlo_pcs : Forall (fun pc : word => IMG_LO <= bv_unsigned pc < RW_LO /\ bv_unsigned pc mod 4 = 0)
              [PC_MALLOC; PC_FREE; PC_CALLOC; PC_LIBC_FREE; PC_MALLOC_IMPL; PC_GET_META; PC_NTFREE;
               PC_ALLOC_META; PC_ALLOC_SLOT; PC_ENFRAME; PC_ALLZEROP; PC_MMAP; PC_MPROTECT; PC_MUNMAP;
               PC_VM_WAIT; PC_SYSCALL_RET; PC_ERRNO_LOC; PC_LOCK; PC_UNLOCK; PC_MEMCPY; PC_MEMSET]
}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma find_segment_cons : forall s rest a n,
  find_segment (s :: rest) a n
  = if (Z.of_N (seg_base s) <=? a) && (a + n <=? Z.of_N (seg_base s) + Z.of_N (seg_size s))
    then Some s else find_segment rest a n.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocLayout ()) [] "h01ah11nh24resth31sp;1p;2p;3p-1p10000p4p710p9g000\j1:Tg001<j19Tg001^j14Tg002\j11Tg003:j22Tg003Wj20Tg0044j18Tg0052j25Tg005Pj26Tg0062j37Tg0076j23Tg007PR0%:0g008OR1%90R2g008mP2f3R2#4#1R3f1R4'2f0R5,04%82#1,03'2'51602f2?745n0100000020000'3X11W0W2W3o"). Qed.

Definition seg_misses (a n : Z) (s : Segment) : Prop :=
  a < Z.of_N (seg_base s) \/ Z.of_N (seg_base s) + Z.of_N (seg_size s) < a + n.

Lemma find_segment_none : forall segs a n,
  Forall (seg_misses a n) segs -> find_segment segs a n = None.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocLayout ()) [] "p'0h02H0h12H1h21li001lh35Hresth42Hsh51ah61bi011bh71eh81ni021nh91ri031rh:1Hh;4__p1h<4__x1h=4__x2h>4__x3h?4__x4h@2n0hA1si041shB4segshC2H2hD2IHhE7__arithhF4__ffhG8__varmaphH5__withI4cstrhJ5cstr0hK2l0hL2n1hM1ohN4resthO1xi051xp;1p;2p;3p;6p;4p;7p;5p;8g000\R0j1STg009Mj2<j3@Tg001<j1XTg0062j37Tg00:Yj1OTg00;;j30Tg00;Uj1LTg0076j2BTg003:j24Tg003Wj21Tg0052j23Tg00<5j6^Tg00<Qj2QTg00=0j6NTg00=Mj2MTg00>0j25Tg00>LR1j2KTg001^j1JTg00>oj1ITg002\j1;Tg0044j1ATg00?Rj2HTg00@0j1ZTg00@Nj4GTg00@lj1YTg00AJj1WTg00B5j2>Tg00BXj1FTg00C=j3ETg00C`j1VTg00DEj4?Tg00E0j7UTg00ETj6TTg00F8j2hTg00FZj2gTg00GFj3fTg00Gej4eTg00HWj2RTg00I3j2cTg00IMj1PTg00Ifj6CTg00JDj4]Tg00KWj5_Tg00L9R2j3\Tg00LZj3`Tg005Pj2aTg00M:j7[Tg00M^j8dTg007PR3f1R4f0R53\p=:A`345p=6%J5#;p=2%A5#;,14p=81a35p=9P4g00NBR6g00NaR7P7g00OAR8P5g00OaF[p==f3R9P6P7P7P8f2R:P4P5Gdp=D%A5#;p=b%S3R;P3g008OR<1<45R=/::%X3R>A79:4%O3R?30[^8<]5R@XB;%L3RA,:=1B>?W:X8<X5<f4RB/69RC,:=P>g008mR=P>f5RD#2RE/4:11:418ED'4'3%9DA7B:4n0100000020000A0>5?XM>P2P31<:4f7R2f6RE'6RF90;4P=P>f8RG#2RH/4D11DB18HG'4'3%9GA72DBn0100000020000=0>?RH[P516DBRI90;A16EDRJ90;AP;PAP0P3p-0RAP5g00PAg00P]RKn10110000020020000000X7;g00Q:PFP5E^PK1QH5b1W0P5O1W0A@G24f9RH/<G/:4169:f=RFf<RL'650;f>RM/6F90;CP;P;P0P3P;P5PDP5n10110000020020104100X7;PIf?RC/6MP5ENA0;BMP;P3P0P3P3P5P2P4n10110000020020104100X7;PJf@R0/6CP4ENA03E0fAR09032P5fBRC903GP3fCRMA0;HMRFA@C041<MCRNf;':P=P>fGRO#2RPfDRQ'4RR11QM18PO'4'3%9OfFRS?7QMn0100000020000=0>?]3]4[XA3A0;GCP5PFP;PQA@MCS1<QM/:4P=P>fHRM#2RFfERT'4RU11TQ18FM'4'3%9MA7OTQn0100000020000=0>?]3]4X2;A@C0T1:NT1MPQ15PQ/KRPUP=P1fIRU#2/5SP=P>11MORSfKRR#2/8RRQ'4RP,34%9RfJRT?7MOn0100000020000=0>?P4%2T/5ORO1MSQRN15SQ/KPRP11UMfLRM#2/8M'4RQP=P111TUfMRU#2/8U'5RSP=P>g00QVRC/34fOR0#9RFfNRV?7MRRWn0100000020000=0>?P411RT%2V/8V'5RTA0>F?%J0RX#Ig00R6RY%;X'5fP#ARX#I%;X,5Yg00RTRX#L%SXP<P<1H<BP:%Z<CGP41H<9CG%Y<%W<RXP<g00S@RZ,><R[%FZR\#F,><5E<R]g00SeR^1><\R\%VZ,><5E<RZC?,=X%O7R_PXP<P\P^P[C?,=XP_PXPXP6P7P7P8P<P[g00TLR[P\C?,=XP<PZP[P]C?,=XFUP_PXP6P7P7P8PEETCDCDCD1hX8P5P:1B=C1g5:=0=CdAf<Y4CebFbGbHX<<X=<X><X?<X;A1159114:'515:41R:9119B11:D'R'cP2[[[^<<^=<^><^?<^;AP5PKPVfRRV#b%2VP0P9P2PLO8bEbJbI'QP=P>13CCPFPWn0100000020000=0>?eWKP5O1%PTRLPUPMPRPGO3RGP=P>g00U3RR,3CPFPWn0100000020000=0>?eW@P5O1n10210110300021110010102b6b9W2P5O1%POPNPPPQP=P1PSP=P>13R4PFPWn0100000020000=0>?P4PGP=P>13RCPFPWn0100000020000=0>?eX2TP5O1PGP=P>13RRPFPWn0100000020000=0>?eXLLP5O1n10210110300021010010102b6b9W@P5O1n10210110300021110010102b6b9W3W4f:P5ECbCW1PHP5ECb1W0P5O1b1P5O1b1W0P5P:P4O3W0W3W4X2;XO3P9P:P4P5O4n200210000000020041105100000000A0;5JP=P>%22R=/4B11B918=2'4'3%92A7EB9n0100000020000=0>?[X2;PIO1P51B;JO1b0A7I:4PDPBP:P4C]ECW:X8<X5<XD@XN;XA3P5D_WBo"). Qed.

Lemma find_segment_hit : forall pre s rest a n,
  Forall (seg_misses a n) pre ->
  Z.of_N (seg_base s) <= a -> a + n <= Z.of_N (seg_base s) + Z.of_N (seg_size s) ->
  find_segment (pre ++ s :: rest) a n = Some s.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocLayout ()) [] "p'0h01Hh12H0h21bi001bh31li011lh42Hph55Hresth61si021sh71ah81eh91ni031nh:3preh;1ri041rh<4resth=3Hhih>3Hloh?4Hpreh@4__p1hA4__x1hB4__x2hC4__x3hD4__x4hE2n0hF2H1hG2IHhH7__arithhI4__ffhJ8__varmaphK5__withL4cstrhM5cstr0hN5cstr1hO5cstr2hP2l0hQ2n1hR1ohS1phT1xi051xp;1p;2p;3p;4p;6p;7p;5p;8g000\R0j1WTg009Mj2?j3BTg00>0j21Tg003Wj23Tg001<j1_Tg00;;j30Tg00;Uj1JTg003:j24Tg0052j26Tg0062j3<Tg0076j2ITg00USj2STg00V3j4UTg00Ifj6=Tg00JDj4PTg00<5j6]Tg00<Qj2OTg00=0j6NTg00=Mj2MTg00>LR1j2LTg001^j1GTg002\j1:Tg0044j1ATg00>oj1@Tg00@0j1\Tg00?Rj2KTg00@Nj4FTg00@lj1[Tg00AJj1ZTg00BXj1RTg00B5j2CTg00C`j1YTg00C=j3XTg00DEj4DTg00:Yj1nTg00E0j7mTg00ETj6lTg00F8j2kTg00FZj2iTg00GFj3hTg00Gej4gTg00HWj2TTg00I3j2fTg00IMj1QTg00KWj5cTg00L9R2j3dTg00LZj3bTg00VNj3VTg005Pj2aTg00M:j7`Tg00M^j8jTg007PR3f1R4f0R53dp=;%G5#:p=5%A5#:,34p=8Ab345p=2f3R6f2R75V3?<45p=91a35p=7g008mR8g00QVR9705p=>AV345p=^P4g00NBR:g00NaR;P;g00OAR<P5g00OaF`p=EP6P:P;P;P<P7P4P5Gjp=H%A5#:p=e%W3R=P3g008OR>1?45R?f4R@';%5@/17RA1367f5RB#5/8B'1RC%_3RDf7REf6RF/2BRGP@P6C9%7FRH30[[[^9>]7^<=^63RIX:=%J3RJ,;?PDP8PD%5FRK/4@RL13@6RM18KFRN'4RO'6PHA<B@6n0100000020000%7ERP90D5XRDRQP8P9P8PD13B@RR%5ERS/8ERT'4RU,65PPA<FB@RVn0100000020000=0DPX28P8P9P8PD1695PPPVn0100000020000=0DPX281IDHPO%>O11RT[11MN%>U[1SMNP5CUE=PL%>L11SB[11K@14SB#>[1SK@P4CUE=A<G@6PFPBP@P6CPE=PJPGP@P6C9=0DHeX=CX>AW?X9>X7>X<=X631;?GPDP8PDf9R?#5RK/4@18K?,4M'6%7?RMf8RK/^GRS?<@6n0100000020000PQP2P31?@6f;R2f:RQ'2RL90=4P8PDf<RN#5RU/4E13EF18UN'4'6%7NP212?KRNPEPFC9n0100000020000=0DMRM[P7A0=JN12Q?RU90=JP=PJP0P3p-0RJP5g00PAg00P]RTn10110100020020000000X8=g00Q:PLP5E]PT1OM5b1W0P5O1W0ABQ?41?2Q/;41267fARMf@'250=12@6fBRL/2M50=P=P=P0P3P=P5PBP5n10110100020020102101X8=12B@fCRM/2LP5ENA0=@LP=P3P0P3P3P5PEP4n10110100020020102101X8=PGfDR0/2MP4ENA03F0fERL903EP5fFRR903KP3fGROA0=?ORPAB0M41?L0RV/;2P8PDfKRW#5RX/4RRY13RL18XW'4'6%7WfJRZfHR[/2OPRPLC9n0100000020000%7[50D]5]4[X63A0=KRP5PPP=P[ABL0Z1?RL/;4P8PDfLRL#5RP/4OR\13OR18PL'4'6%7LRPPWfIR]/2[POPRC9n0100000020000%7]50D]5]4X3=AB0M]1;V]1MXR11XR/LYP\P8P1fMR\#5/1[P8PD13Z]R[fORY#5/8YRX'4RR,64%7YfNRV12LWPZP]C9n0100000020000=0DPP4%5V/1]R]1M[XRP11[X/LRRR13WZfPRX#GR[#:R0/8X'4RMP8P113LWfQRO#5/8O'1R^P8PD1694fSR_#7R`fRRa12XYPVP\C9Rbn0100000020000%7XRc50DP413\L%5a%AaRL#:Rd'3'1ReA0D`c%@[g00R6R[/10fT#GR0#@%:0,1[%@L11[dfV#ARd#@%:d,1[g00RTRd#J%WdP>P>%\>RdP41K>@CFP@P>1K>6P7PdCFCF%[>%Z>RdP>g00S@RL#RR0,C>Rf%YLRL,C>5X>Rgg00SeRh%Y0,C>R0%RL,C>5X>RLCD,Ed%n;RiPdP>P0PhPfCD,EdPiPdPdP:P;P;P<P>Pfg00TLRfP0CD,EdP>PLPfPgCD,EdFmPiPdP:P;P;P<PFElCHCHCH1kd<P5P71I891i57#>dAh>[4CgbIbJbKXA>XB>XC>XD>X@J13541376R['111641T7@13@B/T['fPE[[[^A>^B>^C>^D>^@JP5PTfXRT#e%5TPaP_PBP?f>O8bHbObNbMbL'OP8PD1699P`Pbn0100000020000=0DceWPP5O1%QeR_POPXPYPVP\PKPWPZO7RZP8PDg00U3RW,69P`Pbn0100000020000=0DceWEP5O1n10210010400021110110103b2b;W3P5O1%Q]PPPRPMP8P1P^P8PD16W4P`Pbn0100000020000=0DcP4PZP8PD16W9P`Pbn0100000020000=0DceX3eP5O1PZP8PD16WWP`Pbn0100000020000=0DceXQ_P5O1n10210010400021010110103b2b;WEP5O1n10210010400021110110103b2b;W5W4PQP5E=bFW1P?P5E=b1W0P5O1b1P5O1b1W0P5P7P4O3W0W5W4X3=XT3P6P7P4P5O4n200210100000020041105101000000A0=5UP8PD%52R8/4F13FB1882'4'6%72PQ12KEPFPBC9n0100000020000%7K50D[X3=PNO1P51I=UO1b012?S?<@6P?PSP@P6CPE=PNPGP@P6C9=0DHeX=CX>AW?X9>X7>X<=X63XGIX:=XS3P5DcW:o"). Qed.

(* [comment removed for export] *)
Lemma seg_rom_unfold : forall segs (a : word),
  seg_rom segs a
  = match find_segment segs (bv_unsigned a) 1 with
    | Some seg => if seg_readable seg
                  then match segment_read_bytes (seg_bytes seg) (Z.to_N (bv_unsigned a - Z.of_N (seg_base seg))) 1 with
                       | Some (b :: _) => Some b | _ => None end
                  else None
    | None => None
    end.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocLayout ()) [] "p'0h01ah11bi001bh21oi011oh33segi023segh44segsi031li042l0i051si061xp;1p;2p;3g000\R0j1<Tg00BXj11Tg00Vkj19Tg00WIj1;Tg00Wlj22Tg00XVj1DTg0062j3=Tg001<R1j1:Tg00Y4j1@Tg00Z6j18Tg001^j17Tg002\j14Tg00[5j23Tg00[Rj16Tg00\0j1ETg00\Pj30Tg00:Yj1?Tg005Pj2CTg00]Zj1BTg00;;j35Tg0076j2>Tg00^9j2ATg007PR2#<g00S@R3#1#1#1R4#1#1#1#9R5#;f1R6f0R7,25R8%D33=R9%:2P1P2%94#;R4#:R:P1%<4R;P:P1P2%:;R<P7g008mR=P<%@7R>%87R?f3,25%77#4R@'3#6RA%93R3#ERB30%?;RCn0100000020000PCn10110600021010200P0P4P:P7%?4R01C46n10110300020020100104R4P0n10110600021010300P1P2P:P7P=P:P>P1P;P:g00_5#BRD90?AP4P0n10110600021010300P0n0100000020000P0n1011060002101020035P7P>P=P=P1P;P:P=P<P7f2RA#8REf5,25%7A#4'3#6RA;0BPCn0100000020000P4P0n10110600021010300P=P:P7P1P;P:A0EADP4P0n10110600021010300P0n010000002000055:P7P1P;P:%86f4,25%76#4'3#6;0DP4P0n10110600021010300,>:1>:0RAn0110001020000b1X32P7O1PAn10110101021110500b2P1P;P:P1P2P<%439=68P=P<P>1256/3@#6R@=0?BPCn0100000020000PCn10110600021010200P4P0n10110600021010300P1P2P:P9P=P:P>P1P;P:A0?@DP4P0n10110600021010300P0n0100000020000P0n10110600021010200R055:e1A67=5:0eW0W4o"). Qed.

Lemma seg_rom_none_of_find : forall segs (a : word),
  find_segment segs (bv_unsigned a) 1 = None -> seg_rom segs a = None.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocLayout ()) [] "p'0h01oh11Hh21ah34segsi001bi011li022l0i033segi041xp;1p;2p;3p;6g000\R0j17Tg00BXj10Tg00Vkj14Tg00WIj13Tg001<R1j1<Tg00Wlj21Tg00XVj1CTg0062j35Tg00:Yj16Tg00;;j32Tg00Y4j1?Tg00Z6j1>Tg001^j1=Tg002\j1FTg00[5j2;Tg00[Rj19Tg00]Zj1ETg00\Pj3:Tg005Pj2DTg0076j2BTg00Ifj68Tg00^9j2ATg00_Tj2@Tg007PR2#7g00S@R3#0#0#0R4#0#0#0#4R5#3%<2R6f1R7f0R8,15%C3R335%62R932%44#3R4#<R:P1P2P:f2R;1157;53R3g008mR<P:%?8R=P1%74R>P:%>8R?115;%=8#FR@';#9g00_5#ERA3:P0P4P:P8%64R01D47n10110100020020100102R4P0n10110400021010100P0n0100000020000P0n10110400021010300A2:80X0:P6P9P1P2P:P8P<P:P=P1P>P:f3,15/;@#9=:?AP4P0n10110400021010100P0n0100000020000P0n10110400021010300=2:0X061B:0P3P8E81A;71@;7E8W1W2W3o"). Qed.

Lemma seg_rom_some_of_find : forall segs (a : word) seg,
  find_segment segs (bv_unsigned a) 1 = Some seg -> seg_readable seg = true ->
  segment_byte_at (seg_bytes seg) (Z.to_N (bv_unsigned a - Z.of_N (seg_base seg))) <> None ->
  seg_rom segs a <> None.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocLayout ()) [] "p'0h02Hbh11oi001oh21bi011bh31Hh42H0h52H1h62Hrh71ah81eh93segi023segh:4segsi031li042l0i051xp;1p;2p;3p;6g000\R0j1BTg00BXj12Tg00Vkj1?Tg00WIj1>Tg001<R1j1=Tg00Wlj23Tg00XVj1LTg0062j3ATg005Pj21Tg00;;j39Tg00Y4j1;Tg00Z6j16Tg001^j18Tg002\j1:Tg00[5j25Tg00[Rj14Tg00`dj2DTg00:Yj1CTg00]Zj1KTg00\Pj37Tg00;Uj1JTg00LZj3ITg00<5j6HTg00<Qj2GTg00IMj1@Tg00Ifj6<Tg00^9j2FTg00_Tj2ETf2R2f1R3f0R439#@p=0g007PR5#Bg00S@R6#2#2#2R7#2#2#2#?R8#>%=5R91383%L6R65A2115439g008mR:%;3g00QVR;39%?7#>R7#=R<%62f3R=,38%82#:'5#4'D%C7R>30P<P1P5P<f5R?f4R@,38RA;A6R6P:P<%;4RBP1%B7RCP<%64RD138?RE%84#:RF'5#4g00_5#KRG37P0P7P<P4P>1173R0n10110300020020101104RHP>n10110500021010300P>n0100000020000P>n10110500021010200A0<4>RIX1<P9115=P1P5P<P4P:P<PBP1PCP<f6,38/5F#4=7DGPHP>n10110500021010300P>n0100000020000P>n10110500021010200=0<>X19P:P;P:P<P4P1PCP<%6@%8@#:,5E#4;7GPHP>n10110500021010300P>n0100000020000=0<>X2:%6=R:%8=#:,5A#4RA'DP<P1P7P1PCP<P1P7%=CP3%J79I74,1C%CCn10110500021010100PHP>n10110500021010300=0<>^0IP41174=0<>A9<0>R0P<1172P1P7p-0P4g00PAg00P]RIn10110000021000000X8<g00Q:P>P4EHPI1GI4b5W4%@0eW0X27P4O1A0<>>P4W0n10110000021010100P3O1b1P1PCP<A7:AGPHP>n10110500021010300=0<>e%;=P3E<P6P2E<1F?@1E?@E<W0W6W3X95W7W:o"). Qed.

Lemma wview_of_find_none : forall segs m (a : word),
  find_segment segs (bv_unsigned a) 1 = None -> wview segs m a = m a.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocLayout ()) [] "p'0h01oi001oh11Hh21ah31bi011bh41mh54segsi023segi031xp;1p;2p;3p;6g000\j1DTg00BXj10Tg00Vkj14Tg00WIj13Tg001<R0j18Tg00Wlj22Tg00XVj1<Tg0062j35Tg00:Yj16Tg00;;j31Tg005Pj2;Tg00akj1:Tg00Z6j19Tg001^j1CTg002\j1BTg00[5j2ATg00[Rj1=Tg00`dj2>Tg0076j27Tg00Ifj6?Tg00bmj3@Tg007PR1#Dg00S@R2#0#0#0R3#0#0#0#4R4#3R5%43#3R3#8R6[%81R7f2R8f0R9,24%<2R235%61R:31P7P:P0P3P6f3R:P8O1R;1;39R<P0P1P6P9g008mP6%:9%99124:%C9#B'A#='>%63R1n0100000020000P1n10110300021010200n10110300021010100=16;X07P8f1R7O1R;P6P0P3P0P3P6P9P<P1n10110300021010100=169P9176<X33P9O11761n10110000021010100b01247=5:2P9E?A@:87=16;eW1X25W4W5o"). Qed.

Lemma wview_of_find_ro : forall segs m (a : word) seg,
  find_segment segs (bv_unsigned a) 1 = Some seg -> seg_writable seg = false -> wview segs m a = m a.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocLayout ()) [] "p'0h01bi001bh11oi011oh21Hh32Hwh41ah51mh63segi023segh74segsi031xp;1p;2p;3p;6g000\j1DTg00BXj10Tg00Vkj17Tg00WIj15Tg001<R0j1@Tg00Wlj22Tg00XVj1BTg0062j36Tg005Pj23Tg00;;j31Tg00akj14Tg00Z6j18Tg001^j19Tg002\j1?Tg00[5j2=Tg00[Rj1<Tg00`dj2;Tg00:Yj1CTg0076j2>Tg00Ifj6:Tg00bmj3ATg007PR1#Dg00S@R2#0#0#0R3#0#0#0#7R4#5R5%73#5R3#@R6[%@1R7f3R8f1R9,24%B2R236f0R:,3131g008mR;%49g00U3R<31P7f2R=,31P0P3P6f5R>f4R?O1R@133:RAP0P1P6P:P;P6%4:%8:124>%9:#?'=#<';%C3RBn0100000020000PBn10110300021010200n10110300021010000=16@X17P;P<P0P3P6P@PAP;P6P:%88124?%98#?'=#<';PBn0100000020000n10110300021010000=16@X0;P?P8O1R;P6P0P3P0P3P6P:PAPBn10110300021010000=16:P:1>6AX03P:O11>6Bn10110100021010000b1%4=P:E:1248=6>2P9E:AA>?8=16;eW3W2X61X45W5W7o"). Qed.

Lemma wview_of_find_rw : forall segs m (a : word) seg,
  find_segment segs (bv_unsigned a) 1 = Some seg -> seg_writable seg = true ->
  segment_byte_at (seg_bytes seg) (Z.to_N (bv_unsigned a - Z.of_N (seg_base seg))) <> None ->
  wview segs m a <> None.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocLayout ()) [] "p'0h01bi001bh11oi011oh21Hh32H0h42H1h52Hbh62Hwh71ah81eh91mh:3segi023segh;4segsi031xp;1p;2p;3p;6g000\j1FTg00BXj11Tg00Vkj1=Tg00WIj1<Tg001<R0j1@Tg00Wlj23Tg00XVj1DTg0062j3>Tg005Pj25Tg00;;j30Tg00akj1;Tg00Z6j14Tg001^j18Tg002\j1:Tg00[5j29Tg00[Rj16Tg00`dj27Tg00:Yj1ETg00IMj12Tg00<5j6CTg00<Qj2BTg00Ifj6?Tg00bmj3ATg007PR1#Fg00S@R2#1#1#1R3#1#1#1#=R4#<R5%=3#<R3#@R6[%@1R7f3R8f1R9,34%D2R23>f0R:,5130g008mR;%;9g00QVR<30f2R=#41348%8=#:'9#6'7%E3R>506#2P71518P0P3P6f6R?f5R@O1RA153:RBP0P1P6P:P;P6%;:%4:134?RC%8:#:'9#6'7P>n0100000020000P>n10110300021010200n10110300021010000=06>#2X17P;P<P0P3P6PAPBP;P6P:f4RA#4134@%8A#:'9#6'7P>n0100000020000n10110300021010000=06>#2X0;P@PAO1P6P0P3P0P3P6P:PB%4@%8@#:,9C#6'7n10110300021010000=06>#2P:A06B>RBP61539P0P3p-0P:g00PAg00P]R0n10110100021000000X86g00Q:P>P:ECP01B0:b4W3%2BeX03P:O1P9n10110100021010000b1%;8P9E?134A=>?2P=E?AA?@A=06>#2eW5W6W2X:1X75W9W;o"). Qed.

(* [comment removed for export] *)
Fixpoint Zseq (lo : Z) (n : nat) : list Z :=
  match n with O => [] | S n' => lo :: Zseq (lo + 1) n' end.

Lemma Zseq_In : forall n lo x, lo <= x < lo + Z.of_nat n -> In x (Zseq lo n).
Proof.
ltac2:(KReplay.run1 (kr_t_MallocLayout ()) [] "p'0h01xh11Hh24__x1h34__x2h42loh51ni001nh62H0h77__arithh84__ffh94__p1h:8__varmaph;5__with<4__x3h=3Hneh>2IHh?4cstrh@1ei011ehA1mhB1si021shC1yp;2p;1p;4p;6p;3p;7p;<p;Bp;8g00>0j23Tg00cjR0j12Tg00dJj26Tg003WR1j20Tg00HWR2j28Tg00ePj2CTg00ekj1ATg00fIj4VTg0076j2=Tg00flj6JTg00gUj4KTg00;Uj1^Tg000\j1]Tg00?Rj2ITg00@0j1ZTg00@Nj4HTg00@lj1YTg00AJj1XTg00B5j2BTg00BXj1WTg00DEj4;Tg00h<j2GTg00C=j3:Tg00:Yj1UTg00ETj6TTg00F8j2PTg00FZj2QTg00;;j3FTg00GFj3RTg00Gej4STg00]ZR3j1<Tg00h_j2nTg00IMj1DTg00i?R4j2mTg00XVj1lTg00I3j2LTg00i_j3kTg00Ifj7jTg00j9j1dTg00C`j1_Tg00j^j6`Tg00kBj3aTg00k\j4bTg00l=j3cTg00lTl<ETg00m9lB\Tg00m_l<[Tg00M:j7gTg00nDj7hTg00M^j8iTf3R5f2R6f1R7f0R8'0'8'Cp=1g008OR9?c78p=71=98p=4g00nhR:P9P9P9P0P0P5P6P7g00_5R;g00R6R<P8M<Ep=OP9P9P9P9P9P9P1P8P7P6P1P5f4R1f5R=f6R>f7R?f8R@f9RAMB\p=NP9P9P2P?P2P>P=P1P5P6P7P8M<[p=MP7g00NBR2g00NaRBPBg00OARCP8g00OaFgp=9P9P7g00TLP8C;p=@P6P2PBPBPCP7P8Fhp=?P5P2PBPBPCP6P7P8Gip=>AF978p=5P:P:P9P9P3P0P0P5g00oGP6P7P8M<Ep=fP:P9P9P9P0P0P=P1P5P6P7P8M<Ep=e1378R0P8P7%26C11665,77[^09^49R3X5:P0P8P7%2;RDC11367RE106DRF,87RG'CPEP7P6P<C1RHPEPGPEP8X09RGP<O1RI,06RJ,87%AEPG1878#AXC9X09REP7P7%47PFPJPGPGPGP9P9g00ok1078CV#4XA9X59RJP6P6%46PDPIPGPG%28#4X0:RI1=9<COM:NGMEJP8CKPHp-0RHg00RTRD#^RF%]DRDP91I96RKP7%Z9CH%Y9RL%X9RMP9g00S@RN,B9ROg00SeRP%WN,B9RQC;,9MRR1G9<9:9O,@Q,9M5?M%UBRSPMP2PBPBPCP1ETC>1PMCRTP8P6g008mRUg00QVRV'=1Q86=FUVdAR9<7CSRVb8b:b;X29X39W91387RUP7P8P<C1P5[^29^39^9HP8161;,75P5P1P7O4b7b6W1X09X49P0P8P7%<5#2C11n671567R0%D0'mP41556R4%D41515R4%lNR0,01/6>,75'LP8P9P1138=P=P8%<@#2C1157>1070/6A,7>'L]1X491311P1P1%<?RA#2R;C115==10=0RH/6@,7=%4=RW3kW1P=P8P5FjX@4P8O1%D415=116H?,71P>PHP113=1RH10=;R>,81R4'CPHP1P=%2?RX/00C1RYPHP4PHPG1080X09R4PXO1RZO1R[,0=R\,81%AHPGPEP1P1%41P>P\PGPGPGPJP=P=PWP;P[PGPGPIPAPZP4P?PX%4XCfEeM:NGMEJP5CKPY%d@%2@,3<PFPDP9PKP71I95CHPLPM%_N,B9RN1G90RL5:99:9O,@Q,9M9?MRPSPMPMP2PBPBPCP9POg010OPQC;,9ME`PSP9A:9OLRLPPPQC;,9MA:9LN,@Q,9M5?MC>C>PTPVb8b:b;X29X39X<9PUP7P81060R0C11576g00P][1305P5P0P1C1[[^29^39^<9P8f:#2P?P@P6P5O5b7b?b6O33aW=P8O1n200110200021010111100bB%<1,66,77eW1X09X49X>3X5:P8CbX5:o"). Qed.

(* [comment removed for export] *)
Definition chk_range (f : Z -> bool) (lo : Z) (pages : nat) : bool :=
  forallb (fun pg => forallb (fun i => f (lo + 4096 * pg + i)) (Zseq 0 4096)) (Zseq 0 pages).

Lemma chk_range_sound : forall f lo pages, chk_range f lo pages = true ->
  forall a, lo <= a < lo + 4096 * Z.of_nat pages -> f a = true.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocLayout ()) [] "h04__x1h11ih22H0h32H1h42H2h52H3h62H4h74__x2h84cstrh91qh:1rh;7__arithh<4__ffh=6__sat0h>8__varmaph?5__with@1xhA4__p1hB1HhC2H5hD2H6hE5heq_ihF2pghG2H7hH2H8hI6__sat1hJ4__x3hK6heq_pghL4__x4hM1ahN5lemmahO2EahP2H9hQ2HahR2HihS3HpghT6__sat2hU1fhV2lohW1mhX1nhY5pageshZ1yp%0p&0p;3p;2p;1p;4p;5p;6p;<p;7p;8p;Bg0116k30ETg00>0j2ITg00BXj1WTg00XVk10:Tg00cjR0j16Tg012Aj27Tg003WR1j24Tg00dJj2VTg00l=j3\Tg012^j2dTg0137j3bTg013hj3aTg00[5j25Tg014Kj29Tg014hj28Tg00HWS00j23Tg00j9j1MTg015Hj2QTg0169j2Kj3sTg00IMj1gTg016Zj2Gj3uTg017Aj2HTg00ePR2j2?Tg017hj2JTg018Nj2LTg00;Uk10CTg000\k10BTg00?Rj2YTg00@0k10=Tg00@Nj4XTg00@lk10<Tg00AJk10;Tg00B5j2STg00:Yk109Tg00h<j2eTg0194k308Tg00F8k207Tg0076j2TTg00FZk203Tg00GFk302Tg00Gej4~Tg019Wj4}Tg00C`j1{Tg01:8j3zTg00C=j3NTg01:[j5wTg01;Gj4vTg01;bj2OTg00j^j6tTg01<Sj1xTg01=1j2yTg01=Rj2cTg01>;j3rTg01>dj3qTg01?Mj2pTg00LZj3|Tg01@9j4`Tg01ABj3oTg00ekk100Tg00fIk401Tg00m_m<04Tg00flj6lTg01Ahk405Tg00Ifk606Tg00;;j3UTg00]Zj11Tg01BSj3kTg00DEj4ZTg00M:j7jTg00ETj6iTg00nDj7hTg00M^k80?Tg00lTm<0@Tg00m9mB0ATg008mR3f0R4g00QVR53Up=<%W4#Wp=Rf2R6f1R7/34'?p=:1467/44p=D%14#1p=_%14#1#1#1p=f%14#1#1#1#1#1#1#1p>0D%14#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1p>0>%14#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1p=0g008OR8?k74p=Bg00R6R9/I4p=21T84p=@AU874p=>AU849p=E14749U86p==1I49p=FP8P7g00SeP4CZp=^P7g00NBR:g00NaR;P;g00OAR<P4g00OaFjp=;P7P:P;P;P<P4Eip=]P6P:P;P;P<P7P4Fhp=Pf3R=P:P;P;P<P6P7P4L0?p=AP8P7g00TLP4CZp=CP8P7g010OP4CZp=[g00nhR>P8P8P8P0P0f5R0f4R?P=P6P7P4N<0@p=nP8P8P8P8P8P8P1f7R@f6RAP0P1P?P9P9P=P6P7P4NB0Ap=mP3\8B0E674#<1I=4g00S@R1#WRB#WS01#R#R#R#R#R$0:RC%66'7,4=7:4P@17C7RD=DA4O1X18g00_5S02#_S03#_#f$0D$0>#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0RE,V9RF'BXF8RG1V9=RH'B#<1V9?RI9\84f9RJf8RK?DD4O1X18/BFXF8P7O1#<[^@8RL'dPKAD@D4O1X18/BFXF8/BI#<1V909\84f:RIADJD4O1X18/BFXF8P7O1#<[^@8;b4WNAa8GHP6O2PL1560/9CP815=A/8CP815?@RL/9CRH#2%6ARG,3HPLPC18LCRH#@1>4HRHeS04PH%M@S05%6@#2S0615AJRD/QCS07%2D%2CRMf;RN,5KRO/8CRP#2[[S0815@IRQ/KCS09%ECRR#gRS19OCRT,7C==OP[RP1GOCRU139CRVf<RW,5JRX/8CRY#2S0:?:YC[RZ1HXCR[13C9R\f=R],5IR^/8CR_,3C%F_'?[R`1J^CRaf>Rb,5NRc/9CRd#E\RRe1LcCRff?Rg,5WRh/8CRi/>h\RRj19hCRkP8f@Rl,5]Rm/8CRnP8p-0Rog00RTRp$0CRq&0BpRrP81Y86S0;P7&0=8RsCXS0<&0<8Rt&0;8Ru1S8BRB1S81Rv'^,;uS0=1]u?5Pu&09;Rw1e89RxB088vBRy'^,;uCA207u<RzP4P61T3520346#<dB02897C~R5b<b>b?X08X78WA1I74/?61576R3#2[^08^78^AoP4fBR{fAR|#6R},7C'4,3gP{PgPbO4b;b:b9b6b5b4b3b2b=b8bEQ04PHQ05Q06Q07Q08Q09PPPUPZP[P`PaPePfPjPkP8PnP8PqPrPsPt1e8CR~,Cx,;uPzP5b<b>b?PVP4b;S0>b:b9b6b5b4b3b2b=b8bES0?C}PLPCPGQ0?Q04PHQ05Q06Q07Q08Q09PPPUPZP[P`PaPePfPjPkP8PnP8PqPrP8Q0;P71Y8=S0;CXPtPu1]u0%{1,S89z8~Rj9N8BS09,Cv,;u5PuPw1Cyj,;uCAPzP5b<b>b?X08X78XJ8XAo17C6S08,479:=417C=Rf,33[^08^78^J8^AoP41I{gP}P{PgPbO5b;b:b9b6b5b4b3b2b=b8bEDwCv%27Re?:7G150KRG19GCRG#@1>6GRGePG%MKRG%6K#2Ra1OQC%2QR`19XCR[#2\M[1KOC17C[==XY\S1GXC%2_S07?:_C\V1H^C18cCR[,3C%F['?\\1JcC%Ek\R1LhC1>nm\R19mCRkP815b|RZ/8CRUP8P2%2W13W}PVPI%2bfDR}#6,3gQ0>WDWCP7P4O2n2001000000120000000b:b9b6b5b4b3b2b=b8bK7uCA:e7CPGPa1QQCQ0:\M\`1OOC%2OS0:19^CR`#2\M[1KXC17C`==^_\S1G^C%2[?:[C\V1HcC13Ci%Fi'?\\1JhC%Ek\R1LmC1>UZ\R19ZCS0>P815g{R_/8CRaP8P2%24S06134CS05PSPI%26RG13=CS04P2%20S0?fFRP#6S0@,30PSPg%2@RHfIRL#6S0A,3KPqPrPsPtPuP:P;P;P<1[~x,;uEtS0BPzP5b<b>b?g00P]\RR<P4b;WHWGP7P4O2n2001000000120000000WDWCP7P4O2n2001000000120000000b:b9b6b5b4b3b2b=bIb89sDC19DC,7C18DC5=D%MJ%6J#21QOCQ0:Q07\M[1OXC%2X%2d\M[1K^C17Cd==c[\S1GcC%2iS0:?:iC\V1HhC13Cn%Fn'?\\1JmCQ0>#E\R1LZC1>a_\R19_CRiP8fCR[,5lRd/8CRXP8P2Q06Q05fEROQ08'4=={7PNQ04P2Q0?fGRD#6,3017CAS0?,4L==P0PlfJR;#6R:,3K%x1,y8Q03,c85r8Q02,c85q8g01Bo'p=|pqPrP8P81Y8?P6PsCXP7Q0;CXPtPuPuQ0BPwQ01,S8Rs9N8j,[y,;uRyCAPwPuPyPwPuQ0=1]uA5PuPwQ09=N8s,[v,;uCACACAPzP5b<b>b?X08X78XJ8XL8XAoA=3f?R3\<1I=6/?A17C0R<,4?===A[\3[^08^78^J8^L8^AoP4fMR3fL#6Rs,7C'4,3;PJPIP3P;PgP[PLO8b;WPXHHP7P4O2n2001000000121000000WGXDGP7P4O2n2001000000121000000b:b9bCb6b5b4b3bIbTb8b214Jf==A6P0P?PJP9P?18QCRQ#@1>=QRQePQ%@T1>0TRTePT%MN%6N#21Q^C%2^Q0:\M[1OcC%2c%2k\M[1KhC17Ck==mn\S1GmC%2URn?:UC\V1HZC13Ca%Fa'?\\1J_C19dC#E\R1LdC15|}RU/8CRk/>U\R19UCP815{ORc/8CP8P2%2g13gC%2|R^Q0@,497:|P]13{CP2%2}Q0A,3}%2O149:7:OP{%2PRO13DsPqPrQ0<PtPu1CvB,;uPwPu1^xv,;uRsPwAN8xB,Cv,;u9PusCACAPzP5b<b>b?X08X781347149=9:G6\e[^08^78P4fN#6RBPLP7P6O4b;WHWGP7P4O2n2001000000120000000WDXC^P7P4O2n2001000000121000000b:b9b6b5b4b3b2b=bIb8bKbEC`O2PWADN<4O1X18/BF#<P]Q0?,4WRW/44O1X18R</BF#<A\84FRNPg17CK=Db4O1X18P7O1#<[^@8RK'dPb17C@,4]Rb/44O1X18/BF#<Pl17CJ=Dg4O1X18P7O1#<\N^@8;b4WNAa8<FP4O2PKP4P0PEP9P0%@Y1>0YRYePY%@`1>@`R`eP`%6ER`,49RY,3@RK,?H149CR<,3@RF,?HPHPKPHPF1ToH9oHHP8P8Q00P4X@8RHQ001374$00XZ8X@8P@P@%@@PYP<PHPHPHP8P8g00ok1474H01#@XW8XX81T89P`PCPHPH%64#@X@>PEPC%@CEnGmN<04El%M]%6]#21QhC%2hPn\M[1OmC%2m%2i\M[1KZC17Ci==_a\S1G_C%2X?:XC\V1HdC13Ck%Fk'?\\1JUC19cC#E\R1LcC15[PRc/8C/>c\R19cCP815}D/8CP8P2P^13|C%2{?:{<Pg%2[13}CP2POfK#6,3PA:OP<P}fH#213LBPqPr1Y87PtPu1Cv~,;uPwPuPsPwAN8x~,Cv,;u9PusCACAPzP5b<b>b?X08Q05A:G6<\e[^08P4P;P0PAO3b;WHWGP7P4O2n2001000000121000000WDWCP7P4O2n2001000000121000000b:b9b6b5b4b3b2b=bIb8H05bKbEC`O2P]14W0O1#<P814bAPgP4O1#<XM8P4PIP=J06bBbBbBbObRbSb1bFbBWQXM8WBXY>XV8WUo"). Qed.

(* [comment removed for export] *)
Definition chk_list (f : Z -> bool) (lo : Z) (n : nat) : bool := forallb f (Zseq lo n).

Lemma chk_list_sound : forall f lo n, chk_list f lo n = true ->
  forall a, lo <= a < lo + Z.of_nat n -> f a = true.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocLayout ()) [] "h01Hh11xh22Hah31ah41fh55lemmah62loh71np;3p;2p;1p;4g01C[j3>Tg00>0j25Tg00cjj14Tg003Wj2=Tg00HWj2:Tg00ePj26Tg00dJj21Tg01BSj32Tg00l=j33Tg012^j27Tg0137j38Tg013hj39Tg01@9j4<Tg00;;j3;Tg008mR0f0R1g00QV3;p=0g008OR2P0[g00nhf2R0f1R3;>1#0f3R4/51%40,=4,:1'6f5R5f4R6/14R4522#01156R79321f7P3O1#0[^12R8'7f6R9=227#011959321f8P3O1#0[^12;81W5A9254P0O2P8P1P0P6P5P0P3C<O2b0W2X32W0W7X62W4o"). Qed.

(* [comment removed for export] *)
Fixpoint chk_rom_bytes (rom : word -> option byte) (a : Z) (bs : list Z) : bool :=
  match bs with
  | [] => true
  | b :: bs' => match rom (Z_to_bv 64 a) with
               | Some v => (bv_unsigned v =? b mod 256) && chk_rom_bytes rom (a + 1) bs'
               | None => false
               end
  end.

Lemma chk_rom_bytes_sound : forall rom bs a,
  Forall (fun b => 0 <= b < 256) bs ->
  chk_rom_bytes rom a bs = true -> rom_bytes rom a bs.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocLayout ()) [] "p'0h01Hh12H0h22H1h32Hbh45Hresth52Hvh61ah71eh82bsh91li001lh:2H2h;3Hbsh<1bi011bh=1mh>1nh?1vi021vh@1zi031zhA2IHhB1oi041ohC3romhD1xi051xp;1p;2p;3p;6p;8p;4p;5g00BXj1:Tg00Vkj1JTg00WIj1ETg001<R0j1OTg000\R1j1WTg00>0j2ATg00XVj1ITg00HWj2@Tg00ePR2j23Tg00L9R3j3>Tg01Dej38Tg01F4j34Tg00;Uj1VTg00;;j30Tg01G?j21j1NTg005Pj26j1QTg003Wj25Tg00<5j6CTg00<Qj2HTg00=0j6GTg0076j2?Tg00Wlj2<Tg014hj2=Tg01Gej2;Tg0052j2FTg01HBj3STg01Hej2RTg01IEj3MTg00Ifj6BTg01Ihj8DTg01JEj2LTg01;Gj4PTg00:Yj1KTg00KWj5TTg00LZj3UTg008mR4f0R5g00QVR630p=2g008OR7f1R8;U5p=7A0785p=9g00S@R9#:#:#:R:#:#:#:R;#JR<#E%J:R:#ER=#OR>[%W7R?P7g00R6R@/A5%:;#:#IR;,@5'3X<7RA=>78RBf4RCf2RD788#2f5REf3RF74D[[^67X8?%V7RG9>7AA8F8G#2g00Q:RHW0W;X67A8E8D#2f6RI?4DF[\B^6717FDRJ9>7A17CFRK98I8#2P3P7PAf7R3/7IRL90?8f:RM11<EO1f8RN,1:,6=50>%I9R9,5E=4M3'3RO[P817ECRP90?G17IERQ90?GP?PGP1P7p-0RGP5g00PARRg00P]RSn10110000020020000000X7?PHPLP5ECPS1HO5b2W1P5O1W11A@81@8;'3ROf=RLf<'790?Jf>RJ/7L90?KP?P?P1P7P?P5PEP5n10110000020020103100X7?PPf?RK/7JP5EGA0?CJP?P7P1P7P7P5P3P8n10110000020020103100X7?PQf@R1/7KP8EG19I1fA,93P5fBR1,9NP7fCRKf9RT=0?KRKf;9>7AfIRUfDRV,1<O1RWfGRX,1:,6=50>15V9fFRY54U'3]4^3O[X@7A0?N1P5PKP?PV1A@Y1@Y;'3fJRKfER1,1<O1ROfHRZ,1:,6=50>1519=4KX'3^4B]3X9?1A@11@1;'3A>7A1PWP>1?>5A0>O5P0P=fLRO11<XO1=0>5P0P=P4P81<:51=O;R0';fNRX15U9RUfKRW38R1'Fg00U3RAn10110500021010200#211:O,6=R@90>DA4XUWRU'3]0]5P8fMR[11<ZO116=550>1<:8/;0/F1#21<:D1=[;';R1fOR015K9;8ORK;S5%21%2K'3P21<:F1=X;';#2fPRK15W9;8[#216=C11:0,6=50>fQR015O9;4X'3P51<:E1=K;';#2fSRE15X9;8K#2P21;85#219D8[R219851;D8#2RK[19FD\K1R85P8n2001000000120000000X=7X>7P2^=7^>7P51<:NRN1=E;R2PDO319N216=TfTR2,1:RN,6=50>fV1509R0;4EP=P>%Q=REPEPTPNP>\=/?EP=1<:TRE,1:fURN,1:90=5X?=P7P=%N:RKPKPEP2P=\7/?KP71=2;195NX@7AM2;JPEP5EBGDPT1L:TECGDfRP0PLPDO3CPb2b0W:W2P8P5O2n2001000000121000000b0W0W5X?=P5O1PW11<YO1%K=RY50>A04A6P4PAP4PGP5PSPRn0110100020000X74PHP6P5ECPSA0>Y@/3U/H5b1W0W5n10110400021110100P5PVO2b5bBW4W3PMP5EBb:W2PTP5EBb2W1P5O1b2P5O1b2W1P5PDP8O3W1X4BW3X9?XD7PFPDP8P5O4n200210000000020041105100000000A0?5QPT11<CO111:3,6=50>15C9=4TI'3[X9?PPO1P51??QO1b1A43DPeW0W;X67WAX8?X<7P5DTW8WCo"). Qed.

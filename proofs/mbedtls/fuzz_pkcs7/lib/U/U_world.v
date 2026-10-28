(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import Amb CatExec StoreOk BBFrame MallocDefs.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import U_enframe_base.
Import ListNotations.
#[local] Existing Instance PropExec.fx0.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_P_world () : Init.string Init.list := ["Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Datatypes.nil"; "Corelib.Init.Logic.or"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.add"].


Abbreviation RSEGS := Ubsan.M.loaded_segments.


(* [comment removed for export] *)
Definition cell (M : word -> option byte) (a : Z) (n : nat) (v : Z) : Prop :=
  rdn RSEGS M (Z_to_bv 64 a) n = Some (word_to_le_bytes n (Z_to_bv 64 v)).

(* [comment removed for export] *)
Definition zero_bytes (M : word -> option byte) (a n : Z) : Prop :=
  forall i, 0 <= i < n -> M (Z_to_bv 64 (a + i)) = Some (Z_to_bv 8 0).

(* [comment removed for export] *)
Definition img_clear (M : word -> option byte) (lo hi : Z) : Prop :=
  forall i, lo <= i < hi -> M (Z_to_bv 64 i) = None.

(* [comment removed for export] *)
Definition img_clear_ivs : list (Z * Z) := ltac2:(CDefT.buildp (gd_tbl_P_world ()) "(0.(1.$2.$2.)(3.$2.$2.=+1000.)(0.(1.$2.$2.)(3.$2.$2.+10000.+4<?20.)(0.(1.$2.$2.)(3.$2.$2.+4<?21.+5<??8.)(0.(1.$2.$2.)(3.$2.$2.+7=0=0.+7=0?0.)(0.(1.$2.$2.)(3.$2.$2.+5=02<.+5=078.)(0.(1.$2.$2.)(3.$2.$2.+5=080.+5=098.)(0.(1.$2.$2.)(3.$2.$2.+5=0:0.+5=0;8.)(0.(1.$2.$2.)(3.$2.$2.+5=0<8.+5=0=8.)(0.(1.$2.$2.)(3.$2.$2.+5=0>0.+5=150.)(0.(1.$2.$2.)(3.$2.$2.+7=108.+7=330.)(0.(1.$2.$2.)(3.$2.$2.+7=338.+7=340.)(0.(1.$2.$2.)(3.$2.$2.+7=351.+7=358.)(0.(1.$2.$2.)(3.$2.$2.+7=360.+7=368.)(0.(1.$2.$2.)(3.$2.$2.+7=378.+7=380.)(0.(1.$2.$2.)(3.$2.$2.+7=388.+7=3;8.)(0.(1.$2.$2.)(3.$2.$2.+7=3<0.+7=3<8.)(0.(1.$2.$2.)(3.$2.$2.+7=418.+7=578.)(0.(1.$2.$2.)(3.$2.$2.+7=580.+7=6?8.)(0.(1.$2.$2.)(3.$2.$2.+7=700.+7=758.)(0.(1.$2.$2.)(3.$2.$2.+7=759.+7=760.)(0.(1.$2.$2.)(3.$2.$2.+7=770.+7>000.)(4.(1.$2.$2.)))))))))))))))))))))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition CTX : Z := 0x7d3c8.
Definition ctx_secret : Z := CTX.            (* [comment removed for export] *)
Definition ctx_init_done : Z := CTX + 8.     (* [comment removed for export] *)
Definition ctx_mmap_counter : Z := CTX + 12. (* [comment removed for export] *)
Definition ctx_free_meta_head : Z := CTX + 16.
Definition ctx_avail_meta : Z := CTX + 24.
Definition ctx_avail_meta_count : Z := CTX + 32.
Definition ctx_avail_meta_area_count : Z := CTX + 40.
Definition ctx_meta_alloc_shift : Z := CTX + 48.
Definition ctx_meta_area_head : Z := CTX + 56.
Definition ctx_meta_area_tail : Z := CTX + 64.
Definition ctx_avail_meta_areas : Z := CTX + 72.
Definition ctx_active (sc : Z) : Z := CTX + 80 + 8 * sc.          (* [comment removed for export] *)
Definition ctx_usage (sc : Z) : Z := CTX + 80 + 384 + 8 * sc.     (* [comment removed for export] *)
Definition ctx_unmap_seq : Z := CTX + 80 + 768.                    (* [comment removed for export] *)
Definition ctx_bounces : Z := CTX + 80 + 800.                      (* [comment removed for export] *)
Definition ctx_seq : Z := CTX + 80 + 832.                          (* [comment removed for export] *)
Definition ctx_brk : Z := CTX + 80 + 840.                          (* [comment removed for export] *)
Definition CTX_END : Z := 0x7d770.


(* [comment removed for export] *)
Definition W64K : Z := 17 * 4096 + 44 * 64 + 32.

(* [comment removed for export] *)
Record main_frame (sp0 : Z) (M : word -> option byte) : Prop := {
  mf_ra : cell M (sp0 - 56) 8 0x3f2a8;
  mf_s0 : cell M (sp0 - 64) 8 (sp0 + 8);       (* [comment removed for export] *)
  mf_s1 : cell M (sp0 - 72) 8 2;               (* [comment removed for export] *)
  mf_s2 : cell M (sp0 - 80) 8 0x1d24c;         (* [comment removed for export] *)
  mf_s3 : cell M (sp0 - 88) 8 (sp0 + 32);      (* [comment removed for export] *)
  mf_s4 : cell M (sp0 - 96) 8 0;
  mf_s5 : cell M (sp0 - 104) 8 0;
  mf_s6 : cell M (sp0 - 112) 8 0
}.

(* [comment removed for export] *)
Record world0 (area gm brkv mas tid : Z) (M : word -> option byte) : Prop := {
  (* [comment removed for export] *)
  w_secret  : cell M ctx_secret 8 0;
  w_init    : cell M ctx_init_done 4 1;
  w_ctr     : cell M ctx_mmap_counter 4 1;
  w_fmh     : cell M ctx_free_meta_head 8 0;
  w_am      : cell M ctx_avail_meta 8 (area + 64);
  w_amc     : cell M ctx_avail_meta_count 8 100;
  w_amac    : cell M ctx_avail_meta_area_count 8 0;
  w_mas     : cell M ctx_meta_alloc_shift 8 mas;
  w_mah     : cell M ctx_meta_area_head 8 area;
  w_mat     : cell M ctx_meta_area_tail 8 area;
  w_amas    : cell M ctx_avail_meta_areas 8 (area + 4096);
  w_active44: cell M (ctx_active 44) 8 (area + 24);
  w_usage44 : cell M (ctx_usage 44) 8 1;
  w_seq     : cell M ctx_seq 1 1;
  w_brk     : cell M ctx_brk 8 brkv;
     (* [comment removed for export] *)
  (* [comment removed for export] *)
  w_area_chk  : cell M area 8 0;
  w_area_next : cell M (area + 8) 8 0;
  w_area_ns   : cell M (area + 16) 8 101;
  w_slot0_prev: cell M (area + 24) 8 (area + 24);
  w_slot0_next: cell M (area + 32) 8 (area + 24);
  w_slot0_mem : cell M (area + 40) 8 gm;
  w_slot0_msk : cell M (area + 48) 8 0;          (* [comment removed for export] *)
  w_slot0_W   : cell M (area + 56) 8 W64K;
  w_area_rest : zero_bytes M (area + 64) (4096 - 64);   (* [comment removed for export] *)
  w_area_def  : forall i, 0 <= i < 4096 -> M (Z_to_bv 64 (area + i)) <> None;
  (* [comment removed for export] *)
  w_grp_meta  : cell M gm 8 (area + 24);
  w_grp_aidx  : cell M (gm + 8) 1 0;             (* [comment removed for export] *)
  w_grp_pad   : zero_bytes M (gm + 9) 4;          (* [comment removed for export] *)
  w_enframe   : enframe_post M 0 65536 69616 (gm + 16) 1;
  w_grp_tail  : zero_bytes M (gm + 69628) 4;     (* [comment removed for export] *)
  w_grp_def   : forall i, 0 <= i < 69632 -> M (Z_to_bv 64 (gm + i)) <> None;  (* [comment removed for export] *)
  (* [comment removed for export] *)
  w_area_al : area mod 4096 = 0;
  w_gm_al   : gm mod 4096 = 0;
  w_area_rng: 0x2000 <= area /\ area + 4096 <= 0x7fff7f800000;
  w_area_img: area + 4096 <= 0x10000 \/ 0x7f000 <= area;   (* [comment removed for export] *)
  w_gm_rng  : 0x7e000 <= gm /\ gm + 69632 <= 0x7fff7f800000;
  w_disj    : area + 4096 <= gm \/ gm + 69632 <= area;   (* [comment removed for export] *)
  w_brkv    : brkv = area + 4096 \/ brkv = 2 ^ 64 - 1;
  w_masv    : mas = 0 \/ mas = 1;
  (* [comment removed for export] *)
  w_tid     : cell M 0x5d020 4 tid;
  w_tidr    : 0 < tid < 2 ^ 22;
  w_errno   : exists e, 0 <= e < 2 ^ 32 /\ cell M 0x5d024 4 e;
  w_self    : cell M 0x5d000 8 0x5d000;
  w_canary  : cell M 0x7d330 8 0;
  w_pagesz  : cell M 0x7d380 8 4096;
  w_lock80  : cell M 0x7d3b8 8 0;
  (* [comment removed for export] *)
  w_img     : Forall (fun iv => img_clear M (fst iv) (snd iv)) img_clear_ivs
}.

(* [comment removed for export] *)
Definition world0_fp (area gm : Z) (i : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_world ()) "(5.(6.(7.=O1.)(8.O1.+1000.))(5.(6.(7.+10000.O1.)(8.O1.+7>000.))(5.(6.(7.O3.O1.)(8.O1.(9.O3.+1000.)))(5.(6.(7.O2.O1.)(8.O1.(9.O2.+20.)))(6.(7.(9.O2.+10020.)O1.)(8.O1.(9.O2.+11000.)))))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)



(* [comment removed for export] *)



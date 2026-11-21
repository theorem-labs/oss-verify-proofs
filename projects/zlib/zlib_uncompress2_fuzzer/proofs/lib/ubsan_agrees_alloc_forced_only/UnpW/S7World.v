(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import RunCtx. (* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.World Require Import SrcO_zlib_zlib_uncompress2_fuzzer_repro.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import PropExec CatExec StoreOk Frame MallocDefs. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW Require Import S7EnframeBase.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.
Import ListNotations.
Open Scope Z_scope.

Abbreviation RSEGS := SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments.

Lemma u64_lit : forall z, (0 <= z < 2 ^ 64)%Z -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. apply Z_to_bv_small. unfold bv_modulus. lia. Qed.

(* [comment removed for export] *)
Definition cell {RCa1 : RunCtx}  (M : word -> option byte) (a : Z) (n : nat) (v : Z) : Prop :=
  rdn (run_segments RSEGS rc_inp rc_sp rc_mb) M (Z_to_bv 64 a) n = Some (word_to_le_bytes n (Z_to_bv 64 v)).

(* [comment removed for export] *)
Definition zero_bytes (M : word -> option byte) (a n : Z) : Prop :=
  forall i, 0 <= i < n -> M (Z_to_bv 64 (a + i)) = Some (Z_to_bv 8 0).

(* [comment removed for export] *)
Definition img_clear (M : word -> option byte) (lo hi : Z) : Prop :=
  forall i, lo <= i < hi -> M (Z_to_bv 64 i) = None.

(* [comment removed for export] *)
Definition img_clear_ivs : list (Z * Z) :=
  [(0, 0x1000); (0x10000,0x22e70); (0x22e71,0x22eb9); (0x32eb9,0x72ef0); (0x72f24,0x72f70); (0x72f78,0x72f90);
   (0x72f98,0x72fb0); (0x72fc0,0x72fd0); (0x72fd8,0x92fe8); (0x93000,0x93228); (0x93230,0x93238); (0x93249,0x93250);
   (0x93258,0x93260); (0x93270,0x93278); (0x93280,0x932b0); (0x932b8,0x932c0); (0x93310,0x93470); (0x93478,0x935f0);
   (0x935f8,0x93650); (0x93651,0x93658); (0x93668,0x94000)].

(* [comment removed for export] *)
Definition CTX : Z := 0x932c0.
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
(* [comment removed for export] *)                    (* [comment removed for export] *)
(* [comment removed for export] *)                      (* [comment removed for export] *)
Definition ctx_seq : Z := CTX + 80 + 832.                          (* [comment removed for export] *)
Definition ctx_brk : Z := CTX + 80 + 840.                          (* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition W64K : Z := 17 * 4096 + 44 * 64 + 32.
(* [comment removed for export] *)

(* [comment removed for export] *)
Record main_frame {RCa1 : RunCtx}  (sp0 : Z) (M : word -> option byte) : Prop := {
  mf_ra : cell M (sp0 - 56) 8 0x18c6c;
  mf_s0 : cell M (sp0 - 64) 8 (sp0 + 8);       (* [comment removed for export] *)
  mf_s1 : cell M (sp0 - 72) 8 2;               (* [comment removed for export] *)
  mf_s2 : cell M (sp0 - 80) 8 0x148cc;         (* [comment removed for export] *)
  mf_s3 : cell M (sp0 - 88) 8 (sp0 + 32);      (* [comment removed for export] *)
  mf_s4 : cell M (sp0 - 96) 8 0;
  mf_s5 : cell M (sp0 - 104) 8 0;
  mf_s6 : cell M (sp0 - 112) 8 0;
  mf_s7 : cell M (sp0 - 120) 8 0
}.
Arguments Build_main_frame {RCa1}.  (* a worker (A1) tool *)

(* [comment removed for export] *)
Record world0 {RCa1 : RunCtx}  (sp0 area gm brkv mas tid can sec : Z) (M : word -> option byte) : Prop := {
  (* [comment removed for export] *)
  w_secret  : cell M ctx_secret 8 sec;
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
  w_area_chk  : cell M area 8 sec;
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
  w_sp0rng  : 0x7fff80000000 <= sp0 <= 0x800000000000;
  w_area_rng: 0x2000 <= area /\ area + 4096 <= sp0 - 8388608;
  w_area_img: area + 4096 <= 0x10000 \/ 0x95000 <= area;   (* [comment removed for export] *)
  w_gm_rng  : 0x94000 <= gm /\ gm + 69632 <= sp0 - 8388608;
  w_disj    : area + 4096 <= gm \/ gm + 69632 <= area;   (* [comment removed for export] *)
  w_brkv    : brkv = area + 4096 \/ brkv = 2 ^ 64 - 1;
  w_masv    : mas = 0 \/ mas = 1;
  (* [comment removed for export] *)
  w_tid     : cell M 0x72f18 4 tid;
  w_tidr    : 0 < tid < 2 ^ 22;
  w_errno   : exists e, 0 <= e < 2 ^ 32 /\ cell M 0x72f1c 4 e;
  w_self    : cell M 0x72ef8 8 0x72ef8;
  w_canary  : cell M 0x93228 8 can;
  w_pagesz  : cell M 0x93278 8 4096;
  (* [comment removed for export] *)
  w_img     : Forall (fun iv => img_clear M (fst iv) (snd iv)) img_clear_ivs
}.
Arguments Build_world0 {RCa1}.  (* a worker (A1) tool *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

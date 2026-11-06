(* Modified by Theorem Labs, 2026-10: proofs/libreac/fuzz_disco/lib/A/RT_gxa_mem_Tbl.v at 2d2ff01bb6f2 relocated to reac-pw/fuzz_rate's ASan image A: module paths changed; numerals by port_core 1e42da8952ec (ledger provenance/reloc/A-Snp.tsv); the cp_donor / dp_donor / dp_donor_value fields keep the donor walk's own source image's addresses (fuzz_reply.asan), the cp_target / dp_target fields and the checked words are reac-pw/fuzz_rate's; the target fields are named cp_target / dp_target / dp_target_value (disco's cp_disco / dp_disco / dp_disco_value) and FUZZ_RATE_ASAN_SHA256 is reac-pw/fuzz_rate.asan's pinned sha256 (disco's FUZZ_DISCO_ASAN_SHA256); every cp_size, cp_insns, cp_differing and fs_bytes is recomputed on fuzz_rate.asan (cp_differing: the instructions whose 4 or 2 bytes differ between the fuzz_reply.asan copy and rate's, the count that reproduces disco's 15 values on disco's image): eight cp_differing values differ from disco's (asan_memcpy 40, icpt_memset 23, icpt_memcpy 53, mem_to_shadow_4 10, mem_to_shadow_5 10, region_is_poisoned 20, asan_inited_fn 1, try_asan_init_from_rtl 1); disco's relocation-run counts MOVED_CODE_NUMERALS, MOVED_DATA_NUMERALS and KEPT_ADDRESS_SIZED_NUMERALS are left out (a count of disco's own relocation run, not a fact of rate's image; nothing uses them). *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RT_gxa_mem_Tbl.v at 71994ff034c7, derived by derive_y.py: addresses moved from reac-pw/fuzz_rate's asan image (image A) to its asan-ubsan image (image B), the image module Asan -> AsanUbsan; the Modified-by lines above describe how lib/A/RT_gxa_mem_Tbl.v was made and quote that file's image-A values; the code below carries image B's values.; image B's own quantities, recomputed on fuzz_rate.asan-ubsan: FUZZ_RATE_ASAN_SHA256 is renamed FUZZ_RATE_ASAN_UBSAN_SHA256 and holds image B's pinned sha256; cp_size / cp_insns / fs_bytes / fs_word are those of image B's same-named functions (each word-identical to image A's but for pc-relative fields); cp_differing against the fuzz_reply.asan copy, by the rule above, is 38 for asan_memcpy, 51 for icpt_memcpy and 14 for mem_to_shadow_3 (image A: 40, 53, 15), the others as image A's; the build-identity word of LLVMFuzzerTestOneInput (0x8076c) is 0xde010113. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU.Bz.Lib Require Import ImageA.
Require OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.GXA.CopyCall.
Require OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.GXA.SetCall.
Import ListNotations.
Open Scope Z_scope.

Module GXC := OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.GXA.CopyCall.
Module GXM := OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.GXA.SetCall.

Definition MC_TRAMP : Z := 0x518b4.
Definition MC_ICPT : Z := 0x52284.
Definition MS_TRAMP : Z := 0x518b0.
Definition MS_ICPT : Z := 0x51f94.

Definition DONOR_FUZZ_REPLY_ASAN_SHA256 : Z := 0x42c58610e125e0b47770217f7175ffe2f23ed5ee1399b3e81539eff364611d5a.
Definition FUZZ_RATE_ASAN_UBSAN_SHA256 : Z := 0xc30584a7214902c43e35abebe35194418b7fdefacb6e7ed16fe0492228ec1d14.

Record code_pair : Type := { cp_donor : Z; cp_target : Z; cp_size : Z; cp_insns : Z; cp_differing : Z }.

Definition CP_tramp_memset : code_pair :=
  {| cp_donor := 0x52720; cp_target := 0x518b0; cp_size := 0x4; cp_insns := 1; cp_differing := 1 |}.
Definition CP_tramp_memcpy : code_pair :=
  {| cp_donor := 0x52724; cp_target := 0x518b4; cp_size := 0x4; cp_insns := 1; cp_differing := 1 |}.
Definition CP_asan_memcpy : code_pair :=
  {| cp_donor := 0x52728; cp_target := 0x518b8; cp_size := 0x49c; cp_insns := 295; cp_differing := 38 |}.
Definition CP_asan_memset : code_pair :=
  {| cp_donor := 0x52bc4; cp_target := 0x51d54; cp_size := 0x240; cp_insns := 144; cp_differing := 18 |}.
Definition CP_icpt_memset : code_pair :=
  {| cp_donor := 0x53174; cp_target := 0x51f94; cp_size := 0x2f0; cp_insns := 188; cp_differing := 23 |}.
Definition CP_icpt_memcpy : code_pair :=
  {| cp_donor := 0x53464; cp_target := 0x52284; cp_size := 0x5f0; cp_insns := 380; cp_differing := 51 |}.
Definition CP_mem_to_shadow_3 : code_pair :=
  {| cp_donor := 0x53b40; cp_target := 0x52960; cp_size := 0x13c; cp_insns := 79; cp_differing := 14 |}.
Definition CP_mem_to_shadow_4 : code_pair :=
  {| cp_donor := 0x554d0; cp_target := 0x53fa8; cp_size := 0x13c; cp_insns := 79; cp_differing := 10 |}.
Definition CP_mem_to_shadow_5 : code_pair :=
  {| cp_donor := 0x5e454; cp_target := 0x5ce94; cp_size := 0x13c; cp_insns := 79; cp_differing := 10 |}.
Definition CP_region_is_poisoned : code_pair :=
  {| cp_donor := 0x5595c; cp_target := 0x54434; cp_size := 0x344; cp_insns := 209; cp_differing := 20 |}.
Definition CP_asan_inited_fn : code_pair :=
  {| cp_donor := 0x59ee0; cp_target := 0x589b8; cp_size := 0x18; cp_insns := 6; cp_differing := 1 |}.
Definition CP_try_asan_init_from_rtl : code_pair :=
  {| cp_donor := 0x5adf0; cp_target := 0x598c8; cp_size := 0xa0; cp_insns := 40; cp_differing := 1 |}.
Definition CP_mem_is_zero : code_pair :=
  {| cp_donor := 0x65734; cp_target := 0x64174; cp_size := 0xb4; cp_insns := 45; cp_differing := 5 |}.
Definition CP_musl_memcpy : code_pair :=
  {| cp_donor := 0x964cc; cp_target := 0x9525c; cp_size := 0x404; cp_insns := 257; cp_differing := 0 |}.
Definition CP_musl_memset : code_pair :=
  {| cp_donor := 0x96900; cp_target := 0x95660; cp_size := 0xf8; cp_insns := 62; cp_differing := 0 |}.

Definition code_pairs : list code_pair :=
  [CP_tramp_memset;
   CP_tramp_memcpy;
   CP_asan_memcpy;
   CP_asan_memset;
   CP_icpt_memset;
   CP_icpt_memcpy;
   CP_mem_to_shadow_3;
   CP_mem_to_shadow_4;
   CP_mem_to_shadow_5;
   CP_region_is_poisoned;
   CP_asan_inited_fn;
   CP_try_asan_init_from_rtl;
   CP_mem_is_zero;
   CP_musl_memcpy;
   CP_musl_memset].

Record data_pair : Type := { dp_donor : Z; dp_target : Z; dp_donor_value : option Z; dp_target_value : option Z }.

Definition DP_got_shadow_cell : data_pair :=
  {| dp_donor := 0x9d9d0; dp_target := 0x9c170; dp_donor_value := Some 0xa60b8; dp_target_value := Some 0xa4f38 |}.
Definition DP_got_replace_intrin_flag : data_pair :=
  {| dp_donor := 0x9e538; dp_target := 0x9ccd8; dp_donor_value := Some 0xa6d99; dp_target_value := Some 0xa5c19 |}.
Definition DP_real_memcpy : data_pair :=
  {| dp_donor := 0x9f868; dp_target := 0x9dfd0; dp_donor_value := Some 0x964cc; dp_target_value := Some 0x9525c |}.
Definition DP_real_memset : data_pair :=
  {| dp_donor := 0x9f870; dp_target := 0x9dfd8; dp_donor_value := Some 0x96900; dp_target_value := Some 0x95660 |}.
Definition DP_asan_inited : data_pair :=
  {| dp_donor := 0xa6d98; dp_target := 0xa5c18; dp_donor_value := None; dp_target_value := None |}.
Definition DP_k_high_mem_end : data_pair :=
  {| dp_donor := 0xa6da0; dp_target := 0xa5c20; dp_donor_value := None; dp_target_value := None |}.
Definition DP_k_mid_mem_beg : data_pair :=
  {| dp_donor := 0xa6da8; dp_target := 0xa5c28; dp_donor_value := None; dp_target_value := None |}.
Definition DP_k_mid_mem_end : data_pair :=
  {| dp_donor := 0xa6db0; dp_target := 0xa5c30; dp_donor_value := None; dp_target_value := None |}.

Definition data_pairs : list data_pair :=
  [DP_got_shadow_cell;
   DP_got_replace_intrin_flag;
   DP_real_memcpy;
   DP_real_memset;
   DP_asan_inited;
   DP_k_high_mem_end;
   DP_k_mid_mem_beg;
   DP_k_mid_mem_end].

Record frame_site : Type := { fs_pc : Z; fs_bytes : Z; fs_word : Z }.

Definition FR_icpt_memcpy : list frame_site :=
  [{| fs_pc := 0x52284; fs_bytes := 0x7f0; fs_word := 0x81010113 |};
   {| fs_pc := 0x522b4; fs_bytes := 0x80; fs_word := 0xf8010113 |}].
Definition FR_icpt_memset : list frame_site :=
  [{| fs_pc := 0x51f94; fs_bytes := 0x7f0; fs_word := 0x81010113 |};
   {| fs_pc := 0x51fbc; fs_bytes := 0x70; fs_word := 0xf9010113 |}].
Definition FR_region_is_poisoned : list frame_site :=
  [{| fs_pc := 0x54434; fs_bytes := 0x40; fs_word := 0xfc010113 |}].
Definition FR_mem_is_zero : list frame_site :=
  [{| fs_pc := 0x64174; fs_bytes := 0x10; fs_word := 0xff010113 |}].
Definition FR_musl_memcpy : list frame_site := [].
Definition FR_musl_memset : list frame_site := [].

Definition frame_bytes (l : list frame_site) : Z := fold_right (fun f s => fs_bytes f + s) 0 l.

Lemma copy_depth_measured :
  frame_bytes (FR_icpt_memcpy ++ FR_region_is_poisoned ++ FR_mem_is_zero ++ FR_musl_memcpy) = GXC.COPY_DEPTH.
Proof. reflexivity. Qed.

Lemma set_depth_measured :
  frame_bytes (FR_icpt_memset ++ FR_region_is_poisoned ++ FR_mem_is_zero ++ FR_musl_memset) = GXM.SET_DEPTH.
Proof. reflexivity. Qed.

Lemma entries_paired :
  cp_target CP_tramp_memcpy = MC_TRAMP /\ cp_target CP_icpt_memcpy = MC_ICPT /\
  cp_target CP_tramp_memset = MS_TRAMP /\ cp_target CP_icpt_memset = MS_ICPT /\
  option_map fs_pc (hd_error FR_icpt_memcpy) = Some MC_ICPT /\
  option_map fs_pc (hd_error FR_icpt_memset) = Some MS_ICPT /\
  dp_target_value DP_real_memcpy = Some (cp_target CP_musl_memcpy) /\
  dp_target_value DP_real_memset = Some (cp_target CP_musl_memset).
Proof. repeat split; reflexivity. Qed.

Definition MC_TRAMP_WORD : Z := 0x1d10006f.
Definition MS_TRAMP_WORD : Z := 0x6e40006f.

Definition jal_offset (w : Z) : Z :=
  let i := Z.land (Z.shiftr w 31) 1 * 2 ^ 20 + Z.land (Z.shiftr w 21) 0x3ff * 2
           + Z.land (Z.shiftr w 20) 1 * 2 ^ 11 + Z.land (Z.shiftr w 12) 0xff * 2 ^ 12 in
  if 2 ^ 20 <=? i then i - 2 ^ 21 else i.

Lemma tramps_jump :
  Z.land MC_TRAMP_WORD 0xfff = 0x6f /\ MC_TRAMP + jal_offset MC_TRAMP_WORD = MC_ICPT /\
  Z.land MS_TRAMP_WORD 0xfff = 0x6f /\ MS_TRAMP + jal_offset MS_TRAMP_WORD = MS_ICPT.
Proof. vm_compute. repeat split. Qed.


Lemma rt_gxa_mem_build_identity :
  fetch_word asegs (Z_to_bv 64 0x802cc) = Some (Z_to_bv 32 0xfb010113) /\
  fetch_word asegs (Z_to_bv 64 0x8076c) = Some (Z_to_bv 32 0xde010113) /\
  fetch_word asegs (Z_to_bv 64 MC_TRAMP) = Some (Z_to_bv 32 MC_TRAMP_WORD) /\
  fetch_word asegs (Z_to_bv 64 MS_TRAMP) = Some (Z_to_bv 32 MS_TRAMP_WORD) /\
  fetch_word asegs (Z_to_bv 64 0x52284) = Some (Z_to_bv 32 0x81010113) /\
  fetch_word asegs (Z_to_bv 64 0x522b4) = Some (Z_to_bv 32 0xf8010113) /\
  fetch_word asegs (Z_to_bv 64 0x51f94) = Some (Z_to_bv 32 0x81010113) /\
  fetch_word asegs (Z_to_bv 64 0x51fbc) = Some (Z_to_bv 32 0xf9010113) /\
  fetch_word asegs (Z_to_bv 64 0x54434) = Some (Z_to_bv 32 0xfc010113) /\
  fetch_word asegs (Z_to_bv 64 0x64174) = Some (Z_to_bv 32 0xff010113) /\
  fetch_word asegs (Z_to_bv 64 0x9525c) = Some (Z_to_bv 32 0x0035f693) /\
  fetch_word asegs (Z_to_bv 64 0x95660) = Some (Z_to_bv 32 0x0e060a63).
Proof. repeat split; vm_compute; reflexivity. Qed.

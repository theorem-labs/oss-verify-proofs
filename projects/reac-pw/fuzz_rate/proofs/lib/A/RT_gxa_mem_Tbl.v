(* Modified by Theorem Labs, 2026-10: proofs/libreac/fuzz_disco/lib/A/RT_gxa_mem_Tbl.v at 2d2ff01bb6f2 relocated to reac-pw/fuzz_rate's ASan image A: module paths changed; numerals by port_core 1e42da8952ec (ledger provenance/reloc/A-Snp.tsv); the cp_donor / dp_donor / dp_donor_value fields keep the donor walk's own source image's addresses (fuzz_reply.asan), the cp_target / dp_target fields and the checked words are reac-pw/fuzz_rate's; the target fields are named cp_target / dp_target / dp_target_value (disco's cp_disco / dp_disco / dp_disco_value) and FUZZ_RATE_ASAN_SHA256 is reac-pw/fuzz_rate.asan's pinned sha256 (disco's FUZZ_DISCO_ASAN_SHA256); every cp_size, cp_insns, cp_differing and fs_bytes is recomputed on fuzz_rate.asan (cp_differing: the instructions whose 4 or 2 bytes differ between the fuzz_reply.asan copy and rate's, the count that reproduces disco's 15 values on disco's image): eight cp_differing values differ from disco's (asan_memcpy 40, icpt_memset 23, icpt_memcpy 53, mem_to_shadow_4 10, mem_to_shadow_5 10, region_is_poisoned 20, asan_inited_fn 1, try_asan_init_from_rtl 1); disco's relocation-run counts MOVED_CODE_NUMERALS, MOVED_DATA_NUMERALS and KEPT_ADDRESS_SIZED_NUMERALS are left out (a count of disco's own relocation run, not a fact of rate's image; nothing uses them). *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A.Bz.Lib Require Import ImageA.
Require OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.GXA.CopyCall.
Require OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.GXA.SetCall.
Import ListNotations.
Open Scope Z_scope.

Module GXC := OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.GXA.CopyCall.
Module GXM := OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.GXA.SetCall.

Definition MC_TRAMP : Z := 0x5185c.
Definition MC_ICPT : Z := 0x5222c.
Definition MS_TRAMP : Z := 0x51858.
Definition MS_ICPT : Z := 0x51f3c.

Definition DONOR_FUZZ_REPLY_ASAN_SHA256 : Z := 0x42c58610e125e0b47770217f7175ffe2f23ed5ee1399b3e81539eff364611d5a.
Definition FUZZ_RATE_ASAN_SHA256 : Z := 0x22bc8613d780c9a99353dc86368f9401311ef5c8358882651217836298529b6a.

Record code_pair : Type := { cp_donor : Z; cp_target : Z; cp_size : Z; cp_insns : Z; cp_differing : Z }.

Definition CP_tramp_memset : code_pair :=
  {| cp_donor := 0x52720; cp_target := 0x51858; cp_size := 0x4; cp_insns := 1; cp_differing := 1 |}.
Definition CP_tramp_memcpy : code_pair :=
  {| cp_donor := 0x52724; cp_target := 0x5185c; cp_size := 0x4; cp_insns := 1; cp_differing := 1 |}.
Definition CP_asan_memcpy : code_pair :=
  {| cp_donor := 0x52728; cp_target := 0x51860; cp_size := 0x49c; cp_insns := 295; cp_differing := 40 |}.
Definition CP_asan_memset : code_pair :=
  {| cp_donor := 0x52bc4; cp_target := 0x51cfc; cp_size := 0x240; cp_insns := 144; cp_differing := 18 |}.
Definition CP_icpt_memset : code_pair :=
  {| cp_donor := 0x53174; cp_target := 0x51f3c; cp_size := 0x2f0; cp_insns := 188; cp_differing := 23 |}.
Definition CP_icpt_memcpy : code_pair :=
  {| cp_donor := 0x53464; cp_target := 0x5222c; cp_size := 0x5f0; cp_insns := 380; cp_differing := 53 |}.
Definition CP_mem_to_shadow_3 : code_pair :=
  {| cp_donor := 0x53b40; cp_target := 0x52908; cp_size := 0x13c; cp_insns := 79; cp_differing := 15 |}.
Definition CP_mem_to_shadow_4 : code_pair :=
  {| cp_donor := 0x554d0; cp_target := 0x53f50; cp_size := 0x13c; cp_insns := 79; cp_differing := 10 |}.
Definition CP_mem_to_shadow_5 : code_pair :=
  {| cp_donor := 0x5e454; cp_target := 0x5ce3c; cp_size := 0x13c; cp_insns := 79; cp_differing := 10 |}.
Definition CP_region_is_poisoned : code_pair :=
  {| cp_donor := 0x5595c; cp_target := 0x543dc; cp_size := 0x344; cp_insns := 209; cp_differing := 20 |}.
Definition CP_asan_inited_fn : code_pair :=
  {| cp_donor := 0x59ee0; cp_target := 0x58960; cp_size := 0x18; cp_insns := 6; cp_differing := 1 |}.
Definition CP_try_asan_init_from_rtl : code_pair :=
  {| cp_donor := 0x5adf0; cp_target := 0x59870; cp_size := 0xa0; cp_insns := 40; cp_differing := 1 |}.
Definition CP_mem_is_zero : code_pair :=
  {| cp_donor := 0x65734; cp_target := 0x6411c; cp_size := 0xb4; cp_insns := 45; cp_differing := 5 |}.
Definition CP_musl_memcpy : code_pair :=
  {| cp_donor := 0x964cc; cp_target := 0x94f54; cp_size := 0x404; cp_insns := 257; cp_differing := 0 |}.
Definition CP_musl_memset : code_pair :=
  {| cp_donor := 0x96900; cp_target := 0x95358; cp_size := 0xf8; cp_insns := 62; cp_differing := 0 |}.

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
  {| dp_donor := 0x9d9d0; dp_target := 0x9be70; dp_donor_value := Some 0xa60b8; dp_target_value := Some 0xa4c38 |}.
Definition DP_got_replace_intrin_flag : data_pair :=
  {| dp_donor := 0x9e538; dp_target := 0x9c9d8; dp_donor_value := Some 0xa6d99; dp_target_value := Some 0xa5919 |}.
Definition DP_real_memcpy : data_pair :=
  {| dp_donor := 0x9f868; dp_target := 0x9dcd0; dp_donor_value := Some 0x964cc; dp_target_value := Some 0x94f54 |}.
Definition DP_real_memset : data_pair :=
  {| dp_donor := 0x9f870; dp_target := 0x9dcd8; dp_donor_value := Some 0x96900; dp_target_value := Some 0x95358 |}.
Definition DP_asan_inited : data_pair :=
  {| dp_donor := 0xa6d98; dp_target := 0xa5918; dp_donor_value := None; dp_target_value := None |}.
Definition DP_k_high_mem_end : data_pair :=
  {| dp_donor := 0xa6da0; dp_target := 0xa5920; dp_donor_value := None; dp_target_value := None |}.
Definition DP_k_mid_mem_beg : data_pair :=
  {| dp_donor := 0xa6da8; dp_target := 0xa5928; dp_donor_value := None; dp_target_value := None |}.
Definition DP_k_mid_mem_end : data_pair :=
  {| dp_donor := 0xa6db0; dp_target := 0xa5930; dp_donor_value := None; dp_target_value := None |}.

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
  [{| fs_pc := 0x5222c; fs_bytes := 0x7f0; fs_word := 0x81010113 |};
   {| fs_pc := 0x5225c; fs_bytes := 0x80; fs_word := 0xf8010113 |}].
Definition FR_icpt_memset : list frame_site :=
  [{| fs_pc := 0x51f3c; fs_bytes := 0x7f0; fs_word := 0x81010113 |};
   {| fs_pc := 0x51f64; fs_bytes := 0x70; fs_word := 0xf9010113 |}].
Definition FR_region_is_poisoned : list frame_site :=
  [{| fs_pc := 0x543dc; fs_bytes := 0x40; fs_word := 0xfc010113 |}].
Definition FR_mem_is_zero : list frame_site :=
  [{| fs_pc := 0x6411c; fs_bytes := 0x10; fs_word := 0xff010113 |}].
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
  fetch_word asegs (Z_to_bv 64 0x80274) = Some (Z_to_bv 32 0xfb010113) /\
  fetch_word asegs (Z_to_bv 64 0x80714) = Some (Z_to_bv 32 0xe2010113) /\
  fetch_word asegs (Z_to_bv 64 MC_TRAMP) = Some (Z_to_bv 32 MC_TRAMP_WORD) /\
  fetch_word asegs (Z_to_bv 64 MS_TRAMP) = Some (Z_to_bv 32 MS_TRAMP_WORD) /\
  fetch_word asegs (Z_to_bv 64 0x5222c) = Some (Z_to_bv 32 0x81010113) /\
  fetch_word asegs (Z_to_bv 64 0x5225c) = Some (Z_to_bv 32 0xf8010113) /\
  fetch_word asegs (Z_to_bv 64 0x51f3c) = Some (Z_to_bv 32 0x81010113) /\
  fetch_word asegs (Z_to_bv 64 0x51f64) = Some (Z_to_bv 32 0xf9010113) /\
  fetch_word asegs (Z_to_bv 64 0x543dc) = Some (Z_to_bv 32 0xfc010113) /\
  fetch_word asegs (Z_to_bv 64 0x6411c) = Some (Z_to_bv 32 0xff010113) /\
  fetch_word asegs (Z_to_bv 64 0x94f54) = Some (Z_to_bv 32 0x0035f693) /\
  fetch_word asegs (Z_to_bv 64 0x95358) = Some (Z_to_bv 32 0x0e060a63).
Proof. repeat split; vm_compute; reflexivity. Qed.

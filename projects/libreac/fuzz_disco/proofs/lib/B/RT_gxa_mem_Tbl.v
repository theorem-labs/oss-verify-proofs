From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.B.Bz.Lib Require Import ImageA.
Require OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.GXA.CopyCall.
Require OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.GXA.SetCall.
Import ListNotations.
Open Scope Z_scope.

Module GXC := OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.GXA.CopyCall.
Module GXM := OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.GXA.SetCall.

Definition MC_TRAMP : Z := 0x52104.
Definition MC_ICPT : Z := 0x52ad4.
Definition MS_TRAMP : Z := 0x52100.
Definition MS_ICPT : Z := 0x527e4.

Definition DONOR_FUZZ_REPLY_ASAN_SHA256 : Z := 0x42c58610e125e0b47770217f7175ffe2f23ed5ee1399b3e81539eff364611d5a.
Definition FUZZ_DISCO_ASAN_UBSAN_SHA256 : Z := 0xcee6f04ad3d4928e242405689ae058bb9e8b6533000c90bde984a2f0d5ff5146.

Record code_pair : Type := { cp_donor : Z; cp_disco : Z; cp_size : Z; cp_insns : Z; cp_differing : Z }.

Definition CP_tramp_memset : code_pair :=
  {| cp_donor := 0x52720; cp_disco := 0x52100; cp_size := 0x4; cp_insns := 1; cp_differing := 1 |}.
Definition CP_tramp_memcpy : code_pair :=
  {| cp_donor := 0x52724; cp_disco := 0x52104; cp_size := 0x4; cp_insns := 1; cp_differing := 1 |}.
Definition CP_asan_memcpy : code_pair :=
  {| cp_donor := 0x52728; cp_disco := 0x52108; cp_size := 0x49c; cp_insns := 295; cp_differing := 38 |}.
Definition CP_asan_memset : code_pair :=
  {| cp_donor := 0x52bc4; cp_disco := 0x525a4; cp_size := 0x240; cp_insns := 144; cp_differing := 18 |}.
Definition CP_icpt_memset : code_pair :=
  {| cp_donor := 0x53174; cp_disco := 0x527e4; cp_size := 0x2f0; cp_insns := 188; cp_differing := 27 |}.
Definition CP_icpt_memcpy : code_pair :=
  {| cp_donor := 0x53464; cp_disco := 0x52ad4; cp_size := 0x5f0; cp_insns := 380; cp_differing := 58 |}.
Definition CP_mem_to_shadow_3 : code_pair :=
  {| cp_donor := 0x53b40; cp_disco := 0x531b0; cp_size := 0x13c; cp_insns := 79; cp_differing := 15 |}.
Definition CP_mem_to_shadow_4 : code_pair :=
  {| cp_donor := 0x554d0; cp_disco := 0x547f8; cp_size := 0x13c; cp_insns := 79; cp_differing := 14 |}.
Definition CP_mem_to_shadow_5 : code_pair :=
  {| cp_donor := 0x5e454; cp_disco := 0x5d6e4; cp_size := 0x13c; cp_insns := 79; cp_differing := 14 |}.
Definition CP_region_is_poisoned : code_pair :=
  {| cp_donor := 0x5595c; cp_disco := 0x54c84; cp_size := 0x344; cp_insns := 209; cp_differing := 29 |}.
Definition CP_asan_inited_fn : code_pair :=
  {| cp_donor := 0x59ee0; cp_disco := 0x59208; cp_size := 0x18; cp_insns := 6; cp_differing := 2 |}.
Definition CP_try_asan_init_from_rtl : code_pair :=
  {| cp_donor := 0x5adf0; cp_disco := 0x5a118; cp_size := 0xa0; cp_insns := 40; cp_differing := 2 |}.
Definition CP_mem_is_zero : code_pair :=
  {| cp_donor := 0x65734; cp_disco := 0x649c4; cp_size := 0xb4; cp_insns := 45; cp_differing := 5 |}.
Definition CP_musl_memcpy : code_pair :=
  {| cp_donor := 0x964cc; cp_disco := 0x99b10; cp_size := 0x404; cp_insns := 257; cp_differing := 0 |}.
Definition CP_musl_memset : code_pair :=
  {| cp_donor := 0x96900; cp_disco := 0x99f14; cp_size := 0xf8; cp_insns := 62; cp_differing := 0 |}.

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

Record data_pair : Type := { dp_donor : Z; dp_disco : Z; dp_donor_value : option Z; dp_disco_value : option Z }.

Definition DP_got_shadow_cell : data_pair :=
  {| dp_donor := 0x9d9d0; dp_disco := 0xa08b0; dp_donor_value := Some 0xa60b8; dp_disco_value := Some 0xa9478 |}.
Definition DP_got_replace_intrin_flag : data_pair :=
  {| dp_donor := 0x9e538; dp_disco := 0xa1418; dp_donor_value := Some 0xa6d99; dp_disco_value := Some 0xaa159 |}.
Definition DP_real_memcpy : data_pair :=
  {| dp_donor := 0x9f868; dp_disco := 0xa2710; dp_donor_value := Some 0x964cc; dp_disco_value := Some 0x99b10 |}.
Definition DP_real_memset : data_pair :=
  {| dp_donor := 0x9f870; dp_disco := 0xa2718; dp_donor_value := Some 0x96900; dp_disco_value := Some 0x99f14 |}.
Definition DP_asan_inited : data_pair :=
  {| dp_donor := 0xa6d98; dp_disco := 0xaa158; dp_donor_value := None; dp_disco_value := None |}.
Definition DP_k_high_mem_end : data_pair :=
  {| dp_donor := 0xa6da0; dp_disco := 0xaa160; dp_donor_value := None; dp_disco_value := None |}.
Definition DP_k_mid_mem_beg : data_pair :=
  {| dp_donor := 0xa6da8; dp_disco := 0xaa168; dp_donor_value := None; dp_disco_value := None |}.
Definition DP_k_mid_mem_end : data_pair :=
  {| dp_donor := 0xa6db0; dp_disco := 0xaa170; dp_donor_value := None; dp_disco_value := None |}.

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
  [{| fs_pc := 0x52ad4; fs_bytes := 0x7f0; fs_word := 0x81010113 |};
   {| fs_pc := 0x52b04; fs_bytes := 0x80; fs_word := 0xf8010113 |}].
Definition FR_icpt_memset : list frame_site :=
  [{| fs_pc := 0x527e4; fs_bytes := 0x7f0; fs_word := 0x81010113 |};
   {| fs_pc := 0x5280c; fs_bytes := 0x70; fs_word := 0xf9010113 |}].
Definition FR_region_is_poisoned : list frame_site :=
  [{| fs_pc := 0x54c84; fs_bytes := 0x40; fs_word := 0xfc010113 |}].
Definition FR_mem_is_zero : list frame_site :=
  [{| fs_pc := 0x649c4; fs_bytes := 0x10; fs_word := 0xff010113 |}].
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
  cp_disco CP_tramp_memcpy = MC_TRAMP /\ cp_disco CP_icpt_memcpy = MC_ICPT /\
  cp_disco CP_tramp_memset = MS_TRAMP /\ cp_disco CP_icpt_memset = MS_ICPT /\
  option_map fs_pc (hd_error FR_icpt_memcpy) = Some MC_ICPT /\
  option_map fs_pc (hd_error FR_icpt_memset) = Some MS_ICPT /\
  dp_disco_value DP_real_memcpy = Some (cp_disco CP_musl_memcpy) /\
  dp_disco_value DP_real_memset = Some (cp_disco CP_musl_memset).
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

Definition MOVED_CODE_NUMERALS : Z := 97.
Definition MOVED_DATA_NUMERALS : Z := 14.
Definition KEPT_ADDRESS_SIZED_NUMERALS : Z := 108.

Lemma rt_gxa_mem_build_identity :
  fetch_word asegs (Z_to_bv 64 0x80b1c) = Some (Z_to_bv 32 0xfb010113) /\
  fetch_word asegs (Z_to_bv 64 0x80fbc) = Some (Z_to_bv 32 0xdc010113) /\
  fetch_word asegs (Z_to_bv 64 MC_TRAMP) = Some (Z_to_bv 32 MC_TRAMP_WORD) /\
  fetch_word asegs (Z_to_bv 64 MS_TRAMP) = Some (Z_to_bv 32 MS_TRAMP_WORD) /\
  fetch_word asegs (Z_to_bv 64 0x52ad4) = Some (Z_to_bv 32 0x81010113) /\
  fetch_word asegs (Z_to_bv 64 0x52b04) = Some (Z_to_bv 32 0xf8010113) /\
  fetch_word asegs (Z_to_bv 64 0x527e4) = Some (Z_to_bv 32 0x81010113) /\
  fetch_word asegs (Z_to_bv 64 0x5280c) = Some (Z_to_bv 32 0xf9010113) /\
  fetch_word asegs (Z_to_bv 64 0x54c84) = Some (Z_to_bv 32 0xfc010113) /\
  fetch_word asegs (Z_to_bv 64 0x649c4) = Some (Z_to_bv 32 0xff010113) /\
  fetch_word asegs (Z_to_bv 64 0x99b10) = Some (Z_to_bv 32 0x0035f693) /\
  fetch_word asegs (Z_to_bv 64 0x99f14) = Some (Z_to_bv 32 0x0e060a63).
Proof. repeat split; vm_compute; reflexivity. Qed.

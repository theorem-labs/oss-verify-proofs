From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib Require Import Contract.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require Import
ManifestModel ManifestMem Ledger ManifestB names_c printf_facts_c.
Import ListNotations.
Local Open Scope Z_scope.

Definition CHECK_ROUND_TRIP : Z := 0x132f4.
Definition CRT_K : Z := 112 + (32 + NAMES_K).

Definition EMPTY_STR : Z := 0x102e7.
Definition FMT_TW : Z := 0x10344.
Definition FMT_TX : Z := 0x10298.
Definition FMT_T1 : Z := 0x1035d.
Definition FMT_T2 : Z := 0x1041d.
Definition FMT_T3 : Z := 0x103bf.
Definition FMT_T1X : Z := 0x10391.

Definition fmt_tw : list Z := [60; 37; 115; 62] ++ tail_lv2.
Definition fmt_tx : list Z := [60; 37; 115; 88; 62] ++ tail_lv2.
Definition fmt_t1 : list Z :=
  [64; 112; 114; 101; 102; 105; 120; 32; 112; 58; 32; 60; 37; 46; 42; 115; 62; 32; 46; 10; 112; 58; 37; 115]
  ++ tail_lv2.
Definition fmt_t2 : list Z :=
  [80; 82; 69; 70; 73; 88; 32; 112; 58; 32; 60; 37; 46; 42; 115; 62; 10; 112; 58; 37; 115] ++ tail_lv2.
Definition fmt_t3 : list Z :=
  [64; 112; 114; 101; 102; 105; 120; 32; 58; 32; 60; 37; 46; 42; 115; 62; 32; 46; 10; 58; 37; 115] ++ tail_lv2.
Definition fmt_t1x : list Z :=
  [64; 112; 114; 101; 102; 105; 120; 32; 112; 58; 32; 60; 37; 46; 42; 115; 62; 32; 46; 10; 112; 58; 37; 115; 88]
  ++ tail_lv2.

Definition crt_strings (m : word -> option byte) : Prop :=
  bytes_at rsegs m EMPTY_STR [Z_to_bv 8 0] /\
  bytes_at rsegs m FMT_TW (pf_bytes (fmt_tw ++ [0])) /\
  bytes_at rsegs m FMT_TX (pf_bytes (fmt_tx ++ [0])) /\
  bytes_at rsegs m FMT_T1 (pf_bytes (fmt_t1 ++ [0])) /\
  bytes_at rsegs m FMT_T2 (pf_bytes (fmt_t2 ++ [0])) /\
  bytes_at rsegs m FMT_T3 (pf_bytes (fmt_t3 ++ [0])) /\
  bytes_at rsegs m FMT_T1X (pf_bytes (fmt_t1x ++ [0])).

Fixpoint rt_used (u : list Z) (k fuel : nat) : nat :=
  match fuel with
  | O => O
  | S fuel' =>
      if (k <? length u)%nat && negb (byte_at u (k - 1) =? 62)
      then ((if plain_name (skipn k u) then 1 else 0) + rt_used u (S k) fuel')%nat
      else O
  end.

Definition rt_nk (u : list Z) : nat := rt_used u 1 (length u).

Definition rt_calls (u : list Z) : Z :=
  match u with
  | [] => 0
  | _ :: _ => 3 + 4 * Z.of_nat (rt_nk u)
  end.

Definition rt_peak (u : list Z) (live peak : Z) : Z :=
  match u with
  | [] => peak
  | _ :: _ => Z.max peak (live + Z.of_nat (length u) + 3)
  end.

Section K.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let segs := ms_segs B.
Let MR := aa_MR API.

Definition crt_post (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
    (u : list byte) (Lam : list (Z * Z)) (peak cnt : Z) (b : sbound) (c' : config) : Prop :=
  exists (fx' : FPState) L' A' regs' mem' md',
    c' = mkCfg (@mkst fx' regs' (getr regs 1) mem' (seg_rom segs)) md' /\
    frm_zero (@fp_csr fx') /\ st_init_done A' = true /\
    bpost B MR CRT_K stat_writes L A regs mem md L' A' regs' mem' md' /\
    (exists us', cstr_at mem' (bv_unsigned (getr regs 10)) u us') /\
    ledger B L' A' mem' Lam (rt_peak (zbytes u) (lsum Lam) peak) (cnt + rt_calls (zbytes u)) (2 ^ 64 - 1) /\
    res_ok_slots A' b.

Definition check_round_trip_contract : Prop :=
  forall L A regs mem md b (u us : list byte) Lam peak cnt fail,
    segs = rsegs ->
    call_pre_k B MR CRT_K L A regs mem md -> st_init_done A = true ->
    bv_unsigned (getr regs 2) <= TASK_SIZE ->
    frm_zero fp_csr ->
    ro_agree rsegs mem -> guard_cells B mem ->
    cstr_at mem (bv_unsigned (getr regs 10)) u us ->
    (exists a k, In (a, k) (blocks L A) /\ a <= bv_unsigned (getr regs 10) /\
       bv_unsigned (getr regs 10) + Z.of_nat (length u) + 1 <= a + k) ->
    (length u <= 255)%nat ->
    img_strings mem -> crt_strings mem ->
    ledger B L A mem Lam peak cnt fail -> quiet cnt fail 1019 ->
    res_ok_slots A b -> sb_live b + 2 <= sb_cap b <= CAPMAX -> 0 <= sb_bytes b ->
    sb_bytes b + (4 * Z.of_nat (length u) + 83) <= 2 ^ 40 ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 CHECK_ROUND_TRIP) mem (seg_rom segs)) md)
      (crt_post L A regs mem md u Lam peak cnt b).

End K.

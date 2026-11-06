(* fm program part, statement base: fm.asan addresses, the per-function stack/event/live constants, the user-poison
   wrappers over the donor's afn_pre / apost_base, C-string premises, fm's static allocation counters (fuzz/alloc.c).
   Definitions only. Design: a Theorem Labs lane's design/HARNESS.md. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YK11 YK0s YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YC20 YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison FMPstat.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require ManifestModel.
Import ListNotations.
Local Open Scope Z_scope.

(* ---- fm.asan addresses (MEASURED from the unstripped twin, identical loadable bytes) ---- *)
(* harness entry and its driver context: target_run's call `jal` at 0x80814 *)
Definition FM_LLVMF : Z := 0x8091c.
Definition FM_RA_LLVMF : Z := 0x80818.
Definition FM_EMPTY : Z := 0x5d43e0.
(* relro: .data.rel.ro start .. .got end (donor 0x9da38 .. 0x9eca8) *)
Definition FM_RLO : Z := 0x99450.
Definition FM_RHI : Z := 0x9a6a8.
(* the target functions *)
Definition A_check_no_overread : Z := 0x80b20.
Definition A_check_bounded_alloc : Z := 0x80db4.
Definition A_check_as_written : Z := 0x80dd8.
Definition A_check_reject_clean : Z := 0x80e14.
Definition A_check_reject_clean_starved : Z := 0x80e44.
Definition A_check_round_trip : Z := 0x80ea0.
Definition A_expected : Z := 0x81130.
Definition A_plain : Z := 0x81778.
Definition A_as_ruled : Z := 0x81880.
Definition A_fuzz_malloc : Z := 0x8193c.
Definition A_fuzz_free : Z := 0x81a78.
Definition A_fuzz_alloc_live : Z := 0x81b94.
Definition A_fuzz_alloc_peak : Z := 0x81ba0.
Definition A_fuzz_alloc_peak_reset : Z := 0x81bac.
Definition A_fuzz_alloc_fail : Z := 0x81bc0.
Definition A_names : Z := 0x81be4.
Definition A_readings : Z := 0x81c04.
Definition A_has_prefixed : Z := 0x82130.
Definition A_name_char : Z := 0x822c4.
(* runtime entries the target code calls (interceptor trampolines `__wrap_*`, musl isalnum, asan entry points) *)
Definition PC_strlen : Z := 0x412c8.
Definition PC_strncmp : Z := 0x412d4.
Definition PC_strncasecmp : Z := 0x412d8.
Definition PC_strstr : Z := 0x412dc.
Definition PC_strchr : Z := 0x412e0.
Definition PC_bcmp : Z := 0x412e8.
Definition PC_memchr : Z := 0x412ec.
Definition PC_snprintf : Z := 0x41314.
Definition PC_isalnum : Z := 0x88350.
Definition PC_poison : Z := 0x54294.
Definition PC_unpoison : Z := 0x54434.
(* fuzz/alloc.c statics: non-owned program statics (in the journal footprint FM_PSTAT_FP of whoever writes them) *)
Definition G_FAIL : Z := 0x9df80.
Definition G_LIVE : Z := 0x5d4400.
Definition G_PEAK : Z := 0x5d4420.
Definition G_COUNT : Z := 0x5d4440.
(* stack protector cells musl's printf_core reads (donor A/AE2d.v:35-36 A_GOT_canary / A_canary at cgif_file addresses):
   the .got slot and __stack_chk_guard *)
Definition FM_GOT_canary : Z := 0x9a638.
Definition FM_canary : Z := 0x5f4db0.
(* fm's seven snprintf formats (.rodata, registered asan globals with redzones; fm-fn-measure.md section 4) *)
Definition FMT_whole : Z := 0x20fa0.     (* "<%s>", lv2_locate.c:97 *)
Definition FMT_tw : Z := 0x20d60.        (* fuzz_manifest.c:270 *)
Definition FMT_tx : Z := 0x20da0.        (* :272 *)
Definition FMT_t1 : Z := 0x20de0.        (* :280 *)
Definition FMT_t2 : Z := 0x20e40.        (* :282 *)
Definition FMT_t3 : Z := 0x20ea0.        (* :284 *)
Definition FMT_t1x : Z := 0x20f00.       (* :286 *)
Definition STR_empty : Z := 0x20d40.     (* "" passed to the reader, fuzz_manifest.c:262 *)

(* the journal footprint of fuzz/alloc.c's statics is FM_PSTAT_FP of lib/A/FMPstat.v (Reloc.JournalFP; the ajournal
   image clause admits a write to an image byte inside FP): a function that writes them, or calls one that does, names
   it in its FP *)

(* ---- program constants ---- *)
Definition SIZE_MAXZ : Z := 2 ^ 64 - 1.
Definition HEAD : Z := 16.
(* MANIFEST_MAX, fuzz_manifest.c:44 *)
Definition MANIFEST_MAX : Z := 4 * 2 ^ 20.
(* reader allocations (fuzz_malloc calls) one LLVMFuzzerTestOneInput call makes, at most: check_no_overread 2, the
   named call 1, the starved call 1, check_round_trip rt_calls u <= 3 + 4 * 254 (fuzz_manifest.c:262-289); 1027 is the
   bound fm's plain proof uses (lib/Prog/slot.v:98) and covers 1023. *)
Definition CNT_LIB : Z := 1027.

(* ---- stack each function's walk may use below its entry sp (afn_pre STK; donor TNEWGIF_STK style:
   own frame + the most any callee or runtime call needs) ---- *)
(* runtime calls: what each runtime contract (FMH_Rt.v) asks below the call's sp *)
Definition STK_RT_STR : Z := 2 * ESTACK.      (* strlen, strchr, strncmp, strncasecmp, memchr (two Theorem Labs lanes) *)
Definition STK_RT_ISALNUM : Z := ESTACK.      (* ecall_pre's ESTACK window (YG0d.v:281-282), G2 *)
Definition STK_RT_STRSTR : Z := 2 * ESTACK.
Definition STK_RT_PRINTF : Z := 3 * ESTACK.   (* a Theorem Labs lane: snprintf .. printf_core + the strnlen interceptor = 11712 *)
Definition STK_RT_BCMP : Z := 2 * ESTACK.     (* donor abcmp_realizes, YG0d.v:352-355 *)
Definition STK_RT_POISON : Z := 64.           (* design/POISON.md section 7 *)
(* own frames: MEASURED (first `addi sp, sp, -N`); 0 for the four leaf counters *)
Definition STK_name_char : Z := 16 + STK_RT_ISALNUM.
Definition STK_has_prefixed : Z := 112 + Z.max STK_RT_STRSTR (Z.max STK_RT_STR STK_name_char).
Definition STK_fuzz_alloc : Z := 16.
Definition STK_fuzz_malloc : Z := 32 + Z.max ASTACK STK_RT_POISON.
Definition STK_fuzz_free : Z := 32 + Z.max ASTACK STK_RT_POISON.
Definition STK_readings : Z :=
  208 + Z.max STK_fuzz_malloc (Z.max STK_fuzz_free (Z.max STK_RT_PRINTF (Z.max STK_RT_STRSTR
    (Z.max STK_RT_STR (Z.max STK_RT_ISALNUM STK_has_prefixed))))).
Definition STK_names : Z := 16 + STK_readings.
Definition STK_plain : Z := 32 + STK_RT_STR.
Definition STK_expected : Z := 208 + Z.max STK_RT_STR (Z.max STK_RT_BCMP STK_plain).
Definition STK_as_ruled : Z := 32 + Z.max STK_names STK_expected.
Definition STK_check_bounded_alloc : Z := 16.
Definition STK_check_as_written : Z := 16 + STK_expected.
Definition STK_check_reject_clean : Z := 16 + STK_fuzz_alloc.
Definition STK_check_reject_clean_starved : Z := 32 + Z.max STK_fuzz_alloc (Z.max STK_names STK_check_reject_clean).
Definition STK_check_no_overread : Z := 96 + Z.max ASTACK (Z.max ESTACK STK_names).
Definition STK_check_round_trip : Z :=
  112 + Z.max ASTACK (Z.max STK_RT_STR (Z.max STK_RT_PRINTF (Z.max STK_names (Z.max STK_as_ruled STK_plain)))).

(* ---- allocator events (ticks: one per malloc, one per free, YG00.v:233, :411, :540) each function makes, at most ---- *)
Definition EV_names : Z := 2.                                  (* malloc + free of `whole`, lv2_locate.c:94, :99 *)
Definition EV_as_ruled : Z := EV_names.
Definition EV_check_no_overread : Z := 4 + 4 + 2 * EV_names.    (* 4 copies, 4 frees, 2 reader calls *)
Definition EV_check_reject_clean_starved : Z := EV_names.      (* the bound names_spec gives; really 0 (G5) *)
Definition EV_check_round_trip : Z := 2 + (3 + 4 * 254) * EV_names.
(* LLVMFuzzerTestOneInput: 2 copies + 2 frees + the rest = 2060 <= EV_LIB = 2100 (lib/A/ACfn.v; a Theorem Labs lane ruling, EV_MAX
   11776: 4 * 2100 + 3 <= 11776) *)
Definition EV_LLVMF : Z := 4 + EV_check_no_overread + EV_names + EV_check_reject_clean_starved + EV_check_round_trip.

(* ---- live bytes each function may add (blocks_bytes S + LIVE_F <= LIVE_MAX; donor LIVE_NEWGIF style) ---- *)
Definition LIVE_names : Z := 2 ^ 9.                 (* uri_len + 3 + HEAD <= 274 *)
Definition LIVE_as_ruled : Z := LIVE_names.
Definition LIVE_check_no_overread : Z := 2 ^ 24.    (* 2 (un + 18) + 2 (tn + 18) + a reader block, tn <= 2^22 *)
Definition LIVE_check_round_trip : Z := 2 ^ 11.     (* 3 n + 64 + a reader block, n <= 255 *)
Definition LIVE_LLVMF : Z := 2 ^ 25.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* ---- the user-poison wrappers (design/POISON.md section 8): U = [] converts to the donor's form ---- *)
Definition afn_preU (STK : Z) (ly : alayout) (S : astate) (U : list (Z * Z)) (W : world segs) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) (ch : list (Z * Z * Z)) : Prop :=
  afn_pre segs B STK ly S W regs (unpoison U mem) md ch /\ upoison_ok B ly S U /\ upoisoned segs W mem U.

Definition apost_baseU (STK : Z) (FP : list (Z * Z)) (regs : bvmap 5 word) ly S W mem md (k : Z) (U U' : list (Z * Z))
  (Q : alayout -> astate -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
  : world segs -> config -> Prop :=
  fun W' c' => exists ly' S' regs' mem' md',
    c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
    ajournal segs B STK (spZ regs) FP ly S W (unpoison U mem) md [] ly' S' W' (unpoison U' mem') md' k /\
    upoison_ok B ly' S' U' /\ upoisoned segs W' mem' U' /\
    aregs_preserved regs regs' /\ Q ly' S' W' regs' mem' md'.

(* ecall_pre (YG0d.v:277) with STK bytes of present stack, as abcmp_realizes asks (YG0d.v:355), and the stack above
   alloc_ceiling (astk_ok, YCbq.v:333), so a string below alloc_ceiling (cstr_ok) is outside the callee's window *)
Definition ecall_pre_k (STK : Z) (ly : alayout) (S : astate) (W : world segs) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) : Prop :=
  ecall_pre segs B ly S W regs mem md /\ alloc_ceiling <= ly_stk_lo ly /\ ly_stk_lo ly + STK <= spZ regs /\
  (forall a, spZ regs - STK <= a < spZ regs -> apresent (w_H W) mem a).

(* Poison's ecall_preU (A/FMupoison.v) with STK bytes of stack *)
Definition ecall_preU_k (STK : Z) (ly : alayout) (S : astate) (U : list (Z * Z)) (W : world segs)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop :=
  ecall_preU segs B ly S U W regs mem md /\ alloc_ceiling <= ly_stk_lo ly /\ ly_stk_lo ly + STK <= spZ regs /\
  (forall a, spZ regs - STK <= a < spZ regs -> apresent (w_H W) mem a).

(* ---- C strings ---- *)
(* the bytes l (no NUL) then a NUL at p, as the walk reads them *)
Definition cstr (W : world segs) (mem : word -> option byte) (p : Z) (l : list Z) : Prop :=
  garr8 segs (rdW W mem) p (l ++ [0]) /\ Forall (fun c => c <> 0) l.
(* what a runtime string reader needs of it: below the stack, shorter than 2^32 (donor k + 1 < 2^32, YG0d.v:407), its word reads inside one memory band
   (amem_range over len + 8; the interceptors' range check region_in_mem, a Theorem Labs lane), every byte up to the NUL addressable
   (the interceptor's range check), and the rest of the 8-byte word holding the NUL visible (musl's word reads; donor
   astrnlen_realizes, YG0d.v:411) *)
Definition cstr_ok (W : world segs) (mem : word -> option byte) (p : Z) (l : list Z) : Prop :=
  cstr W mem p l /\ 4096 <= p /\ p + Z.of_nat (length l) + 8 <= alloc_ceiling /\ Z.of_nat (length l) + 1 < 2 ^ 32 /\
  amem_range p (Z.of_nat (length l) + 8) /\
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF p (Z.of_nat (length l) + 1) /\
  shadow_hull_vis (aview segs (w_H W) mem) p (Z.of_nat (length l) + 1) /\
  (forall a, p + Z.of_nat (length l) < a < p + Z.of_nat (length l) - (p + Z.of_nat (length l)) mod 8 + 8 ->
     aview segs (w_H W) mem a <> None).
(* a byte window [p, p + n) of a C string's bytes, each visible *)
Definition bytes_at (W : world segs) (mem : word -> option byte) (p : Z) (l : list Z) : Prop :=
  garr8 segs (rdW W mem) p l.
(* a destination the walk may write n bytes at (donor dest_ok, YG0d.v:311, with an STK window) *)
Definition wdest_ok (STK : Z) (ly : alayout) (S : astate) (W : world segs) (regs : bvmap 5 word)
  (mem : word -> option byte) (d n : Z) : Prop :=
  0 <= d /\ d + n <= alloc_ceiling /\ amem_range d n /\
  (forall a, d <= a < d + n -> writable_at segs (rdW W mem) a /\ ~ aowned B ly S a /\ ~ (spZ regs - STK <= a < spZ regs)) /\
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF d n /\ (0 < n -> shadow_hull_vis (aview segs (w_H W) mem) d n).

(* ---- fuzz/alloc.c's statics (alloc.c:28): g_live, g_peak, g_count, g_fail_at; live, peak and count stay below 2^33
   (< alloc_ceiling), so a callee's afn_pre finds an empty frame chain when s0 holds one of them (G5) ---- *)
Definition fm_glob (W : world segs) (mem : word -> option byte) (live peak cnt fail : Z) : Prop :=
  val_mem segs (rdW W mem) G_LIVE 8 live /\ val_mem segs (rdW W mem) G_PEAK 8 peak /\
  val_mem segs (rdW W mem) G_COUNT 8 cnt /\ val_mem segs (rdW W mem) G_FAIL 8 fail /\
  0 <= live <= peak /\ peak < 2 ^ 33 /\ 0 <= cnt < 2 ^ 33 /\ 0 <= fail < 2 ^ 64.
(* the harness invariant: no reader allocation is set to fail (g_fail_at = SIZE_MAX), g_live = live *)
Definition fm_stat (W : world segs) (mem : word -> option byte) (live cnt : Z) : Prop :=
  exists peak, fm_glob W mem live peak cnt SIZE_MAXZ.
(* a reader block (fuzz/alloc.c own): the asan block (p - 16, n + 16) is live, its head holds n, and the 16-byte head is
   user-poisoned (U = [(p - 16, 16)]); n > 0 so the granule after the head is in the block, as Poison's
   apoison16/aunpoison16_realizes ask (fm's only fuzz_malloc call asks uri_len + 3 >= 4 bytes, G1) *)
Definition fm_rblock (ly : alayout) (S : astate) (W : world segs) (mem : word -> option byte) (p n : Z) : Prop :=
  In (p - HEAD, n + HEAD) (ablocks B ly S) /\ p mod 16 = 0 /\ 0 < n /\
  val_mem segs (rdW W mem) (p - HEAD) 8 n.

(* the shadow of the stack reads 0. AR gives it: ARm's am_zshadow (YG0n.v:217) covers zero_shadow_ranges, whose head is
   the stack (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly) (YG0n.v:187-190); readings' `++*readings` check (names' stack
   slot) uses it. Not a contract premise: derive it from AR where needed (G3, G5). *)
Definition stk_sh0 (W : world segs) (mem : word -> option byte) (lo hi : Z) : Prop :=
  forall a, lo <= a < hi -> aview segs (w_H W) mem (shadow_addr a) = Some 0.

(* the non-owned part of the donor's rom_view (YG0d.v:382): every read-only byte that is not a runtime-owned static and
   not errno reads as the image byte. arodata_okP gives it at every state; rom_view itself is not provable for fm, whose
   .rodata global redzones are owned statics (A/AF0m.v:557) that no AR clause pins (Integrate). The runtime walks read
   only non-owned read-only bytes (musl's word constants, the formats). *)
Definition rom_viewN (W : world segs) (mem : word -> option byte) : Prop :=
  forall a, in_rom segs a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  aview segs (w_H W) mem a = option_map (fun b : byte => bv_unsigned b) (seg_rom segs (Z_to_bv 64 a)).

(* the owned part: every read-only byte that is a runtime-owned static (fm's .rodata global redzones and the runtime's
   read-only cells, A/AF0m.v:555-559) reads as the image byte. A runtime word read of a read-only string's NUL word
   reaches a redzone; the clean-memory transfer of a Theorem Labs lane's / a Theorem Labs lane's walks needs these bytes (a Theorem Labs lane). Source: AR's
   constant cells, once Tfib_const pins every owned read-only byte to its image value (Reloc); the final instance
   proves it inside fm_img_facts. *)
Definition rom_viewO (W : world segs) (mem : word -> option byte) : Prop :=
  forall a, in_rom segs a -> Exists (in_zr a) (as_owned_static B) ->
  aview segs (w_H W) mem a = option_map (fun b : byte => bv_unsigned b) (seg_rom segs (Z_to_bv 64 a)).

(* where a string the caller keeps across a program call lives: inside a live block's requested bytes, or in read-only
   image bytes that are not runtime-owned (fm plain readings_c.v:55-56 str_home). A callee's ajournal keeps both
   (blocks live at both ends, non-owned image bytes); cstr_ok alone does not say where the bytes are (G3, G5). *)
Definition str_homeA (ly : alayout) (S : astate) (p n : Z) : Prop :=
  (exists b m, In (b, m) (ablocks B ly S) /\ b <= p /\ p + n <= b + m) \/
  (forall a, p <= a < p + n -> in_roP segs FM_RLO FM_RHI a /\ ~ Exists (in_zr a) (as_owned_static B) /\
     ~ (as_errno B <= a < as_errno B + 4)).
End c.

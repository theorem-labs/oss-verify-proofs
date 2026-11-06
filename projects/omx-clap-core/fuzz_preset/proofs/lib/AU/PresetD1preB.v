(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: GENERATED from lib/A/PresetD1preA.v (lane CwPreA, a working branch a9e03801db9b) by port/a2b.py (sha256 e4f47803449f38c2) with its measured literal map (a table literal in code is written as its image-B cell name from lib/Reusable/YImgCellsB.v) and --map 0x10000=0x10000 0x20e00=0x20e00 0x20f40=0x20f40 (image B's first zero-shadow range is also (YImgTop.IMG_LO, 0x20f40 - YImgTop.IMG_LO), lib/Reusable/YF0m.v Tfib_zero_shadow). No hand edit. PENDING YF0m (over ARcf); the B core closure is relocB 2e00af38a8f4. *)
(* Modified by Theorem Labs, 2026-10: for omx-clap-core/fuzz_preset (asan-ubsan image), the driver's pre-loop leaves and
   interceptor sites of the closed ASan-side walk, restated over the second allocator instance ARcf
   (lib/Reusable/YG0ncf.v), which holds from the allocator's initial state on (the switch from cgif's AR is at
   init_state, a Theorem Labs lane with a Theorem Labs lane, 2026-10-28 22:44Z). Made from proofs/cgif/cgif_file_fuzzer/lib, here as
   relocated by the core in lib/Reusable:
     YD1v.v:117-130 cannot_open_tfa, :230-243 malloc_site_tfa, :267-272 drv_epre, :273-288 memcpy_site_tfa,
     :291-302 read_check_tfa, :315-328 rderr_leaf_tfa, :329-339 refused_leaf_tfa;
     YD1i.v:18-31 aread_check_stmt;
     YD1w.v:52-58 short_leaf_tfa, :59-65 overrun_leaf_tfa;
     YD1x.v:41-46 icpt_pre, :47-56 icpt_post, :57-68 fwrite_site_tfa, :69-82 fprintf_s_site_tfa, :83-92 refused_site_tfa;
     YD27.v:568-576 the statement of tfib_usage (named usage_tfa_cf here: the donor states it inline);
   and the statements of the results YD1n.v:24 tfib_malloc_site, YD1i.v:105 tfib_memcpy_site, :111 tfib_read_check,
   YD27.v:405 tfib_rderr_leaf, :411 tfib_refused_leaf, :465 tfib_cannot_open, :568 tfib_usage, :862 tfib_short_leaf,
   :870 tfib_overrun_leaf. This file holds STATEMENTS only; the proofs are in PresetD1preBPf.v. Its twin for the
   asan-ubsan image is lib/AU/PresetD1preB.v (lane CwPreB).
   Names: a predicate is the donor's + `_cf`; a result is the donor lemma's + `_cf_B`, proved as <result>_holds.
   Changes from the donor, the same in every item:
   (1) cgif's AR is ARcf at the ghost set Hp = [] (no hidden head exists before the first harness call); cgif's
       acall_post / ecall_pre are acall_post_cf / ecall_pre_cf (lib/Reusable/YG0dcf.v); the read-check routine's
       realizer aread_check_stmt_cf is stated at every Hp, as a8's realizers are;
   (2) cgif's event premise `st_nev S < EV_MAX` is dropped everywhere: the cf instance has no event cap;
   (3) the malloc site is over malloc_cf (YG00cf.v) and its continuation covers EVERY outcome of the call, the
       class-full PNull arm included (a8's malloc_leaf_cf, YG0dcf.v): cgif's no-NULL fact came from its event
       regime, which the cf instance does not have. The continuation receives `gflag tr = true`, so a caller
       that needs a block refutes PNull with a8's malloc_cf_success_of_room (YGcfPath.v:544) from its own room
       fact, and a caller on the driver's OOM arm walks it. This CARRIES a8's ml_malloc_ns_cf NULL arm
       (a Theorem Labs lane the internal file real-edits.md item 1) to the caller; nothing here discharges it;
  (4) the pre of the malloc site is lane CwSites' drv_pre_cf (lib/AU/PresetD1sitesB.v: ARcf .. [], qtight and the
      non-primary room NP S); its one-call ROOM_cf S (for a8's malloc_ok_cf) comes from the interface's PCB.iface_room_np_tail NP,
      a premise of tfib_malloc_site_cf_B. The tail of the short / overrun leaves is CwSites' tail_at_pinv_B (ARcf ..
      [], NP S, drv_minv_cf, PINV in place of cgif's FINV); no headroom number occurs;
   (5) the site premises of the results are this file's _cf sites and CwSites' exit_site_cf / free_site_cf.
   No cgif output-file obligation (A_WB, A_TRAILER, A_PATH) and no FINV / astdio_env occurs in this file.
   Interceptor sites (YD1x): every one EXISTS in preset's driver `main` (asan-ubsan image f0d2e8d4, unstripped): the
   fwrite site serves the short / overrun / out-of-memory diagnostics, the fprintf site the cannot-open,
   read-error, refused and usage diagnostics; none serves an output file, so none is dropped.
   PROVISIONAL literals (no generated name exists; the core's relocated values, lib/Reusable/YD1v.v, YD1x.v):
     0x1d84b / 0x1d860 / 0x158e3 / 0x197b6 the format strings "cli: cannot open %s\n", "cli: read error on %s\n",
     "usage: %s INPUT\n", "cli: input >= %u bytes, refused\n"; 67108864 the refused bound (`lui a2,0x4000`);
     0x81490 the return address after main's fprintf call; 0x42e40 __wrap_fprintf (A_icpt_fprintf);
     0xa6e68 __stderr_FILE (F_STDERR_LO); 0x10578 / 0x1ce6b / 0x1ce80 / 0x20cc8 the .rodata read window of the
     fwrite site (YE3i.v's image chunks).
   MEMNORM KEEPS (lane MnPrefix, a Theorem Labs lane, 2026-10-29; the read loop carries memnorm of the full overlay to the loop
   head): memcpy_site_tfa_cf's post ends with `memnorm mem -> memnorm mem'`, and tfib_memcpy_site_cf_B takes the
   memcpy text in a Theorem Labs lane's keep form YGcallMxmn.aintrin_realizes_xm (as CwSites' printf results do). The
   malloc site takes the malloc row in its keep form YGcfMallocComposeKeep.amalloc_realizes_cf_keep, and its
   continuation the keep leaf malloc_leaf_cf_keep (the layer's malloc_leaf_cf with the keep at its end configuration):
   since field round 3 part 3c the layer's malloc_leaf_cf itself has no keep. read_check_tfa_cf's post ends with
   the same keep, and so does its realizer aread_check_stmt_cf's post (in place, the form of the keep realizers):
   OPEN for that realizer's row owner; until then the driver's ARDCHK premise carries it.
   Rule 24: no function is proved here (composition / driver layer of a port). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.omx_clap_core.fuzz_preset.images Require Import AsanUbsan.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK00 YK0s YK15 YK18 YP0n
YM02 YP0m YP09 YP0l YP06 YP08 YP03 YN3q YN3v YI00 YI16 YK04 YA0i YA0n YA0e YG00 YG0a YG01 YG0k YG0f YG0v YG0n
YG0d YCe5 YL02.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YF0m YD2j YD2i YD1t YD20
YD1v YD2h YD2f YD1w YD1x.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO05 YO09 YO06 YO01 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm YGcallMxmn YGcfMallocComposeKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YGcfNames YG01cf YG00cf YG0ncf YG0dcf YG0d2cf YGcfTok YGcfRoomPre.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import PresetD1sitesB.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.PresetCfnB.
Module PCB := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.PresetCfnB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section S.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
(* No N_LLVMF and no headroom number (resume ROOM change, owner ruling 2026-10-29): a driver state carries the
   interface's non-primary room NP S (CwSites' drv_pre_cf / tail_at_pinv_B, lib/AU/PresetD1sitesB.v; NP is the
   interface's Section Variable iface_room_np, lib/AU/PresetCfnB.v). The malloc site takes its one-call ROOM_cf S from
   the interface's law PCB.iface_room_np_tail NP (PresetCfnB.v:460), a premise of its result. *)
Variable B : asyms.
Variable NP : astate -> Prop.
Variable est : (word -> bool) -> (word -> option byte) -> Prop.
#[local] Notation ELV sp a0 p inp xw xd := (YP08.E0 sp [a0; p] (in_envp inp) xw xd).

(* ---------------------------------------------------------------------- *)
(* 1. The malloc site (MSITE). Donor: YD1v.v:230-243. *)
Definition malloc_site_tfa_cf : Prop :=
forall (ly : alayout) (S : astate) (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
(n : Z) (KB : TSet),
drv_pre_cf B NP ly S W regs mem md ->
getr regs 10%bv = w64 n -> 0 <= n < cf_malloc_max -> blocks_bytes S + n <= LIVE_MAX ->
In [pc_malloc_ra0 (as_code B); raZ regs] (as_universe B) -> In [pc_malloc_ra0 (as_code B)] (as_universe B) ->
AI tfibsegs (w_H W) (w_A W) md ->
(forall (r : sptr * astate) (trc : list Z) tr (W' : world tfibsegs) (c' : config),
In trc (as_universe B) -> apath (malloc_cf n trc S) tr r -> gflag tr = true ->
YGcfMallocComposeKeep.malloc_leaf_cf_keep tfibsegs B ly S [] W regs mem md n r W' c' ->
wle W W' -> AI tfibsegs (w_H W') (w_A W') (cfg_model c') ->
srealizes tfibsegs c' KB) ->
srealizes tfibsegs (cfg_at tfibsegs (pc_wrap_malloc (as_code B)) regs mem md) KB.

(* ---------------------------------------------------------------------- *)
(* 2. The intrinsic sites: the read check (RCHK) and the payload memcpy (MCPY).
      Donor: YD1v.v:267-302, YD1i.v:18-31. *)
Definition drv_epre_cf (ly : alayout) (S : astate) (W : world tfibsegs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) : Prop :=
ARcf tfibsegs B ly S [] W mem md /\ (ly_stk_lo ly = ASAN_CEIL /\ ly_stk_hi ly = kHighMemEnd) /\ YK0s.ret_ok (getr regs 1%bv) /\
spZ regs mod 16 = 0 /\ sp_window_lo - 2304 <= spZ regs <= sp_window_hi /\ ly_top ly - 6239 <= spZ regs <= ly_top ly + 48 /\
(forall a, spZ regs - ESTACK <= a < spZ regs -> apresent (w_H W) mem a) /\
getr regs 3%bv = w64 (as_gp B) /\ getr regs 4%bv = w64 (as_tp B).

Definition memcpy_site_tfa_cf : Prop :=
forall ly S W regs mem md d x n,
drv_epre_cf ly S W regs mem md ->
getr regs 10%bv = w64 d -> getr regs 11%bv = w64 x -> getr regs 12%bv = w64 n -> 0 <= n < 2 ^ 32 -> 0 <= d -> d + n <= 2 ^ 63 ->
dest_ok tfibsegs B ly S W regs mem d n -> amem_range d n ->
range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF d n -> (0 < n -> shadow_hull_vis (aview tfibsegs (w_H W) mem) d n) ->
0 <= x -> x + n <= 2 ^ 63 -> src_ok tfibsegs W regs mem x n -> (d + n <= x \/ x + n <= d) -> amem_range x n ->
range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF x n -> (0 < n -> shadow_hull_vis (aview tfibsegs (w_H W) mem) x n) ->
SRr tfibsegs W (cfg_at tfibsegs (pc_wrap_memcpy (as_code B)) regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\
ARcf tfibsegs B ly S [] W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10%bv = w64 d /\
(forall i, 0 <= i < n -> aview tfibsegs (w_H W) mem' (d + i) = aview tfibsegs (w_H W) mem (x + i)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + n) -> ~ (spZ regs - ESTACK <= a < spZ regs) -> aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a) /\
(YAkMemnorm.memnorm tfibsegs mem -> YAkMemnorm.memnorm tfibsegs mem')).

(* The read-check routine's realizer, at every ghost set Hp (the form of a8's realizers). Its post's last conjunct
   is the memnorm keep, in the form of a Theorem Labs lane's keep realizers (YGcallMxmn.aintrin_realizes_xm): OPEN for the
   realizer's row owner (lane MnPrefix added it, 2026-10-29, so that the read loop keeps memnorm across the check). *)
Definition aread_check_stmt_cf : Prop :=
forall ly S Hp W regs mem md n p,
ecall_pre_cf tfibsegs B ly S Hp W regs mem md ->
getr regs 10%bv = w64 n -> getr regs 9%bv = w64 p -> 0 < n < 2 ^ 31 -> 0 <= p -> p + n <= 2 ^ 63 ->
amem_range p n ->
range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF p n -> shadow_hull_vis (aview tfibsegs (w_H W) mem) p n ->
SRr tfibsegs W (cfg_at tfibsegs A_CHK regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at tfibsegs A_CHK_END regs' mem' md' /\
ARcf tfibsegs B ly S Hp W mem' md' /\
(forall r, acallee_saved r -> r <> 9 -> r <> 18 -> r <> 20 -> getr regs' (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) /\
same_but_materialized md md' /\ getr regs' 10%bv = w64 n /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - ESTACK <= a < spZ regs) -> aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a) /\
(YAkMemnorm.memnorm tfibsegs mem -> YAkMemnorm.memnorm tfibsegs mem')).

Definition read_check_tfa_cf : Prop :=
forall ly S W regs mem md (n ptr : Z),
drv_epre_cf ly S W regs mem md ->
getr regs 10%bv = w64 n -> getr regs 9%bv = w64 ptr -> 0 < n < 2 ^ 31 -> 0 <= ptr -> ptr + n <= 2 ^ 63 ->
amem_range ptr n -> range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF ptr n -> shadow_hull_vis (aview tfibsegs (w_H W) mem) ptr n ->
SRr tfibsegs W (cfg_at tfibsegs A_CHK regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at tfibsegs A_CHK_END regs' mem' md' /\
ARcf tfibsegs B ly S [] W mem' md' /\ chk_regs_post regs regs' /\ same_but_materialized md md' /\
getr regs' 10%bv = w64 n /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - ESTACK <= a < spZ regs) -> aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a) /\
(YAkMemnorm.memnorm tfibsegs mem -> YAkMemnorm.memnorm tfibsegs mem')).

(* ---------------------------------------------------------------------- *)
(* 3. The interceptor sites of the driver's diagnostics (YD1x). Donor: YD1x.v:41-92. *)
Definition icpt_pre_cf (ly : alayout) (S : astate) (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop :=
ARcf tfibsegs B ly S [] W mem md /\ YK0s.ret_ok (getr regs 1%bv) /\ 4096 <= raZ regs /\
spZ regs mod 16 = 0 /\ sp_window_lo - 128 <= spZ regs <= sp_window_hi /\
ly_top ly - 4112 <= spZ regs <= ly_top ly + 32 /\ ly_stk_lo ly = ASAN_CEIL /\ ly_stk_hi ly = kHighMemEnd /\
(forall a, spZ regs - DIAG_STK <= a < spZ regs -> apresent (w_H W) mem a) /\
getr regs 3%bv = w64 (as_gp B) /\ getr regs 4%bv = w64 (as_tp B).

Definition icpt_post_cf (ly : alayout) (S : astate) (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
(ret : Z) (T : TSet) : Prop :=
forall regs' mem' md',
ARcf tfibsegs B ly S [] W mem' md' -> aregs_preserved regs regs' -> same_but_materialized md md' ->
getr regs' 10%bv = w64 ret -> est (w_H W) mem' ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - DIAG_STK <= a < spZ regs) -> ~ STDERR_MUT a ->
aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ STDERR_MUT a -> apresent (w_H W) mem a -> apresent (w_H W) mem' a) ->
AI tfibsegs (w_H W) (w_A W) md' ->
srealizes tfibsegs (cfg_at tfibsegs (raZ regs) regs' mem' md') T.

Definition fwrite_site_tfa_cf : Prop :=
forall (ly : alayout) (S : astate) (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
(E : YP0m.env) (p len : Z) (msg : list byte) (T : TSet),
icpt_pre_cf ly S W regs mem md ->
getr regs 10%bv = w64 p -> getr regs 11%bv = w64 len -> getr regs 12%bv = w64 1 -> getr regs 13%bv = w64 F_STDERR_LO ->
Z.of_nat (length msg) = len -> 1 <= len <= 64 -> YImgCellsB.B_RODATA_0X298 <= p -> p + len <= YImgCellsB.B_RODATA_0X109D4 -> (p + len <= YImgCellsB.B_RODATA_0XCB82 \/ YImgCellsB.B_RODATA_0XCB97 <= p) ->
(forall i, (i < length msg)%nat -> seg_rom tfibsegs (Z_to_bv 64 (p + Z.of_nat i)) = Some (nth i msg NUL)) ->
mem_ok tfibsegs E (mrestrict (w_H W) mem) IMG_REGIONS ->
fd_lookup (m_fds md) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) ->
AI tfibsegs (w_H W) (w_A W) md ->
icpt_post_cf ly S W regs mem md 1 T ->
srealizes tfibsegs (cfg_at tfibsegs A_icpt_fwrite regs mem md) (wr ch_stderr msg T).

Definition fprintf_s_site_tfa_cf (fmt : Z) (lit1 lit2 : list byte) : Prop :=
forall (ly : alayout) (S : astate) (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
(E : YP0m.env) (s : Z) (str : list byte) (T : TSet),
icpt_pre_cf ly S W regs mem md ->
getr regs 10%bv = w64 F_STDERR_LO -> getr regs 11%bv = w64 fmt -> getr regs 12%bv = w64 s ->
Z.of_nat (length str) <= 131071 -> ~ In NUL str ->
spZ regs + 128 <= s -> s + Z.of_nat (length str) + 1 < kHighMemEnd ->
YP03.bytes_at (mrestrict (w_H W) mem) s (str ++ [NUL]) ->
(forall a, s + Z.of_nat (length str) < a < s + Z.of_nat (length str) - (s + Z.of_nat (length str)) mod 8 + 8 -> mrestrict (w_H W) mem (Z_to_bv 64 a) <> None) ->
mem_ok tfibsegs E (mrestrict (w_H W) mem) IMG_REGIONS ->
fd_lookup (m_fds md) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) ->
AI tfibsegs (w_H W) (w_A W) md ->
icpt_post_cf ly S W regs mem md (Z.of_nat (length lit1 + length str + length lit2)) T ->
srealizes tfibsegs (cfg_at tfibsegs A_icpt_fprintf regs mem md) (wr ch_stderr (lit1 ++ str ++ lit2) T).

Definition refused_site_tfa_cf : Prop :=
forall (ly : alayout) (S : astate) (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
(E : YP0m.env) (T : TSet),
icpt_pre_cf ly S W regs mem md ->
getr regs 10%bv = w64 F_STDERR_LO -> getr regs 11%bv = w64 YImgCellsB.B_RODATA_0X9480 -> getr regs 12%bv = w64 67108864 ->
mem_ok tfibsegs E (mrestrict (w_H W) mem) IMG_REGIONS ->
fd_lookup (m_fds md) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) ->
AI tfibsegs (w_H W) (w_A W) md ->
icpt_post_cf ly S W regs mem md (Z.of_nat (length msg_refused)) T ->
srealizes tfibsegs (cfg_at tfibsegs A_icpt_fprintf regs mem md) (wr ch_stderr msg_refused T).

(* ---------------------------------------------------------------------- *)
(* 4. The pre-loop error leaves (RDERR, REFUSED, HCO, usage). Donor: YD1v.v:117-130, :315-339; YD27.v:568-576. *)
Definition rderr_leaf_tfa_cf : Prop :=
forall (E' : YP0m.env) (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
(ly : alayout) (S : astate) (usp : Z) (p : list byte) (zp : Z) (fs : Fs),
bv_unsigned (ew E' 0) = usp -> sp_window_lo <= usp <= sp_window_hi -> usp mod 16 = 0 -> 1 <= bv_unsigned (ew E' 8) <= 4194303 ->
getr regs 10%bv = w64 YImgCellsB.B_STDERR_FILE_CELL -> getr regs 11%bv = w64 YImgCellsB.B_RODATA_0XD577 -> getr regs 12%bv = w64 zp ->
getr regs 1%bv = w64 YImgCellsB.B_MAIN_PC_OFF_264 -> spZ regs = usp - 128 -> getr regs 3%bv = w64 TFIB_GP -> getr regs 4%bv = w64 TFIB_TP ->
usp <= zp -> zp + Z.of_nat (length p) + 1 < kHighMemEnd -> ~ In NUL p -> Z.of_nat (length p) <= 131071 ->
YP03.bytes_at (mrestrict (w_H W) mem) zp (p ++ [NUL]) ->
(forall a, zp + Z.of_nat (length p) < a < zp + Z.of_nat (length p) - (zp + Z.of_nat (length p)) mod 8 + 8 -> mrestrict (w_H W) mem (Z_to_bv 64 a) <> None) ->
mem_ok tfibsegs E' (mrestrict (w_H W) mem) IMG_REGIONS ->
(forall a, usp - 65536 <= a < usp -> apresent (w_H W) mem a) ->
AI tfibsegs (w_H W) (w_A W) md -> ARcf tfibsegs B ly S [] W mem md -> top_ok usp ly ->
fd_lookup (m_fds md) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) -> m_fs md = fs ->
srealizes tfibsegs (mkCfg (mkst regs (w64 YImgCellsB.B_WRAP_FPRINTF_PC) mem (seg_rom tfibsegs)) md) (diag (msg_read_error p) fs).

Definition refused_leaf_tfa_cf : Prop :=
forall (E' : YP0m.env) (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
(ly : alayout) (S : astate) (usp : Z) (fs : Fs),
bv_unsigned (ew E' 0) = usp -> sp_window_lo <= usp <= sp_window_hi -> usp mod 16 = 0 -> 1 <= bv_unsigned (ew E' 8) <= 4194303 ->
getr regs 10%bv = w64 YImgCellsB.B_STDERR_FILE_CELL -> getr regs 11%bv = w64 YImgCellsB.B_RODATA_0X9480 -> getr regs 12%bv = w64 67108864 ->
getr regs 1%bv = w64 YImgCellsB.B_MAIN_PC_OFF_264 -> spZ regs = usp - 128 -> getr regs 3%bv = w64 TFIB_GP -> getr regs 4%bv = w64 TFIB_TP ->
mem_ok tfibsegs E' (mrestrict (w_H W) mem) IMG_REGIONS ->
(forall a, usp - 65536 <= a < usp -> apresent (w_H W) mem a) ->
AI tfibsegs (w_H W) (w_A W) md -> ARcf tfibsegs B ly S [] W mem md -> top_ok usp ly ->
fd_lookup (m_fds md) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) -> m_fs md = fs ->
srealizes tfibsegs (mkCfg (mkst regs (w64 YImgCellsB.B_WRAP_FPRINTF_PC) mem (seg_rom tfibsegs)) md) (diag msg_refused fs).

Definition cannot_open_tfa_cf : Prop :=
forall (sp : word) (inp : ProcInput) (xw : nat -> word) (xd : nat -> list byte)
(W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (ly : alayout) (a0 p : list byte) (e : Z),
in_argv inp = [a0; p] -> valid_sp sp -> valid_argv [a0; p] -> valid_envp (in_envp inp) -> entry_stack_fits sp [a0; p] (in_envp inp) ->
regs_ok (ELV sp a0 p inp xw xd) (ss_regs ss_open) regs ->
mem_ok tfibsegs (ELV sp a0 p inp xw xd) (mrestrict (w_H W) mem) (ss_mem ss_open) ->
facts_ok (ELV sp a0 p inp xw xd) (ss_facts ss_open) ->
runs_at (bv_unsigned sp) (mrestrict (w_H W) mem) (runs_main_tfa true sp [a0; p] (in_envp inp)) ->
AI tfibsegs (w_H W) (w_A W) md -> ARcf tfibsegs B ly init_state [] W mem md ->
top_ok (bv_unsigned sp) ly -> m_fs md = in_fs inp -> m_fds md = APSG.fds_std ->
0 < e < 4096 ->
srealizes tfibsegs
(mkCfg (mkst (regupd regs 10%bv (errno_ret e)) (v_addi (Z_to_bv 64 (ss_pc ss_open)) 4) mem (seg_rom tfibsegs)) md)
(diag (msg_cannot_open p) (in_fs inp)).

(* The donor states tfib_usage inline (YD27.v:568-576); the predicate is named here so the driver lane cites it. *)
Definition usage_tfa_cf : Prop :=
forall (sp : word) (inp : ProcInput) (xw : nat -> word) (xd : nat -> list byte)
(W : world tfibsegs) (ms : machine_state) (md : Model) (ly : alayout),
valid_sp sp -> valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> entry_stack_fits sp (in_argv inp) (in_envp inp) ->
(length (in_argv inp) <> 2)%nat ->
YP0l.st_ok tfibsegs (YP08.E0 sp (in_argv inp) (in_envp inp) xw xd) (ss_main false) (restrict (w_H W) ms) ->
runs_at (bv_unsigned sp) (mrestrict (w_H W) (ms_mem ms)) (runs_main_tfa false sp (in_argv inp) (in_envp inp)) ->
AI tfibsegs (w_H W) (w_A W) md -> ARcf tfibsegs B ly init_state [] W (ms_mem ms) md -> top_ok (bv_unsigned sp) ly ->
m_fs md = in_fs inp -> m_fds md = APSG.fds_std ->
srealizes tfibsegs (mkCfg ms md) (diag (msg_usage (nth 0 (in_argv inp) [])) (in_fs inp)).

(* ---------------------------------------------------------------------- *)
(* 5. The short / overrun leaves (SHORT, OVERRUN). Donor: YD1w.v:52-65, tail_at -> CwSites' tail_at_pinv_B. *)
Definition short_leaf_tfa_cf : Prop :=
forall (sp : word) (inp : ProcInput) (xw : nat -> word) (xd : nat -> list byte) (ws : list word)
(W : world tfibsegs) (ms : machine_state) (md : Model) (ly : alayout) (S : astate) (a0 p data : list byte) (pb : sptr) (cap : Z),
in_argv inp = [a0; p] -> valid_sp sp -> valid_argv [a0; p] -> valid_envp (in_envp inp) -> valid_fs (in_fs inp) ->
fs_lookup (in_fs inp) p = Some data -> dlen data <= 5 ->
tail_at_pinv_B B NP S_SHORT (havoc (ELV sp a0 p inp xw xd) K_M1 ws) sp inp a0 p data W ms md ly S pb cap ->
srealizes tfibsegs (mkCfg ms md) (diag msg_short (in_fs inp)).

Definition overrun_leaf_tfa_cf : Prop :=
forall (sp : word) (inp : ProcInput) (xw : nat -> word) (xd : nat -> list byte) (ws : list word)
(W : world tfibsegs) (ms : machine_state) (md : Model) (ly : alayout) (S : astate) (a0 p data : list byte) (pb : sptr) (cap : Z),
in_argv inp = [a0; p] -> valid_sp sp -> valid_argv [a0; p] -> valid_envp (in_envp inp) -> valid_fs (in_fs inp) ->
fs_lookup (in_fs inp) p = Some data -> 6 <= dlen data < 6 + config_len data ->
tail_at_pinv_B B NP S_OVR (edset (havoc (ELV sp a0 p inp xw xd) K_M1 ws) 2 data) sp inp a0 p data W ms md ly S pb cap ->
srealizes tfibsegs (mkCfg ms md) (diag msg_overrun (in_fs inp)).
End S.

(* ---------------------------------------------------------------------- *)
(* 6. The results (closed). Each is proved in PresetD1preBPf.v as <name>_holds. *)

(* YD1n.v:24 tfib_malloc_site (cgif's model law ml_malloc_ns is a8's malloc_ok_cf, YG07cf.v:390, cited by the proof).
   The two links (PresetD1sitesB.v section 1) turn drv_pre_cf's hull and read-only conjuncts into acall_pre_cf's. *)
Definition tfib_malloc_site_cf_B : Prop :=
forall (fx : YK11.FPState) (rc : YM05.RunCeil) (ci : CfImg) (cp : CfParams) (B : asyms) (NP : astate -> Prop),
PCB.iface_room_np_tail NP -> drv_hull_link -> drv_aro_link B -> YGcfMallocComposeKeep.amalloc_realizes_cf_keep tfibsegs B ->
malloc_site_tfa_cf B NP.

(* YD1i.v:105 tfib_memcpy_site. *)
Definition tfib_memcpy_site_cf_B : Prop :=
forall (fx : YK11.FPState) (rc : YM05.RunCeil) (ci : CfImg) (cp : CfParams) (B : asyms),
YGcallMxmn.aintrin_realizes_xm tfibsegs B (ARcf tfibsegs B) OCpy (pc_wrap_memcpy (as_code B)) -> memcpy_site_tfa_cf B.

(* YD1i.v:111 tfib_read_check. *)
Definition tfib_read_check_cf_B : Prop :=
forall (fx : YK11.FPState) (rc : YM05.RunCeil) (ci : CfImg) (cp : CfParams) (B : asyms),
aread_check_stmt_cf B -> read_check_tfa_cf B.

(* YD27.v:405 tfib_rderr_leaf. *)
Definition tfib_rderr_leaf_cf_B : Prop :=
forall (fx : YK11.FPState) (rc : YM05.RunCeil) (ci : CfImg) (cp : CfParams) (B : asyms)
(xst : nat -> (word -> bool) -> (word -> option byte) -> Prop) (est : (word -> bool) -> (word -> option byte) -> Prop),
TfibSyms B -> xst_frame_tfa xst -> est_frame_tfa est ->
fprintf_s_site_tfa_cf B est YImgCellsB.B_RODATA_0XD577 (strB "cli: read error on "%string) nlB ->
exit_site_cf B est xst -> rderr_leaf_tfa_cf B.

(* YD27.v:411 tfib_refused_leaf. *)
Definition tfib_refused_leaf_cf_B : Prop :=
forall (fx : YK11.FPState) (rc : YM05.RunCeil) (ci : CfImg) (cp : CfParams) (B : asyms)
(xst : nat -> (word -> bool) -> (word -> option byte) -> Prop) (est : (word -> bool) -> (word -> option byte) -> Prop),
TfibSyms B -> xst_frame_tfa xst -> est_frame_tfa est ->
refused_site_tfa_cf B est ->
exit_site_cf B est xst -> refused_leaf_tfa_cf B.

(* YD27.v:465 tfib_cannot_open. *)
Definition tfib_cannot_open_cf_B : Prop :=
forall (fx : YK11.FPState) (rc : YM05.RunCeil) (ci : CfImg) (cp : CfParams) (B : asyms)
(xst : nat -> (word -> bool) -> (word -> option byte) -> Prop) (est : (word -> bool) -> (word -> option byte) -> Prop),
TfibSyms B -> xst_frame_tfa xst -> est_frame_tfa est ->
fprintf_s_site_tfa_cf B est YImgCellsB.B_RODATA_0XD562 (strB "cli: cannot open "%string) nlB ->
exit_site_cf B est xst -> cannot_open_tfa_cf B.

(* YD27.v:568 tfib_usage. *)
Definition tfib_usage_cf_B : Prop :=
forall (fx : YK11.FPState) (rc : YM05.RunCeil) (ci : CfImg) (cp : CfParams) (B : asyms)
(xst : nat -> (word -> bool) -> (word -> option byte) -> Prop) (est : (word -> bool) -> (word -> option byte) -> Prop),
TfibSyms B -> xst_frame_tfa xst -> est_frame_tfa est ->
fprintf_s_site_tfa_cf B est YImgCellsB.B_RODATA_0X55CA (strB "usage: "%string) (strB " INPUT"%string ++ nlB) ->
exit_site_cf B est xst -> usage_tfa_cf B.

(* YD27.v:862 tfib_short_leaf (cgif's model law ml_free is not needed: it served only cgif's event bound). The free
   after the fwrite diagnostic is the free site over drv_pre_cf without memnorm (PresetD1sitesB.v free_site_nomn_cf),
   since the driver does not carry memnorm across the fwrite. *)
Definition tfib_short_leaf_cf_B : Prop :=
forall (fx : YK11.FPState) (rc : YM05.RunCeil) (ci : CfImg) (cp : CfParams) (B : asyms) (NP : astate -> Prop)
(xst : nat -> (word -> bool) -> (word -> option byte) -> Prop) (est : (word -> bool) -> (word -> option byte) -> Prop),
TfibSyms B -> xst_frame_tfa xst -> est_frame_tfa est ->
fwrite_site_tfa_cf B est -> exit_site_cf B est xst -> free_site_nomn_cf B NP -> short_leaf_tfa_cf B NP.

(* YD27.v:870 tfib_overrun_leaf (the free as tfib_short_leaf_cf_B's). *)
Definition tfib_overrun_leaf_cf_B : Prop :=
forall (fx : YK11.FPState) (rc : YM05.RunCeil) (ci : CfImg) (cp : CfParams) (B : asyms) (NP : astate -> Prop)
(xst : nat -> (word -> bool) -> (word -> option byte) -> Prop) (est : (word -> bool) -> (word -> option byte) -> Prop),
TfibSyms B -> xst_frame_tfa xst -> est_frame_tfa est ->
fwrite_site_tfa_cf B est -> exit_site_cf B est xst -> free_site_nomn_cf B NP -> overrun_leaf_tfa_cf B NP.

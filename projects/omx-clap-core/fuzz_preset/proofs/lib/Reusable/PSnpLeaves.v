(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-30 (route (B''): the call memory in the call rules): Section allocm takes
   YGcallx's new QMm (the call's conjuncts on the state and the call memory) and QMQ (QMm S mem -> QM S); its eight
   _m rules take `QMm Sc <call memory>` instead of `QM Sc`, and pass QMm / QMQ to YGcallx's rules. *)
(* Modified by Theorem Labs, 2026-10-30 (the world relation R): the free _m rules are proved once over the journal's
   world relation R and the callee's call post APOST (aj_free_x_ct_mR / aj_free_at_x_ct_mR; the old _m names are the
   instances at wle and acall_post_x; aj_free_x_mR / aj_free_at_x_mR likewise); every other call rule here with a
   journal takes it at any R, the old names being their wle instances: aj_intrin_at_xmR, aj_poison_at_x_mR and
   aj_poison_x_mR take R alone; aj_intrin_at_xm_frR, aj_bcmp_at_xmR, aj_strcmp_at_xroR, aj_strlen_at_xroR,
   aj_strcmp_at_xromR, aj_strlen_at_xromR, aj_strlen_at_xmR, aj_stack_malloc_at_xmR, aj_set_shadow_at_xmR,
   aj_unpoison_at_x_mR and aj_unpoison_x_mR take R reflexive and transitive, binders first (the stack-malloc form uses
   both to compose the call's own journal into the caller's); the malloc _m rules aj_malloc_x_mR, aj_malloc_x_ct_mR,
   aj_malloc_at_x_mR and aj_malloc_at_x_ct_mR also take wle inside R (YGcallx's malloc R forms); section 12 states the cf
   free forms under the re-hide (aj_free_x_ct_m_rh / aj_free_at_x_ct_m_rh: SRr' segs RZ_cf, the journal at wle' segs
   RZ_cf). *)
(* Modified by Theorem Labs, 2026-10-31 (field round 3 part 3c: memnorm out of every call text): YGcallx.v's leaves
   malloc_leaf_x / free_leaf_x / free_leaf_xA lost their memnorm keep, the conjunct family 4's keep was read from. So
   the eight _m malloc / free rules of section 10, their R forms (_mR) and section 12's two cf free forms (_m_rh) drop
   the keep (MN.memnorm segs memT -> MN.memnorm segs mem2) from their conclusion: each _m / _mR rule is now its
   YGcallx.v original VERBATIM (the _mR forms are proved by it), under its own name for the walks that apply it. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Reusable/YGcallMxmn.v, with its module names changed; 186 of its 224 lines of code are new or changed and 2291 lines of the source are left out. *)
(* Theorem Labs, 2026-10: the LEAF CONTRACTS of fuzz_preset's snprintf chain, over the engine's generic ARx with the
   ghost list Hp fixed (route (a), c-omx-hpreset 10:51Z), written out in full next to the four roots so that the
   re-pin and the leaf proofs (P2 / P3) see exactly what they must discharge. Each text is checked equal (by
   conversion) to the name the roots take it under.
   The chain, at preset image A (lib/A/PSnpSnp, PSnpSvsni, PSnpSvsn, PSnpSvfi):
     snp_ok   : top_snprintf at (K, PC_snprintf)                  <- AVSNI    = link_vsni at (KV, A_VSNI), KV + 0x60 <= K
     svsni_ok : link_vsni at (K, A_VSNI)                          <- APCOMMON = leaf_pcommon at (Kpc, A_PCOM),
                                                                     AVSN     = link_vsn at (Kvs, A_VSN),
                                                                     0x870 + Kvs, 0x870 + Kpc, 0x870 + ESTACK <= K
     svsn_ok  : link_vsn at (K, A_VSN)                            <- AMEMSET  = leaf_memset at W_MEMSET,
                                                                     AVFPI    = leaf_vfprintf at (Kvi, A_SNW, A_VFPI),
                                                                     304 + Kvi <= K, gc / gv = AE2p.A_GOT_canary / A_canary
     svfi_ok  : leaf_vfprintf at (K, A_SNW, A_VFPI)               <- APCOMMON = leaf_pcommon at (Kp, A_PCOM),
                                                                     AVFP     = leaf_vfprintf at (Kv, A_SNW, A_VFP),
                                                                     0x30 + Kv, 0x30 + Kp <= K
   So the OPEN leaves are L1 leaf_pcommon (printf_common, twice: svsni_ok's Kpc and svfi_ok's Kp), L2 leaf_memset (the
   memset interceptor) and L3 leaf_vfprintf at A_VFP (musl vfprintf); C1 link_vsn and C2 link_vsni are closed by
   svsn_ok and svsni_ok, and leaf_vfprintf at A_VFPI by svfi_ok. Image-free: pc, windows and cells are parameters.
   Sources: FMsnprintfSx.v:64-78, :123-202, :205-251 and FMsnprintfShared.v:121-154 of origin/cold/port-fm-rtprintf-param
   7e395de08f5 (sh_apcommon_realizesUz, sh_avsnprintf_realizesUa, sh_avsnprintf_icpt_realizesUa,
   sh_avfprintf_icpt_realizesUx, sh_asnprintf_realizesU) and FMsnprintfI.v:185-204 (aintrin_realizesU) at op = OSet,
   with ecall_preU segs B .. U .. -> ecall_pre_x segs B ARx .. Hp .., ARU segs B .. U .. -> ARx .. Hp .. and
   U : list (Z * Z) -> Hp : list Z, nothing else. '+ 8' in this file: rdword / slot / cell word ranges (address ranges);
   no presence form. No image numeral. *)
(* Modified by Theorem Labs, 2026-10: port-fm 00daeaf3796's destination slack (origin/cold/port-fm-rtprintf-param, the
   final text 3e35620c52e): top_snprintf's 'amem_range d (sn_len (n - 1) T + 8)' replaces 'amem_range d
   (sn_len (n - 1) T)'; link_vsn / link_vsni carry 'amem_range d (sn_len (n - 1) T + 8)' after the 2^47 slot bound;
   leaf_vfprintf (L3, musl vfprintf) carries GXA (5) 'amem_range s0 (sn_len n0 T + 8)' after GXA (4). leaf_pcommon and
   leaf_memset are unchanged. Each '+ 8' is an address-range fact (amem_range), not a presence form. *)
(* Modified by Theorem Labs, 2026-10: the memnorm keep (c-omx-alloc 17:03Z ruling (b): preset's caller K0's put_string crosses the region in the m-form, so every contract pays `memnorm segs mem -> memnorm segs mem'`): each of the six texts' posts ends in `(YAkMemnorm.memnorm segs mem -> YAkMemnorm.memnorm segs mem')`, last, as the engine's YGcallSnp.asnprintf_realizes_xrom; leaf_memset is now the engine's YGcallMxmn.aintrin_realizes_xm at OSet (which ends in that keep), discharged at preset A / B by c-libc-stdio RowsSet's prow_memset_icpt_xm_A_lit / _B_lit (lib/A|AU/PRowSet.v, at __wrap_memset: 0x523dc (A') / 0x524c8 (B') on the #102 pins, origin/cold/c-libc-stdio-rows102 599a4cefc740 (A') / 407ddab4a12a (B'), carried by int102 8201be0eb399; 0x52348 / 0x523cc on the old pins, origin/cold/c-libc-stdio-rows-set a6f4ebf35892). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YCbqG FCiface YGcallMx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import PSnpShared PSnpSx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm YGcallMxmn.
Import ListNotations.
Local Open Scope Z_scope.

Section l. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.

(* ---- L1, an open leaf: printf_common, the Uz form. svsni_ok takes it as APCOMMON at (Kpc, A_PCOM), svfi_ok as APCOMMON at (Kp, A_PCOM). ---- *)
Definition leaf_pcommon (FF : fmt_fam) (K : Z) (cr : list (Z * Z)) (pc : Z) : Prop :=
forall ly S (Hp : list Z) W regs mem md f ap (ws T : list Z),
ecall_pre_x segs B ARx ly S Hp W regs mem md -> ly_stk_lo ly + K <= spZ regs ->
(forall a, spZ regs - K <= a < spZ regs -> apresent (w_H W) mem a) ->
getr regs 11 = w64 f -> getr regs 12 = w64 ap ->
consts_view segs W mem cr -> Forall (fun r => 0 <= fst r /\ fst r + snd r <= 2 ^ 63) cr ->
Forall (zdisjoint (spZ regs - K, K)) cr ->
words_at (aview segs (w_H W) mem) ap ws -> zdisjoint (ap, 8 * Z.of_nat (length ws)) (spZ regs - K, K) ->
0 <= ap -> ap + 8 * Z.of_nat (length ws) <= 2 ^ 47 ->
FF (aview segs (w_H W) mem) [(spZ regs - K, K)] f ws T ->
SRr segs W (cfg_at segs pc regs mem md) (fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at segs (raZ regs) regs' mem' md' /\ ARx ly S Hp W mem' md' /\ aregs_preserved regs regs' /\
same_but_materialized md md' /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - K <= a < spZ regs) -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a) /\
(YAkMemnorm.memnorm segs mem -> YAkMemnorm.memnorm segs mem')).

(* ---- L2, an open leaf: the memset interceptor (op = OSet). svsn_ok takes it as AMEMSET at W_MEMSET. ---- *)
Definition leaf_memset (pc : Z) : Prop :=
forall ly S Hp W regs mem md d x n,
ecall_pre_x segs B ARx ly S Hp W regs mem md ->
getr regs 10 = w64 d -> getr regs 11 = w64 x -> getr regs 12 = w64 n -> 0 <= n < 2 ^ 32 -> 0 <= d -> d + n <= 2 ^ 63 ->
dest_ok segs B ly S W regs mem d n -> amem_range d n ->
range_addressable (aview segs (w_H W) mem) SHADOW_OFF d n -> (0 < n -> shadow_hull_vis (aview segs (w_H W) mem) d n) ->
True ->
SRr segs W (cfg_at segs pc regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at segs (raZ regs) regs' mem' md' /\
ARx ly S Hp W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = w64 d /\
(forall i, 0 <= i < n -> aview segs (w_H W) mem' (d + i) = Some (x mod 256)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + n) -> ~ (spZ regs - ESTACK <= a < spZ regs) -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a) /\
(YAkMemnorm.memnorm segs mem -> YAkMemnorm.memnorm segs mem')).

(* ---- L3, an open leaf: musl vfprintf, the Ux form. svfi_ok takes it as AVFP at (Kv, A_SNW, A_VFP). The same text at (Kvi, A_SNW, A_VFPI) is svfi_ok's conclusion and svsn_ok's AVFPI. ---- *)
Definition leaf_vfprintf
    (FF : fmt_fam) (K gc gv img_lo img_hi : Z) (cr : list (Z * Z)) (snw pc : Z) : Prop :=
forall ly S (Hp : list Z) W regs mem md fp f ap bp cp s0 n0 (ws T : list Z) cval,
ecall_pre_x segs B ARx ly S Hp W regs mem md ->
ly_stk_lo ly + K <= spZ regs ->
(forall a, spZ regs - K <= a < spZ regs -> apresent (w_H W) mem a) ->
getr regs 10 = w64 fp -> getr regs 11 = w64 f -> getr regs 12 = w64 ap ->
words_at (aview segs (w_H W) mem) fp (sn_file snw bp cp) -> 0 < bp ->
words_at (aview segs (w_H W) mem) cp [s0; n0] ->
dest_ok segs B ly S W regs mem fp 232 -> dest_ok segs B ly S W regs mem cp 16 ->
0 <= fp -> fp + 232 <= 2 ^ 63 -> 0 <= cp -> cp + 16 <= 2 ^ 63 ->
consts_view segs W mem cr -> Forall (fun r => 0 <= fst r /\ fst r + snd r <= 2 ^ 63) cr ->
Forall (fun r => Forall (zdisjoint r) (vfp_out K (spZ regs) s0 (sn_len n0 T) fp cp)) cr ->
rdword (aview segs (w_H W) mem) gc = Some gv -> rdword (aview segs (w_H W) mem) gv = Some cval ->
0 <= gc -> gc + 8 <= 2 ^ 63 -> 0 <= gv -> gv + 8 <= 2 ^ 63 ->
Forall (zdisjoint (gc, 8)) (vfp_out K (spZ regs) s0 (sn_len n0 T) fp cp) ->
Forall (zdisjoint (gv, 8)) (vfp_out K (spZ regs) s0 (sn_len n0 T) fp cp) ->
words_at (aview segs (w_H W) mem) ap ws ->
0 <= ap -> ap + 8 * Z.of_nat (length ws) < 2 ^ 63 ->
Forall (zdisjoint (ap, 8 * Z.of_nat (length ws))) (vfp_out K (spZ regs) s0 (sn_len n0 T) fp cp) ->
FF (aview segs (w_H W) mem) (vfp_out K (spZ regs) s0 (sn_len n0 T) fp cp) f ws T ->
0 <= n0 < 2 ^ 31 - 1 -> Z.of_nat (length T) < 2 ^ 31 - 1 -> 0 < s0 -> s0 + sn_len n0 T <= 2 ^ 63 ->
pairwise zdisjoint (vfp_out K (spZ regs) s0 (sn_len n0 T) fp cp) ->
dest_ok segs B ly S W regs mem s0 (sn_len n0 T) -> amem_range s0 (sn_len n0 T) ->
range_addressable (aview segs (w_H W) mem) SHADOW_OFF s0 (sn_len n0 T) ->
shadow_hull_vis (aview segs (w_H W) mem) s0 (sn_len n0 T) ->
zdisjoint (s0, sn_len n0 T) (img_lo, img_hi - img_lo) ->
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
(* GXA (1): musl vsnprintf's `*c.s = 0`, the only NUL an empty output leaves *)
aview segs (w_H W) mem s0 = Some 0 ->
(* GXA (2): the frame order musl vsnprintf builds *)
spZ regs <= fp -> fp + 232 <= cp -> cp + 16 <= ap ->
(* GXA (3): the destination is below the window or above the caller's slots *)
(s0 + sn_len n0 T <= spZ regs - K \/ ap + 8 * Z.of_nat (length ws) <= s0) ->
(* GXA (4): the FILE, the cookie and the slots are user memory (with GXA (2), all below 2^47) *)
ap + 8 * Z.of_nat (length ws) <= 2 ^ 47 ->
(* GXA (5): the destination's slack word (pf_rng, AsanFacts.v:78-80: app_mem (D + i + 7) for each written byte) *)
amem_range s0 (sn_len n0 T + 8) ->
SRr segs W (cfg_at segs pc regs mem md)
(fun W' c' => W' = W /\ exists (fx' : YK11.FPState) regs' mem' md',
c' = @cfg_at fx' segs (raZ regs) regs' mem' md' /\
(forall k : bv 5, bv_unsigned k <> 10 -> Sem.reg_get (@fp_regs fx') k = Sem.reg_get (@fp_regs fx) k) /\
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx')) 5) 7 = 0 /\
ARx ly S Hp W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = w64 (Z.of_nat (length T)) /\
(forall i, 0 <= i < sn_len n0 T -> aview segs (w_H W) mem' (s0 + i) = Some (nth (Z.to_nat i) (sn_bytes n0 T) 0)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (s0 <= a < s0 + sn_len n0 T) ->
~ Exists (in_zr a) [(spZ regs - K, K); (fp, 232); (cp, 16)] -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a) /\
(YAkMemnorm.memnorm segs mem -> YAkMemnorm.memnorm segs mem')).

(* ---- C1, closed by svsn_ok: musl vsnprintf, the Ua form. svsni_ok takes it as AVSN at (Kvs, A_VSN). ---- *)
Definition link_vsn (FF : fmt_fam) (K gc gv img_lo img_hi : Z) (cr : list (Z * Z)) (pc : Z) : Prop :=
forall ly S (Hp : list Z) W regs mem md d n f ap (ws T : list Z) cval,
ecall_pre_x segs B ARx ly S Hp W regs mem md ->
ly_stk_lo ly + K <= spZ regs ->
(forall a, spZ regs - K <= a < spZ regs -> apresent (w_H W) mem a) ->
getr regs 10 = w64 d -> getr regs 11 = w64 n -> getr regs 12 = w64 f -> getr regs 13 = w64 ap ->
consts_view segs W mem cr -> Forall (fun r => 0 <= fst r /\ fst r + snd r <= 2 ^ 63) cr ->
Forall (fun r => Forall (zdisjoint r) (snp_out K (spZ regs) d (sn_len (n - 1) T))) cr ->
rdword (aview segs (w_H W) mem) gc = Some gv -> rdword (aview segs (w_H W) mem) gv = Some cval ->
0 <= gc -> gc + 8 <= 2 ^ 63 -> 0 <= gv -> gv + 8 <= 2 ^ 63 ->
Forall (zdisjoint (gc, 8)) (snp_out K (spZ regs) d (sn_len (n - 1) T)) ->
Forall (zdisjoint (gv, 8)) (snp_out K (spZ regs) d (sn_len (n - 1) T)) ->
words_at (aview segs (w_H W) mem) ap ws ->
0 <= ap -> ap + 8 * Z.of_nat (length ws) < 2 ^ 63 ->
Forall (zdisjoint (ap, 8 * Z.of_nat (length ws))) (snp_out K (spZ regs) d (sn_len (n - 1) T)) ->
FF (aview segs (w_H W) mem) (snp_out K (spZ regs) d (sn_len (n - 1) T)) f ws T ->
1 <= n < 2 ^ 31 -> Z.of_nat (length T) < 2 ^ 31 - 1 -> 0 < d -> d + sn_len (n - 1) T <= 2 ^ 63 ->
pairwise zdisjoint (snp_out K (spZ regs) d (sn_len (n - 1) T)) ->
dest_ok segs B ly S W regs mem d (sn_len (n - 1) T) -> amem_range d (sn_len (n - 1) T) ->
range_addressable (aview segs (w_H W) mem) SHADOW_OFF d (sn_len (n - 1) T) ->
shadow_hull_vis (aview segs (w_H W) mem) d (sn_len (n - 1) T) ->
(* dest_off_globals: the caller discharges it by measurement *) zdisjoint (d, sn_len (n - 1) T) (img_lo, img_hi - img_lo) ->
(* frm0_entry: rounding mode 0 at entry (GXA VfprintfCall.v:37) *) Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
(* order: the arguments lie at or above the entry sp (every caller's va area is its own spill or above it) *)
spZ regs <= ap ->
(* the destination is below the window or above the argument slots (GXA VfprintfCall.v:42, first disjunction) *)
(d + sn_len (n - 1) T <= spZ regs - K \/ ap + 8 * Z.of_nat (length ws) <= d) ->
(* the argument slots below 2^47 (the normalized store GXA and printf_common's cleaned run read drops higher bytes) *)
ap + 8 * Z.of_nat (length ws) <= 2 ^ 47 ->
(* the destination's slack word: GXA's range check pf_rng asks app_mem (D + i + 7) for each written byte *)
amem_range d (sn_len (n - 1) T + 8) ->
SRr segs W (cfg_at segs pc regs mem md)
(fun W' c' => W' = W /\ exists (fx' : YK11.FPState) regs' mem' md',
c' = @cfg_at fx' segs (raZ regs) regs' mem' md' /\
(forall k : bv 5, bv_unsigned k <> 10 -> Sem.reg_get (@fp_regs fx') k = Sem.reg_get (@fp_regs fx) k) /\
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx')) 5) 7 = 0 /\
ARx ly S Hp W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = w64 (Z.of_nat (length T)) /\
(forall i, 0 <= i < sn_len (n - 1) T -> aview segs (w_H W) mem' (d + i) = Some (nth (Z.to_nat i) (sn_bytes (n - 1) T) 0)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + sn_len (n - 1) T) ->
~ (spZ regs - K <= a < spZ regs) -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a) /\
(YAkMemnorm.memnorm segs mem -> YAkMemnorm.memnorm segs mem')).

(* ---- C2, closed by svsni_ok: the vsnprintf interceptor, the Ua form. snp_ok takes it as AVSNI at (KV, A_VSNI). ---- *)
Definition link_vsni (FF : fmt_fam) (K gc gv img_lo img_hi : Z) (cr : list (Z * Z)) (pc : Z) : Prop :=
forall ly S (Hp : list Z) W regs mem md d n f ap (ws T : list Z) cval,
ecall_pre_x segs B ARx ly S Hp W regs mem md ->
ly_stk_lo ly + K <= spZ regs ->
(forall a, spZ regs - K <= a < spZ regs -> apresent (w_H W) mem a) ->
getr regs 10 = w64 d -> getr regs 11 = w64 n -> getr regs 12 = w64 f -> getr regs 13 = w64 ap ->
consts_view segs W mem cr -> Forall (fun r => 0 <= fst r /\ fst r + snd r <= 2 ^ 63) cr ->
Forall (fun r => Forall (zdisjoint r) (snp_out K (spZ regs) d (sn_len (n - 1) T))) cr ->
rdword (aview segs (w_H W) mem) gc = Some gv -> rdword (aview segs (w_H W) mem) gv = Some cval ->
0 <= gc -> gc + 8 <= 2 ^ 63 -> 0 <= gv -> gv + 8 <= 2 ^ 63 ->
Forall (zdisjoint (gc, 8)) (snp_out K (spZ regs) d (sn_len (n - 1) T)) ->
Forall (zdisjoint (gv, 8)) (snp_out K (spZ regs) d (sn_len (n - 1) T)) ->
words_at (aview segs (w_H W) mem) ap ws ->
0 <= ap -> ap + 8 * Z.of_nat (length ws) < 2 ^ 63 ->
Forall (zdisjoint (ap, 8 * Z.of_nat (length ws))) (snp_out K (spZ regs) d (sn_len (n - 1) T)) ->
FF (aview segs (w_H W) mem) (snp_out K (spZ regs) d (sn_len (n - 1) T)) f ws T ->
1 <= n < 2 ^ 31 -> Z.of_nat (length T) < 2 ^ 31 - 1 -> 0 < d -> d + sn_len (n - 1) T <= 2 ^ 63 ->
pairwise zdisjoint (snp_out K (spZ regs) d (sn_len (n - 1) T)) ->
dest_ok segs B ly S W regs mem d (sn_len (n - 1) T) -> amem_range d (sn_len (n - 1) T) ->
range_addressable (aview segs (w_H W) mem) SHADOW_OFF d (sn_len (n - 1) T) ->
shadow_hull_vis (aview segs (w_H W) mem) d (sn_len (n - 1) T) ->
(* dest_off_globals: the caller discharges it by measurement *) zdisjoint (d, sn_len (n - 1) T) (img_lo, img_hi - img_lo) ->
(* frm0_entry: rounding mode 0 at entry (GXA VfprintfCall.v:37) *) Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
(* order: the arguments lie at or above the entry sp (every caller's va area is its own spill or above it) *)
spZ regs <= ap ->
(* the destination is below the window or above the argument slots (GXA VfprintfCall.v:42, first disjunction) *)
(d + sn_len (n - 1) T <= spZ regs - K \/ ap + 8 * Z.of_nat (length ws) <= d) ->
(* the argument slots below 2^47 (the normalized store GXA and printf_common's cleaned run read drops higher bytes) *)
ap + 8 * Z.of_nat (length ws) <= 2 ^ 47 ->
(* the destination's slack word: GXA's range check pf_rng asks app_mem (D + i + 7) for each written byte *)
amem_range d (sn_len (n - 1) T + 8) ->
SRr segs W (cfg_at segs pc regs mem md)
(fun W' c' => W' = W /\ exists (fx' : YK11.FPState) regs' mem' md',
c' = @cfg_at fx' segs (raZ regs) regs' mem' md' /\
(forall k : bv 5, bv_unsigned k <> 10 -> Sem.reg_get (@fp_regs fx') k = Sem.reg_get (@fp_regs fx) k) /\
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx')) 5) 7 = 0 /\
ARx ly S Hp W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = w64 (Z.of_nat (length T)) /\
(forall i, 0 <= i < sn_len (n - 1) T -> aview segs (w_H W) mem' (d + i) = Some (nth (Z.to_nat i) (sn_bytes (n - 1) T) 0)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + sn_len (n - 1) T) ->
~ (spZ regs - K <= a < spZ regs) -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a) /\
(YAkMemnorm.memnorm segs mem -> YAkMemnorm.memnorm segs mem')).

(* ---- T, snp_ok's conclusion at (K, PC_snprintf): snprintf over ARx with Hp fixed. ---- *)
Definition top_snprintf (FF : fmt_fam) (K gc gv img_lo img_hi : Z) (cr : list (Z * Z)) (pc : Z) : Prop :=
forall ly S (Hp : list Z) W regs mem md d n f (xs ws T : list Z) cval,
ecall_pre_x segs B ARx ly S Hp W regs mem md ->
ly_stk_lo ly + K <= spZ regs ->
(forall a, spZ regs - K <= a < spZ regs -> apresent (w_H W) mem a) ->
getr regs 10 = w64 d -> getr regs 11 = w64 n -> getr regs 12 = w64 f ->
consts_view segs W mem cr -> Forall (fun r => 0 <= fst r /\ fst r + snd r <= 2 ^ 63) cr ->
Forall (fun r => Forall (zdisjoint r) (snp_out K (spZ regs) d (sn_len (n - 1) T))) cr ->
rdword (aview segs (w_H W) mem) gc = Some gv -> rdword (aview segs (w_H W) mem) gv = Some cval ->
0 <= gc -> gc + 8 <= 2 ^ 63 -> 0 <= gv -> gv + 8 <= 2 ^ 63 ->
Forall (zdisjoint (gc, 8)) (snp_out K (spZ regs) d (sn_len (n - 1) T)) ->
Forall (zdisjoint (gv, 8)) (snp_out K (spZ regs) d (sn_len (n - 1) T)) ->
va_words regs (aview segs (w_H W) mem) (spZ regs) xs ws ->
spZ regs + 8 * Z.of_nat (length xs) <= 2 ^ 47 ->
Forall (zdisjoint (spZ regs, 8 * Z.of_nat (length xs))) (snp_out K (spZ regs) d (sn_len (n - 1) T)) ->
FF (aview segs (w_H W) mem) (snp_out K (spZ regs) d (sn_len (n - 1) T)) f ws T ->
1 <= n < 2 ^ 31 -> Z.of_nat (length T) < 2 ^ 31 - 1 -> 0 < d -> d + sn_len (n - 1) T <= 2 ^ 63 ->
pairwise zdisjoint (snp_out K (spZ regs) d (sn_len (n - 1) T)) ->
dest_ok segs B ly S W regs mem d (sn_len (n - 1) T) -> amem_range d (sn_len (n - 1) T + 8) ->
range_addressable (aview segs (w_H W) mem) SHADOW_OFF d (sn_len (n - 1) T) ->
shadow_hull_vis (aview segs (w_H W) mem) d (sn_len (n - 1) T) ->
(* dest_off_globals: the caller discharges it by measurement *) zdisjoint (d, sn_len (n - 1) T) (img_lo, img_hi - img_lo) ->
(* frm0_entry: rounding mode 0 at entry (GXA VfprintfCall.v:37) *) Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
SRr segs W (cfg_at segs pc regs mem md)
(fun W' c' => W' = W /\ exists (fx' : YK11.FPState) regs' mem' md',
c' = @cfg_at fx' segs (raZ regs) regs' mem' md' /\
(forall k : bv 5, bv_unsigned k <> 10 -> Sem.reg_get (@fp_regs fx') k = Sem.reg_get (@fp_regs fx) k) /\
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx')) 5) 7 = 0 /\
ARx ly S Hp W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = w64 (Z.of_nat (length T)) /\
(forall i, 0 <= i < sn_len (n - 1) T -> aview segs (w_H W) mem' (d + i) = Some (nth (Z.to_nat i) (sn_bytes (n - 1) T) 0)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + sn_len (n - 1) T) ->
~ (spZ regs - K <= a < spZ regs) -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a) /\
(YAkMemnorm.memnorm segs mem -> YAkMemnorm.memnorm segs mem')).


(* ---- the texts are the names the roots take ---- *)
Lemma leaf_pcommon_is : forall FF K cr pc, leaf_pcommon FF K cr pc = sh_apcommon_realizes_xz segs B ARx FF K cr pc.
Proof. reflexivity. Qed.
Lemma leaf_memset_is : forall pc, leaf_memset pc = YGcallMxmn.aintrin_realizes_xm segs B ARx OSet pc.
Proof. reflexivity. Qed.
Lemma leaf_vfprintf_is : forall FF K gc gv img_lo img_hi cr snw pc,
  leaf_vfprintf FF K gc gv img_lo img_hi cr snw pc = sh_avfprintf_icpt_realizes_xx segs B ARx FF K gc gv img_lo img_hi cr snw pc.
Proof. reflexivity. Qed.
Lemma link_vsn_is : forall FF K gc gv img_lo img_hi cr pc,
  link_vsn FF K gc gv img_lo img_hi cr pc = sh_avsnprintf_realizes_xa segs B ARx FF K gc gv img_lo img_hi cr pc.
Proof. reflexivity. Qed.
Lemma link_vsni_is : forall FF K gc gv img_lo img_hi cr pc,
  link_vsni FF K gc gv img_lo img_hi cr pc = sh_avsnprintf_icpt_realizes_xa segs B ARx FF K gc gv img_lo img_hi cr pc.
Proof. reflexivity. Qed.
Lemma top_snprintf_is : forall FF K gc gv img_lo img_hi cr pc,
  top_snprintf FF K gc gv img_lo img_hi cr pc = sh_asnprintf_realizes_x segs B ARx FF K gc gv img_lo img_hi cr pc.
Proof. reflexivity. Qed.
End l.

(* The snprintf contracts every Pau target shares (statements): h-rw-dis-5's lib/Rt/SnprintfDef.v and VsnprintfDef.v
   (origin/cold/h-rw-dis-5-s4printf 4a8b5df89c3) restated over fm's library, with pieces, parser and renderer in
   FMsnprintfPf.v. Kept as there: the arguments (va_words: a3..a7 then the caller's stack slots at sp; words_at ap for
   the v* entries), the read-only constants a run reads (consts_view cr), the stack-protector cells gc -> gv -> cval,
   the disjointness lists (no alloc_ceiling: the destination and the strings may lie on the machine stack outside the
   callee's window), 1 <= n < 2^31, a0 = |T| (the untruncated length).
   Changed:
   - the format family is a parameter FF rd rs f ws T: "the format at f, with the argument words ws, reads only bytes
     disjoint from the regions rs and renders T". pf_family PK is h-rw-dis-5's family (fmt_at, pf_parse, pf_args_asan,
     pf_text) for the conversions PK covers, with every %.*s precision >= 1 (pf_prec_pos, true for a PK without Pps):
     h-rw-dis-5: pf_family pf_disco_piece, fm: pf_family pf_fm_piece; other units define their own FF;
   - the stack windows (h-rw-dis-5's SNPRINTF_STK, VSNPRINTF_ICPT_STK, VSNPRINTF_STK, VFPRINTF_ICPT_STK) are a parameter K
     of each contract (fm's chain needs 3 * ESTACK at the snprintf entry);
   - the truncating post is GXA's form (fuzz_reply lib/CJ/RL/GXA/G_vfprintf_snf.v vfprintf_snf_a_post, origin/ossv/recipes):
     sn_bytes N T = firstn N T ++ [0] at d, N = n - 1 (the cookie's count), nothing else written outside the window;
   - every destination premise (the disjointness lists, dest_ok, amem_range, the shadow) is over the written part
     w = sn_len (n - 1) T = min (|T|, n - 1) + 1 only (GXA's dn; ASan's WRITE_RANGE (str, min (size, res + 1)));
   - each contract is stated over Poison's user-poisoned ranges U (FMupoison.v: ecall_preU, ARU in the post; fm calls
     snprintf inside a poison window); h-rw-dis-5's form (ecall_pre, AR) is its U = [] instance (sh_*_of_U).
   The entries are separate contracts: snprintf, the vsnprintf interceptor, musl vsnprintf, the vfprintf interceptor
   on musl vsnprintf's FILE (musl vfprintf: the same interface), and ASan's printf_common (RtPrintf.Pcommon's text).
   ff_stable / ff_mono are what a family gives the format-generic chain. *)
(* Modified by Theorem Labs, 2026-10: c-libc-stdio's restatement for fuzz_preset (route (a), c-omx-hpreset 10:51Z) of proofs/omx-clap-core/fuzz_manifest/lib/A/FMsnprintfShared.v at origin/cold/port-fm-rtprintf-param 7e395de08f5, over the engine's generic allocator relation ARx (Reusable/YCbqG.v) with the ghost head list Hp passed through unchanged, instead of Poison's user-poisoned ranges U (FMupoison.v is not ported): `ecall_preU segs B ly S U W regs mem md` -> `ecall_pre_x segs B ARx ly S Hp W regs mem md` (FCiface.v:42-48), `ARU segs B ly S U W mem' md'` -> `ARx ly S Hp W mem' md'`, U : list (Z * Z) -> Hp : list Z, and each contract's suffix U -> _x. Left out, as the chain's four roots reach none of them and the chain is generic in FF: the format-family constructors (str_end, pf_arg_asan, pf_args_asan, fmt_at, pf_fm_piece, pf_prec_pos, pf_family, pf_prec_pos_nopps, pf_disco_prec_pos, so no FMsnprintfPf import), and the AR forms with their sh_*_of_U bridges (the AR form is the ARx form at ARx := AR). No image numeral. *)
(* Modified by Theorem Labs, 2026-10: port-fm 00daeaf3796's destination slack (origin/cold/port-fm-rtprintf-param, the
   final text 3e35620c52e): on sh_asnprintf_realizes_x only, 'amem_range d (sn_len (n - 1) T + 8)' replaces
   'amem_range d (sn_len (n - 1) T)' (GXA's pf_rng asks app_mem (D + i + 7) for every written byte). The '+ 8' is an
   address-range fact (amem_range, YG0d.v:317), not a presence form: dest_ok, range_addressable and shadow_hull_vis stay
   over the written extent. The v* contracts here are unchanged. *)
(* Modified by Theorem Labs, 2026-10: the memnorm keep (c-omx-alloc 17:03Z ruling (b)): the posts of sh_asnprintf_realizes_x, sh_avsnprintf_icpt_realizes_x, sh_avsnprintf_realizes_x, sh_avfprintf_icpt_realizes_x and sh_apcommon_realizes_x end in `(YAkMemnorm.memnorm segs mem -> YAkMemnorm.memnorm segs mem')`, last, as the engine's YGcallSnp.asnprintf_realizes_xrom. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import FCiface.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
Import ListNotations.
Local Open Scope Z_scope.

(* ---- as in h-rw-dis-5's SnprintfDef.v ---- *)
Definition words_at (rd : reader) (p : Z) (ws : list Z) : Prop :=
forall i, (i < length ws)%nat -> rdword rd (p + 8 * Z.of_nat i) = Some (nth i ws 0).
Definition va_words (regs : bvmap 5 word) (rd : reader) (sp : Z) (xs ws : list Z) : Prop :=
ws = map (argZ regs) [3; 4; 5; 6; 7] ++ xs /\ words_at rd sp xs.
Definition snp_out (K sp d n : Z) : list (Z * Z) := [(sp - K, K); (d, n)].
Definition sn_file (snw bp cp : Z) : list Z :=
[0; 0; 0; 0; 0; 0; 0; 0; 0; snw; 0; bp; 0; 0; 0; 0; 0; 0xffffffff00000000; 0xffffffff; cp;
0; 0; 0; 0; 0; 0; 0; 0; 0].
(* (h-rw-dis-5: (s0, n0 + 1); here the written part w) *)
Definition vfp_out (K sp s0 w fp cp : Z) : list (Z * Z) := [(sp - K, K); (s0, w); (fp, 232); (cp, 16)].

(* ---- format families ---- *)
(* rd = the memory's reader, rs = the regions a run writes, f = the format, ws = the argument words, T = the text *)
Definition fmt_fam : Type := reader -> list (Z * Z) -> Z -> list Z -> list Z -> Prop.
(* the bytes snprintf leaves at the destination when the cookie counts N = n - 1 (GXA's firstn N o ++ [0]), and how
   many: min (|T|, N) + 1 *)
Definition sn_bytes (N : Z) (T : list Z) : list Z := firstn (Z.to_nat N) T ++ [0].
Definition sn_len (N : Z) (T : list Z) : Z := Z.of_nat (length (sn_bytes N T)).
(* what the format-generic chain asks of a family: its reads avoid the regions rs and the shadow of their bytes lies
   below kHighMemBeg, so a memory change inside rs outside the shadow keeps it (ff_stable), and it holds for regions
   each inside one of rs (ff_mono) *)
Definition ff_stable (FF : fmt_fam) : Prop :=
forall (rd rd' : reader) rs f ws T, FF rd rs f ws T ->
(forall a, rd' a = rd a \/ (Exists (in_zr a) rs /\ ~ (SHADOW_OFF <= a < kHighMemBeg))) ->
FF rd' rs f ws T.
Definition ff_mono (FF : fmt_fam) : Prop :=
forall (rd : reader) rs rs' f ws T, FF rd rs f ws T ->
(forall r', In r' rs' -> exists r, In r rs /\ fst r <= fst r' /\ fst r' + snd r' <= fst r + snd r) ->
FF rd rs' f ws T.

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Definition consts_view (W : world segs) (mem : word -> option byte) (cr : list (Z * Z)) : Prop :=
forall a, Exists (in_zr a) cr -> aview segs (w_H W) mem a = option_map (fun b : byte => bv_unsigned b) (seg_rom segs (Z_to_bv 64 a)).

(* ---- snprintf (d, n, f, ...), entered with a stack window of K bytes ---- *)
Definition sh_asnprintf_realizes_x (FF : fmt_fam) (K gc gv img_lo img_hi : Z) (cr : list (Z * Z)) (pc : Z) : Prop :=
forall ly S (Hp : list Z) W regs mem md d n f (xs ws T : list Z) cval,
ecall_pre_x segs B ARx ly S Hp W regs mem md ->
ly_stk_lo ly + K <= spZ regs ->
(forall a, spZ regs - K <= a < spZ regs -> apresent (w_H W) mem a) ->
getr regs 10 = w64 d -> getr regs 11 = w64 n -> getr regs 12 = w64 f ->
consts_view W mem cr -> Forall (fun r => 0 <= fst r /\ fst r + snd r <= 2 ^ 63) cr ->
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
(* ---- the vsnprintf interceptor (d, n, f, ap): the arguments are the words at ap ---- *)
Definition sh_avsnprintf_icpt_realizes_x (FF : fmt_fam) (K gc gv img_lo img_hi : Z) (cr : list (Z * Z)) (pc : Z) : Prop :=
forall ly S (Hp : list Z) W regs mem md d n f ap (ws T : list Z) cval,
ecall_pre_x segs B ARx ly S Hp W regs mem md ->
ly_stk_lo ly + K <= spZ regs ->
(forall a, spZ regs - K <= a < spZ regs -> apresent (w_H W) mem a) ->
getr regs 10 = w64 d -> getr regs 11 = w64 n -> getr regs 12 = w64 f -> getr regs 13 = w64 ap ->
consts_view W mem cr -> Forall (fun r => 0 <= fst r /\ fst r + snd r <= 2 ^ 63) cr ->
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
(* ---- musl vsnprintf (d, n, f, ap), as the interceptor's REAL ---- *)
Definition sh_avsnprintf_realizes_x (FF : fmt_fam) (K gc gv img_lo img_hi : Z) (cr : list (Z * Z)) (pc : Z) : Prop :=
forall ly S (Hp : list Z) W regs mem md d n f ap (ws T : list Z) cval,
ecall_pre_x segs B ARx ly S Hp W regs mem md ->
ly_stk_lo ly + K <= spZ regs ->
(forall a, spZ regs - K <= a < spZ regs -> apresent (w_H W) mem a) ->
getr regs 10 = w64 d -> getr regs 11 = w64 n -> getr regs 12 = w64 f -> getr regs 13 = w64 ap ->
consts_view W mem cr -> Forall (fun r => 0 <= fst r /\ fst r + snd r <= 2 ^ 63) cr ->
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
(* ---- the vfprintf interceptor (fp, f, ap) on musl vsnprintf's FILE fp (sn_write snw, buffer bp, cookie cp = {s0, n0}) ---- *)
Definition sh_avfprintf_icpt_realizes_x (FF : fmt_fam) (K gc gv img_lo img_hi : Z) (cr : list (Z * Z)) (snw pc : Z) : Prop :=
forall ly S (Hp : list Z) W regs mem md fp f ap bp cp s0 n0 (ws T : list Z) cval,
ecall_pre_x segs B ARx ly S Hp W regs mem md ->
ly_stk_lo ly + K <= spZ regs ->
(forall a, spZ regs - K <= a < spZ regs -> apresent (w_H W) mem a) ->
getr regs 10 = w64 fp -> getr regs 11 = w64 f -> getr regs 12 = w64 ap ->
words_at (aview segs (w_H W) mem) fp (sn_file snw bp cp) -> 0 < bp ->
words_at (aview segs (w_H W) mem) cp [s0; n0] ->
dest_ok segs B ly S W regs mem fp 232 -> dest_ok segs B ly S W regs mem cp 16 ->
0 <= fp -> fp + 232 <= 2 ^ 63 -> 0 <= cp -> cp + 16 <= 2 ^ 63 ->
consts_view W mem cr -> Forall (fun r => 0 <= fst r /\ fst r + snd r <= 2 ^ 63) cr ->
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
(* dest_off_globals: the caller discharges it by measurement *) zdisjoint (s0, sn_len n0 T) (img_lo, img_hi - img_lo) ->
(* frm0_entry: rounding mode 0 at entry (GXA VfprintfCall.v:37) *) Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
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
Definition sh_avfprintf_realizes_x (FF : fmt_fam) (K gc gv img_lo img_hi : Z) (cr : list (Z * Z)) (snw pc : Z) : Prop :=
sh_avfprintf_icpt_realizes_x FF K gc gv img_lo img_hi cr snw pc.

(* ---- ASan's printf_common (ctx, format, aq) (RtPrintf.Pcommon): reads the format and the %s / %.*s strings, checks
   them, writes only its own stack window, returns nothing the caller uses ---- *)
Definition sh_apcommon_realizes_x (FF : fmt_fam) (K : Z) (cr : list (Z * Z)) (pc : Z) : Prop :=
forall ly S (Hp : list Z) W regs mem md f ap (ws T : list Z),
ecall_pre_x segs B ARx ly S Hp W regs mem md -> ly_stk_lo ly + K <= spZ regs ->
(forall a, spZ regs - K <= a < spZ regs -> apresent (w_H W) mem a) ->
getr regs 11 = w64 f -> getr regs 12 = w64 ap ->
consts_view W mem cr -> Forall (fun r => 0 <= fst r /\ fst r + snd r <= 2 ^ 63) cr ->
Forall (zdisjoint (spZ regs - K, K)) cr ->
words_at (aview segs (w_H W) mem) ap ws -> spZ regs <= ap -> ap + 8 * Z.of_nat (length ws) < 2 ^ 63 ->
FF (aview segs (w_H W) mem) [(spZ regs - K, K)] f ws T ->
SRr segs W (cfg_at segs pc regs mem md) (fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at segs (raZ regs) regs' mem' md' /\ ARx ly S Hp W mem' md' /\ aregs_preserved regs regs' /\
same_but_materialized md md' /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - K <= a < spZ regs) -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a) /\
(YAkMemnorm.memnorm segs mem -> YAkMemnorm.memnorm segs mem')).

(* re-pin: the non-FP fields of a config are independent of the FP state, so a consumer that reads neither fa0
   nor the fcsr continues at the post's fx' with the same integer, memory and pc state. *)
Lemma cfg_at_fx_fields : forall (fx1 fx2 : YK11.FPState) pc regs mem md,
  @cfg_at fx1 segs pc regs mem md = mkCfg (@YK11.mkst fx1 regs (w64 pc) mem (seg_rom segs)) md /\
  ms_regs (@YK11.mkst fx1 regs (w64 pc) mem (seg_rom segs)) = ms_regs (@YK11.mkst fx2 regs (w64 pc) mem (seg_rom segs)) /\
  ms_mem (@YK11.mkst fx1 regs (w64 pc) mem (seg_rom segs)) = ms_mem (@YK11.mkst fx2 regs (w64 pc) mem (seg_rom segs)) /\
  ms_pc_val (@YK11.mkst fx1 regs (w64 pc) mem (seg_rom segs)) = ms_pc_val (@YK11.mkst fx2 regs (w64 pc) mem (seg_rom segs)).
Proof. intros. repeat split; reflexivity. Qed.

End s.


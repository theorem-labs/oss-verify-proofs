(* Modified by Theorem Labs, 2026-10: relocated from omx-clap-core/fuzz_manifest lib/A/FMsnprintfShared.v (a working branch 3e35620c52e) to libreac/fuzz_boxreg lib/A/Rt (image-neutral; both images use it): module paths changed; 0 address numerals relocated (port_addr_check 0767e70e074a predict mode, symbol + offset); re-pointed Requires: FMupoison, FMsnprintfPf -> lib.A.Rt. Supersedes the older relocation of this file. Re-pointed from 7e395de08f5 to 3e35620c52e by applying fm's own diff of this file (the destination slack amem_range d (sn_len (n - 1) T + 8) in both shared statements; 0 address numerals). *)
(* The snprintf contracts every Pau target shares (statements): a Theorem Labs lane's lib/Rt/SnprintfDef.v and VsnprintfDef.v
   (a working branch 4a8b5df89c3) restated over fm's library, with pieces, parser and renderer in
   FMsnprintfPf.v. Kept as there: the arguments (va_words: a3..a7 then the caller's stack slots at sp; words_at ap for
   the v* entries), the read-only constants a run reads (consts_view cr), the stack-protector cells gc -> gv -> cval,
   the disjointness lists (no alloc_ceiling: the destination and the strings may lie on the machine stack outside the
   callee's window), 1 <= n < 2^31, a0 = |T| (the untruncated length).
   Changed:
   - the format family is a parameter FF rd rs f ws T: "the format at f, with the argument words ws, reads only bytes
     disjoint from the regions rs and renders T". pf_family PK is a Theorem Labs lane's family (fmt_at, pf_parse, pf_args_asan,
     pf_text) for the conversions PK covers, with every %.*s precision >= 1 (pf_prec_pos, true for a PK without Pps):
     a Theorem Labs lane: pf_family pf_disco_piece, fm: pf_family pf_fm_piece; other units define their own FF;
   - the stack windows (a Theorem Labs lane's SNPRINTF_STK, VSNPRINTF_ICPT_STK, VSNPRINTF_STK, VFPRINTF_ICPT_STK) are a parameter K
     of each contract (fm's chain needs 3 * ESTACK at the snprintf entry);
   - the truncating post is GXA's form (fuzz_reply lib/CJ/RL/GXA/G_vfprintf_snf.v vfprintf_snf_a_post, origin/ossv/recipes):
     sn_bytes N T = firstn N T ++ [0] at d, N = n - 1 (the cookie's count), nothing else written outside the window;
   - every destination premise (the disjointness lists, dest_ok, amem_range, the shadow) is over the written part
     w = sn_len (n - 1) T = min (|T|, n - 1) + 1 only (GXA's dn; ASan's WRITE_RANGE (str, min (size, res + 1)));
   - each contract is stated over Poison's user-poisoned ranges U (FMupoison.v: ecall_preU, ARU in the post; fm calls
     snprintf inside a poison window); a Theorem Labs lane's form (ecall_pre, AR) is its U = [] instance (sh_*_of_U).
   The entries are separate contracts: snprintf, the vsnprintf interceptor, musl vsnprintf, the vfprintf interceptor
   on musl vsnprintf's FILE (musl vfprintf: the same interface), and ASan's printf_common (a Theorem Labs lane's text).
   ff_stable / ff_mono are what a family gives the format-generic chain. *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Rt Require Import FMupoison.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Rt Require Import FMsnprintfPf.
Import ListNotations.
Local Open Scope Z_scope.

(* ---- as in a Theorem Labs lane's SnprintfDef.v ---- *)
Definition words_at (rd : reader) (p : Z) (ws : list Z) : Prop :=
forall i, (i < length ws)%nat -> rdword rd (p + 8 * Z.of_nat i) = Some (nth i ws 0).
Definition va_words (regs : bvmap 5 word) (rd : reader) (sp : Z) (xs ws : list Z) : Prop :=
ws = map (argZ regs) [3; 4; 5; 6; 7] ++ xs /\ words_at rd sp xs.
Definition str_end (w : Z) (s : list Z) : Z :=
w + Z.of_nat (length s) - (w + Z.of_nat (length s)) mod 8 + 8.
Definition pf_arg_asan (rd : reader) (rs : list (Z * Z)) (w : Z) (a : pf_arg) : Prop :=
match a with
| AInt v => -2 ^ 31 <= v < 2 ^ 31 /\ w mod 2 ^ 32 = v mod 2 ^ 32
| AU64 u => w = u
| APtr s =>
Forall (fun c => 0 < c < 256) s /\ 0 < w /\ Z.of_nat (length s) + 8 < 2 ^ 31 /\
(forall i, 0 <= i <= Z.of_nat (length s) -> rd (w + i) = Some (nth (Z.to_nat i) (s ++ [0]) 0)) /\
(forall x, w + Z.of_nat (length s) < x < str_end w s -> rd x <> None) /\
Forall (zdisjoint (w, str_end w s - w)) rs /\
amem_range w (Z.of_nat (length s) + 1) /\
range_addressable rd SHADOW_OFF w (Z.of_nat (length s) + 1) /\
shadow_hull_vis rd w (Z.of_nat (length s) + 1)
end.
Fixpoint pf_args_asan (rd : reader) (rs : list (Z * Z)) (ws : list Z) (args : list pf_arg) : Prop :=
match args, ws with
| [], _ => True
| a :: args', w :: ws' => pf_arg_asan rd rs w a /\ pf_args_asan rd rs ws' args'
| _ :: _, [] => False
end.
Definition fmt_at (rd : reader) (rs : list (Z * Z)) (f : Z) (fmt : list Z) : Prop :=
0 < f /\
(forall i, 0 <= i <= Z.of_nat (length fmt) -> rd (f + i) = Some (nth (Z.to_nat i) (fmt ++ [0]) 0)) /\
Forall (zdisjoint (f, Z.of_nat (length fmt) + 1)) rs /\
amem_range f (Z.of_nat (length fmt) + 1) /\
range_addressable rd SHADOW_OFF f (Z.of_nat (length fmt) + 1) /\
shadow_hull_vis rd f (Z.of_nat (length fmt) + 1).
Definition snp_out (K sp d n : Z) : list (Z * Z) := [(sp - K, K); (d, n)].
Definition sn_file (snw bp cp : Z) : list Z :=
[0; 0; 0; 0; 0; 0; 0; 0; 0; snw; 0; bp; 0; 0; 0; 0; 0; 0xffffffff00000000; 0xffffffff; cp;
0; 0; 0; 0; 0; 0; 0; 0; 0].
(* ((s0, n0 + 1); here the written part w) *)
Definition vfp_out (K sp s0 w fp cp : Z) : list (Z * Z) := [(sp - K, K); (s0, w); (fp, 232); (cp, 16)].

(* ---- format families ---- *)
(* rd = the memory's reader, rs = the regions a run writes, f = the format, ws = the argument words, T = the text *)
Definition fmt_fam : Type := reader -> list (Z * Z) -> Z -> list Z -> list Z -> Prop.
(* fm's conversions: literal bytes, %s, %.*s *)
Definition pf_fm_piece (p : pf_piece) : Prop :=
match p with PLit _ | Ps | Pps => True | _ => False end.
(* every %.*s precision is at least 1 (pf_text already asks k <= len s) *)
Fixpoint pf_prec_pos (ps : list pf_piece) (args : list pf_arg) : Prop :=
match ps, args with
| [], _ => True
| PLit _ :: ps', _ => pf_prec_pos ps' args
| Pps :: ps', AInt k :: _ :: a' => 1 <= k /\ pf_prec_pos ps' a'
| Pps :: _, _ => True
| _ :: ps', _ :: a' => pf_prec_pos ps' a'
| _ :: _, [] => True
end.
(* a Theorem Labs lane's family for the conversions PK covers *)
Definition pf_family (PK : pf_piece -> Prop) : fmt_fam := fun rd rs f ws T =>
exists (fmt : list Z) (ps : list pf_piece) (args : list pf_arg),
fmt_at rd rs f fmt /\ pf_parse fmt = Some ps /\ Forall PK ps /\ pf_args_asan rd rs ws args /\
pf_text ps args = Some T /\ pf_prec_pos ps args.
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
Definition consts_view (W : world segs) (mem : word -> option byte) (cr : list (Z * Z)) : Prop :=
forall a, Exists (in_zr a) cr -> aview segs (w_H W) mem a = option_map (fun b : byte => bv_unsigned b) (seg_rom segs (Z_to_bv 64 a)).

(* ---- snprintf (d, n, f, ...), entered with a stack window of K bytes ---- *)
Definition sh_asnprintf_realizesU (FF : fmt_fam) (K gc gv img_lo img_hi : Z) (cr : list (Z * Z)) (pc : Z) : Prop :=
forall ly S (U : list (Z * Z)) W regs mem md d n f (xs ws T : list Z) cval,
ecall_preU segs B ly S U W regs mem md ->
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
ARU segs B ly S U W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = w64 (Z.of_nat (length T)) /\
(forall i, 0 <= i < sn_len (n - 1) T -> aview segs (w_H W) mem' (d + i) = Some (nth (Z.to_nat i) (sn_bytes (n - 1) T) 0)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + sn_len (n - 1) T) ->
~ (spZ regs - K <= a < spZ regs) -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
(* a Theorem Labs lane's form: no user-poisoned range *)
Definition sh_asnprintf_realizes (FF : fmt_fam) (K gc gv img_lo img_hi : Z) (cr : list (Z * Z)) (pc : Z) : Prop :=
forall ly S W regs mem md d n f (xs ws T : list Z) cval,
ecall_pre segs B ly S W regs mem md ->
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
AR segs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = w64 (Z.of_nat (length T)) /\
(forall i, 0 <= i < sn_len (n - 1) T -> aview segs (w_H W) mem' (d + i) = Some (nth (Z.to_nat i) (sn_bytes (n - 1) T) 0)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + sn_len (n - 1) T) ->
~ (spZ regs - K <= a < spZ regs) -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).

(* ---- the vsnprintf interceptor (d, n, f, ap): the arguments are the words at ap ---- *)
Definition sh_avsnprintf_icpt_realizesU (FF : fmt_fam) (K gc gv img_lo img_hi : Z) (cr : list (Z * Z)) (pc : Z) : Prop :=
forall ly S (U : list (Z * Z)) W regs mem md d n f ap (ws T : list Z) cval,
ecall_preU segs B ly S U W regs mem md ->
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
ARU segs B ly S U W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = w64 (Z.of_nat (length T)) /\
(forall i, 0 <= i < sn_len (n - 1) T -> aview segs (w_H W) mem' (d + i) = Some (nth (Z.to_nat i) (sn_bytes (n - 1) T) 0)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + sn_len (n - 1) T) ->
~ (spZ regs - K <= a < spZ regs) -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
Definition sh_avsnprintf_icpt_realizes (FF : fmt_fam) (K gc gv img_lo img_hi : Z) (cr : list (Z * Z)) (pc : Z) : Prop :=
forall ly S W regs mem md d n f ap (ws T : list Z) cval,
ecall_pre segs B ly S W regs mem md ->
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
AR segs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = w64 (Z.of_nat (length T)) /\
(forall i, 0 <= i < sn_len (n - 1) T -> aview segs (w_H W) mem' (d + i) = Some (nth (Z.to_nat i) (sn_bytes (n - 1) T) 0)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + sn_len (n - 1) T) ->
~ (spZ regs - K <= a < spZ regs) -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).

(* ---- musl vsnprintf (d, n, f, ap), as the interceptor's REAL ---- *)
Definition sh_avsnprintf_realizesU (FF : fmt_fam) (K gc gv img_lo img_hi : Z) (cr : list (Z * Z)) (pc : Z) : Prop :=
forall ly S (U : list (Z * Z)) W regs mem md d n f ap (ws T : list Z) cval,
ecall_preU segs B ly S U W regs mem md ->
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
ARU segs B ly S U W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = w64 (Z.of_nat (length T)) /\
(forall i, 0 <= i < sn_len (n - 1) T -> aview segs (w_H W) mem' (d + i) = Some (nth (Z.to_nat i) (sn_bytes (n - 1) T) 0)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + sn_len (n - 1) T) ->
~ (spZ regs - K <= a < spZ regs) -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
Definition sh_avsnprintf_realizes (FF : fmt_fam) (K gc gv img_lo img_hi : Z) (cr : list (Z * Z)) (pc : Z) : Prop :=
forall ly S W regs mem md d n f ap (ws T : list Z) cval,
ecall_pre segs B ly S W regs mem md ->
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
AR segs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = w64 (Z.of_nat (length T)) /\
(forall i, 0 <= i < sn_len (n - 1) T -> aview segs (w_H W) mem' (d + i) = Some (nth (Z.to_nat i) (sn_bytes (n - 1) T) 0)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + sn_len (n - 1) T) ->
~ (spZ regs - K <= a < spZ regs) -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).

(* ---- the vfprintf interceptor (fp, f, ap) on musl vsnprintf's FILE fp (sn_write snw, buffer bp, cookie cp = {s0, n0}) ---- *)
Definition sh_avfprintf_icpt_realizesU (FF : fmt_fam) (K gc gv img_lo img_hi : Z) (cr : list (Z * Z)) (snw pc : Z) : Prop :=
forall ly S (U : list (Z * Z)) W regs mem md fp f ap bp cp s0 n0 (ws T : list Z) cval,
ecall_preU segs B ly S U W regs mem md ->
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
ARU segs B ly S U W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = w64 (Z.of_nat (length T)) /\
(forall i, 0 <= i < sn_len n0 T -> aview segs (w_H W) mem' (s0 + i) = Some (nth (Z.to_nat i) (sn_bytes n0 T) 0)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (s0 <= a < s0 + sn_len n0 T) ->
~ Exists (in_zr a) [(spZ regs - K, K); (fp, 232); (cp, 16)] -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
Definition sh_avfprintf_icpt_realizes (FF : fmt_fam) (K gc gv img_lo img_hi : Z) (cr : list (Z * Z)) (snw pc : Z) : Prop :=
forall ly S W regs mem md fp f ap bp cp s0 n0 (ws T : list Z) cval,
ecall_pre segs B ly S W regs mem md ->
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
AR segs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = w64 (Z.of_nat (length T)) /\
(forall i, 0 <= i < sn_len n0 T -> aview segs (w_H W) mem' (s0 + i) = Some (nth (Z.to_nat i) (sn_bytes n0 T) 0)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (s0 <= a < s0 + sn_len n0 T) ->
~ Exists (in_zr a) [(spZ regs - K, K); (fp, 232); (cp, 16)] -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
(* musl vfprintf on the same FILE: the interceptor's interface *)
Definition sh_avfprintf_realizesU (FF : fmt_fam) (K gc gv img_lo img_hi : Z) (cr : list (Z * Z)) (snw pc : Z) : Prop :=
sh_avfprintf_icpt_realizesU FF K gc gv img_lo img_hi cr snw pc.

(* ---- ASan's printf_common (ctx, format, aq) (a Theorem Labs lane): reads the format and the %s / %.*s strings, checks
   them, writes only its own stack window, returns nothing the caller uses ---- *)
Definition sh_apcommon_realizesU (FF : fmt_fam) (K : Z) (cr : list (Z * Z)) (pc : Z) : Prop :=
forall ly S (U : list (Z * Z)) W regs mem md f ap (ws T : list Z),
ecall_preU segs B ly S U W regs mem md -> ly_stk_lo ly + K <= spZ regs ->
(forall a, spZ regs - K <= a < spZ regs -> apresent (w_H W) mem a) ->
getr regs 11 = w64 f -> getr regs 12 = w64 ap ->
consts_view W mem cr -> Forall (fun r => 0 <= fst r /\ fst r + snd r <= 2 ^ 63) cr ->
Forall (zdisjoint (spZ regs - K, K)) cr ->
words_at (aview segs (w_H W) mem) ap ws -> spZ regs <= ap -> ap + 8 * Z.of_nat (length ws) < 2 ^ 63 ->
FF (aview segs (w_H W) mem) [(spZ regs - K, K)] f ws T ->
SRr segs W (cfg_at segs pc regs mem md) (fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at segs (raZ regs) regs' mem' md' /\ ARU segs B ly S U W mem' md' /\ aregs_preserved regs regs' /\
same_but_materialized md md' /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - K <= a < spZ regs) -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).

(* ---- the AR forms are the U = [] instances ---- *)
Lemma sh_asnprintf_of_U : forall FF K gc gv img_lo img_hi cr pc,
  sh_asnprintf_realizesU FF K gc gv img_lo img_hi cr pc -> sh_asnprintf_realizes FF K gc gv img_lo img_hi cr pc.
Proof.
intros FF K gc gv img_lo img_hi cr pc HU ly S W regs mem md d n f xs ws T cval Hpre. intros.
eapply SRr_mono.
- apply (HU ly S [] W regs mem md d n f xs ws T cval); try eassumption.
  apply ecall_preU_nil. exact Hpre.
- intros W' c' _ (-> & fx' & regs' & mem' & md' & -> & Hf1 & Hf2 & HA & R). split; [reflexivity|]. exists fx', regs', mem', md'.
  split; [reflexivity|]. split; [exact Hf1|]. split; [exact Hf2|]. split; [apply ARU_nil in HA; exact HA | exact R].
Qed.
Lemma sh_avsnprintf_icpt_of_U : forall FF K gc gv img_lo img_hi cr pc,
  sh_avsnprintf_icpt_realizesU FF K gc gv img_lo img_hi cr pc -> sh_avsnprintf_icpt_realizes FF K gc gv img_lo img_hi cr pc.
Proof.
intros FF K gc gv img_lo img_hi cr pc HU ly S W regs mem md d n f ap ws T cval Hpre. intros.
eapply SRr_mono.
- apply (HU ly S [] W regs mem md d n f ap ws T cval); try eassumption.
  apply ecall_preU_nil. exact Hpre.
- intros W' c' _ (-> & fx' & regs' & mem' & md' & -> & Hf1 & Hf2 & HA & R). split; [reflexivity|]. exists fx', regs', mem', md'.
  split; [reflexivity|]. split; [exact Hf1|]. split; [exact Hf2|]. split; [apply ARU_nil in HA; exact HA | exact R].
Qed.
Lemma sh_avsnprintf_of_U : forall FF K gc gv img_lo img_hi cr pc,
  sh_avsnprintf_realizesU FF K gc gv img_lo img_hi cr pc -> sh_avsnprintf_realizes FF K gc gv img_lo img_hi cr pc.
Proof.
intros FF K gc gv img_lo img_hi cr pc HU ly S W regs mem md d n f ap ws T cval Hpre. intros.
eapply SRr_mono.
- apply (HU ly S [] W regs mem md d n f ap ws T cval); try eassumption.
  apply ecall_preU_nil. exact Hpre.
- intros W' c' _ (-> & fx' & regs' & mem' & md' & -> & Hf1 & Hf2 & HA & R). split; [reflexivity|]. exists fx', regs', mem', md'.
  split; [reflexivity|]. split; [exact Hf1|]. split; [exact Hf2|]. split; [apply ARU_nil in HA; exact HA | exact R].
Qed.
Lemma sh_avfprintf_icpt_of_U : forall FF K gc gv img_lo img_hi cr snw pc,
  sh_avfprintf_icpt_realizesU FF K gc gv img_lo img_hi cr snw pc -> sh_avfprintf_icpt_realizes FF K gc gv img_lo img_hi cr snw pc.
Proof.
intros FF K gc gv img_lo img_hi cr snw pc HU ly S W regs mem md fp f ap bp cp s0 n0 ws T cval Hpre. intros.
eapply SRr_mono.
- apply (HU ly S [] W regs mem md fp f ap bp cp s0 n0 ws T cval); try eassumption.
  apply ecall_preU_nil. exact Hpre.
- intros W' c' _ (-> & fx' & regs' & mem' & md' & -> & Hf1 & Hf2 & HA & R). split; [reflexivity|]. exists fx', regs', mem', md'.
  split; [reflexivity|]. split; [exact Hf1|]. split; [exact Hf2|]. split; [apply ARU_nil in HA; exact HA | exact R].
Qed.
(* re-pin: the non-FP fields of a config are independent of the FP state, so a consumer that reads neither fa0
   nor the fcsr continues at the post's fx' with the same integer, memory and pc state. *)
Lemma cfg_at_fx_fields : forall (fx1 fx2 : YK11.FPState) pc regs mem md,
  @cfg_at fx1 segs pc regs mem md = mkCfg (@YK11.mkst fx1 regs (w64 pc) mem (seg_rom segs)) md /\
  ms_regs (@YK11.mkst fx1 regs (w64 pc) mem (seg_rom segs)) = ms_regs (@YK11.mkst fx2 regs (w64 pc) mem (seg_rom segs)) /\
  ms_mem (@YK11.mkst fx1 regs (w64 pc) mem (seg_rom segs)) = ms_mem (@YK11.mkst fx2 regs (w64 pc) mem (seg_rom segs)) /\
  ms_pc_val (@YK11.mkst fx1 regs (w64 pc) mem (seg_rom segs)) = ms_pc_val (@YK11.mkst fx2 regs (w64 pc) mem (seg_rom segs)).
Proof. intros. repeat split; reflexivity. Qed.

End s.

(* a Theorem Labs lane's conversions satisfy pf_prec_pos (they have no %.*s) *)
Lemma pf_prec_pos_nopps : forall ps args, Forall (fun p => p <> Pps) ps -> pf_prec_pos ps args.
Proof.
intros ps. induction ps as [|p ps IH]; intros args Hp; [exact I|].
inversion Hp as [|? ? Hne Hps]; subst.
destruct p; cbn [pf_prec_pos]; try (destruct args; [exact I | apply IH; exact Hps]).
- apply IH. exact Hps.
- exfalso. apply Hne. reflexivity.
Qed.
Lemma pf_disco_prec_pos : forall ps args, Forall pf_disco_piece ps -> pf_prec_pos ps args.
Proof.
intros ps args H. apply pf_prec_pos_nopps. eapply Forall_impl; [|exact H].
intros p Hp E. subst p. exact Hp.
Qed.


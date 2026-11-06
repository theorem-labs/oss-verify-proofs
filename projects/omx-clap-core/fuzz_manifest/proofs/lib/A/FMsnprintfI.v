(* fm's snprintf walks (lib/A/FMsnprintf*.v), interface: the snprintf sink and the contracts the walks hand to each
   other. The chain (fm.asan, MEASURED from the unstripped twin):
     __wrap_snprintf 0x41314 -> __interceptor_snprintf 0x45c90 -> __interceptor_vsnprintf 0x458a0
       [printf_common 0x44d24; REAL = musl vsnprintf 0x91f0c -> __wrap_vfprintf 0x41308 -> __interceptor_vfprintf 0x457ec
         [printf_common; REAL = musl vfprintf 0x8ede0 -> printf_core 0x8ef90 (f = 0, then f = FILE)
           -> __fwritex 0x8ea20 -> sn_write 0x91fd8; flush sn_write (f, 0, 0)]; WRITE_RANGE (str, min (size, res + 1))]
   Frame base sp0 = musl vfprintf's entry sp. musl vsnprintf's FILE lies at sp0 + FO, its cookie {s, n} at sp0 + CKO,
   vfprintf's 80-byte internal buffer at sp0 + IBO, vfprintf's ap2 at sp0 + OSP_PC, nl_arg / nl_type after it. Every
   call below vfprintf writes only the band [sp0 - SNK_STK, sp0 + 0x200), the sink cells and the destination. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YK11 YK0s YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YC20 YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import AB1v AE39 FMupoison FMH_Base FMH_Rt.
Import ListNotations.
Local Open Scope Z_scope.

(* ---- fm.asan addresses ---- *)
Definition A_SNI : Z := 0x45c90.    (* __interceptor_snprintf *)
Definition A_VSNI : Z := 0x458a0.   (* __interceptor_vsnprintf *)
Definition A_PCOM : Z := 0x44d24.   (* printf_common (ctx, format, aq) *)
Definition A_VFPI : Z := 0x457ec.   (* __interceptor_vfprintf *)
Definition A_VSN : Z := 0x91f0c.    (* musl vsnprintf *)
Definition A_VFP : Z := 0x8ede0.    (* musl vfprintf *)
Definition A_PCORE : Z := 0x8ef90.  (* musl printf_core *)
Definition A_FWX : Z := 0x8ea20.    (* musl __fwritex *)
Definition A_SNW : Z := 0x91fd8.    (* musl sn_write *)
Definition W_MEMCPY : Z := 0x51a64. (* __wrap_memcpy *)
Definition W_MEMSET : Z := 0x51a60. (* __wrap_memset *)
Definition W_STRNLEN : Z := 0x412cc. (* __wrap_strnlen *)
Definition W_VFPRINTF : Z := 0x41308.
Definition RA_PCORE0 : Z := 0x8ee48. (* vfprintf's return points: printf_core (0, ..) *)
Definition RA_PCORE : Z := 0x8eee8. (* printf_core (f, ..) *)
Definition RA_FLUSH : Z := 0x8ef08. (* f->write (f, 0, 0) *)

(* ---- frame offsets from sp0 (the code is byte-identical to cgif_file.asan's, measured there and in fm.asan) ---- *)
Definition FO : Z := 0x30.          (* musl vsnprintf's FILE *)
Definition CKO : Z := FO + 0xe8.    (* its cookie {s, n} *)
Definition IBO : Z := -352.         (* vfprintf's internal_buf[80] *)
Definition OSP_PC : Z := -368.      (* sp at printf_core's entry = &ap2; nl_arg at +0x60, nl_type at +0x108 *)
Definition OSP_FW : Z := -912.      (* sp at __fwritex / sn_write entry from printf_core's out() *)
Definition SNK_STK : Z := 9104.     (* the band below sp0 the chain below vfprintf uses (donor VF_STK) *)
Definition snk_band (sp0 a : Z) : Prop := sp0 - SNK_STK <= a < sp0 + 0x200.

Section i. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
#[local] Abbreviation segs := tfibsegs.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* the sink after the bytes out have been formatted, the last b of them still in the internal buffer, the first
   w = len out - b of them and a NUL in the destination [D, D + N) behind the cookie *)
Definition SNK (W : world segs) (mem : word -> option byte) (sp0 D N : Z) (out : list Z) (b : Z) : Prop :=
let w := Z.of_nat (length out) - b in
val_mem segs (rdW W mem) (sp0 + FO) 4 0 /\
val_mem segs (rdW W mem) (sp0 + FO + 32) 8 (sp0 + IBO + 80) /\
val_mem segs (rdW W mem) (sp0 + FO + 40) 8 (sp0 + IBO + b) /\
val_mem segs (rdW W mem) (sp0 + FO + 56) 8 (sp0 + IBO) /\
val_mem segs (rdW W mem) (sp0 + FO + 72) 8 A_SNW /\
val_mem segs (rdW W mem) (sp0 + FO + 88) 8 (sp0 + IBO) /\
val_mem segs (rdW W mem) (sp0 + FO + 144) 4 0xffffffff /\
val_mem segs (rdW W mem) (sp0 + FO + 152) 8 (sp0 + CKO) /\
val_mem segs (rdW W mem) (sp0 + CKO) 8 (D + w) /\
val_mem segs (rdW W mem) (sp0 + CKO + 8) 8 (N - 1 - w) /\
(forall i, 0 <= i < b -> aview segs (w_H W) mem (sp0 + IBO + i) = Some (nth (Z.to_nat (w + i)) out 0)) /\
(forall i, 0 <= i < w -> aview segs (w_H W) mem (D + i) = Some (nth (Z.to_nat i) out 0)) /\
aview segs (w_H W) mem (D + w) = Some 0 /\
0 <= b <= 80 /\ b <= Z.of_nat (length out) /\ Z.of_nat (length out) <= N - 1 /\ N <= 2 ^ 30 /\
Forall (fun z => 0 <= z < 256) out.
(* the cells a sink call may write: the internal buffer, wpos / wbase, the cookie, the written destination [D, D + M)
   (M <= N: the bytes the whole snprintf writes, out and its NUL) *)
Definition fw_xw (sp0 D M a : Z) : Prop :=
(sp0 + IBO <= a < sp0 + IBO + 80) \/ (sp0 + FO + 40 <= a < sp0 + FO + 64) \/
(sp0 + CKO <= a < sp0 + CKO + 16) \/ (D <= a < D + M).
(* what holds at sp0 for the whole chain below vfprintf: the user-poison-aware AR, the stack above alloc_ceiling
   (so every C string and the destination lie below the band), the band present with zero shadow *)
Definition snk_base (ly : alayout) (S : astate) (U : list (Z * Z)) (W : world segs) (mem : word -> option byte)
(md : Model) (sp0 : Z) : Prop :=
ARU segs B ly S U W mem md /\ alloc_ceiling <= ly_stk_lo ly /\
2 ^ 44 <= sp0 /\ sp0 mod 16 = 0 /\ ly_stk_lo ly + SNK_STK <= sp0 /\ sp0 + 0x200 <= ly_stk_hi ly /\
sp0 + 0x200 <= 2 ^ 47 /\ kHighMemBeg <= sp0 - SNK_STK /\
(forall a, snk_band sp0 a -> apresent (w_H W) mem a) /\
zero_shadow (aview segs (w_H W) mem) SHADOW_OFF (sp0 - SNK_STK) (SNK_STK + 0x200).
(* what a call below vfprintf keeps: snk_base's AR part, the band present, every byte outside the cells XW it may
   write (fw_xw for a sink call, none for the first printf_core pass) and outside the stack below its caller's frame
   [sp0 - SNK_STK, top) *)
Definition snk_frame (ly : alayout) (S : astate) (U : list (Z * Z)) (W : world segs) (mem : word -> option byte)
(md : Model) (sp0 top : Z) (XW : Z -> Prop) (mem' : word -> option byte) (md' : Model) : Prop :=
ARU segs B ly S U W mem' md' /\ same_but_materialized md md' /\
(forall a, snk_band sp0 a -> apresent (w_H W) mem' a) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - SNK_STK <= a < top) -> ~ XW a ->
aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a).
(* the written destination [D, D + M): below alloc_ceiling (so below the band), writable, not runtime-owned, no
   read-only image byte (the walks keep reading the format and printf_core's tables), addressable, away from the
   stack-protector guard every frame of the chain re-reads *)
Definition snk_dest (ly : alayout) (S : astate) (W : world segs) (mem : word -> option byte) (D M : Z) : Prop :=
0 < D /\ D + M <= alloc_ceiling /\ 1 <= M <= 2 ^ 30 /\ (D + M <= FM_canary \/ FM_canary + 8 <= D) /\
(forall a, D <= a < D + M -> writable_at segs (rdW W mem) a /\ ~ aowned B ly S a /\ ~ in_rom segs a) /\
amem_range D M /\ range_addressable (aview segs (w_H W) mem) SHADOW_OFF D M /\
shadow_hull_vis (aview segs (w_H W) mem) D M.
(* the bytes bs at x that __fwritex copies: a literal run of the format or a %s / %.*s string, below alloc_ceiling
   and away from the destination *)
Definition fw_src (W : world segs) (mem : word -> option byte) (D M x : Z) (bs : list Z) : Prop :=
let l := Z.of_nat (length bs) in
0 < x /\ x + l <= alloc_ceiling /\ (x + l <= D \/ D + M <= x) /\
(forall i, 0 <= i < l -> aview segs (w_H W) mem (x + i) = Some (nth (Z.to_nat i) bs 0)) /\
Forall (fun z => 0 <= z < 256) bs /\ amem_range x l /\
range_addressable (aview segs (w_H W) mem) SHADOW_OFF x l /\ (0 < l -> shadow_hull_vis (aview segs (w_H W) mem) x l).
(* the registers every walk below vfprintf starts with *)
Definition snk_regs (regs : bvmap 5 word) (sp : Z) : Prop :=
YK0s.ret_ok (getr regs 1) /\ getr regs 2 = w64 sp /\ getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B).
(* the post of a call below vfprintf: back at ra, the frame kept, callee-saved registers kept, a0 = v *)
Definition snk_post (ly : alayout) (S : astate) (U : list (Z * Z)) (W : world segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (sp0 top : Z) (XW : Z -> Prop) (v : Z) (Q : (word -> option byte) -> Prop)
: world segs -> config -> Prop :=
fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at segs (raZ regs) regs' mem' md' /\ snk_frame ly S U W mem md sp0 top XW mem' md' /\
aregs_preserved regs regs' /\ getr regs' 10 = w64 v /\ Q mem'.

(* __fwritex (x, l, f) from printf_core's out(): appends bs to the sink (no truncation: the cookie has room) *)
Definition afwx_realizesU (pc : Z) : Prop :=
forall ly S U W regs mem md sp0 D N M out b x bs,
snk_base ly S U W mem md sp0 -> snk_regs regs (sp0 + OSP_FW) ->
getr regs 10 = w64 x -> getr regs 11 = w64 (Z.of_nat (length bs)) -> getr regs 12 = w64 (sp0 + FO) ->
SNK W mem sp0 D N out b -> snk_dest ly S W mem D M -> fw_src W mem D M x bs ->
Z.of_nat (length out) + Z.of_nat (length bs) + 1 <= M <= N ->
SRr segs W (cfg_at segs pc regs mem md)
(snk_post ly S U W regs mem md sp0 (sp0 + OSP_FW) (fw_xw sp0 D M) (Z.of_nat (length bs))
(fun mem' => exists b', SNK W mem' sp0 D N (out ++ bs) b')).
(* vfprintf's flush f->write (f, 0, 0) = sn_write: the buffered bytes and a NUL reach the destination *)
Definition asnflush_realizesU (pc : Z) : Prop :=
forall ly S U W regs mem md sp0 D N M out b,
snk_base ly S U W mem md sp0 -> snk_regs regs (sp0 + OSP_PC) ->
getr regs 10 = w64 (sp0 + FO) -> getr regs 11 = w64 0 -> getr regs 12 = w64 0 ->
SNK W mem sp0 D N out b -> snk_dest ly S W mem D M -> Z.of_nat (length out) + 1 <= M <= N ->
SRr segs W (cfg_at segs pc regs mem md)
(snk_post ly S U W regs mem md sp0 (sp0 + OSP_PC) (fw_xw sp0 D M) 0 (fun mem' => SNK W mem' sp0 D N out 0)).
(* the arguments: 8-byte slots at P *)
Definition slots_at (W : world segs) (mem : word -> option byte) (P : Z) (args : list Z) : Prop :=
forall i, (i < length args)%nat -> val_mem segs (rdW W mem) (P + 8 * Z.of_nat i) 8 (nth i args 0).
(* printf_core (f, fmt, &ap2, nl_arg, nl_type), f = the FILE, for one of fm's formats: renders out into the sink *)
Definition apcore_realizesU (pc : Z) : Prop :=
forall ly S U W regs mem md sp0 D N M f ps P args out,
snk_base ly S U W mem md sp0 -> snk_regs regs (sp0 + OSP_PC) -> rom_viewN segs B W mem ->
getr regs 10 = w64 (sp0 + FO) -> getr regs 11 = w64 f -> getr regs 12 = w64 (sp0 + OSP_PC) ->
getr regs 13 = w64 (sp0 + OSP_PC + 0x60) -> getr regs 14 = w64 (sp0 + OSP_PC + 0x108) ->
In (f, ps) FM_SN_FMTS -> cstr_ok segs W mem f (fmt_bytes ps) -> val_mem segs (rdW W mem) (sp0 + OSP_PC) 8 P ->
sp0 + 0x200 <= P -> P + 8 * Z.of_nat (length args) <= ly_stk_hi ly -> slots_at W mem P args ->
frender segs W mem D N ps args out -> Z.of_nat (length out) + 1 <= M <= N ->
SNK W mem sp0 D N [] 0 -> snk_dest ly S W mem D M ->
SRr segs W (cfg_at segs pc regs mem md)
(snk_post ly S U W regs mem md sp0 (sp0 + OSP_PC + 8) (fw_xw sp0 D M) (Z.of_nat (length out))
(fun mem' => exists b', SNK W mem' sp0 D N out b')).
(* printf_core (0, fmt, &ap2, nl_arg, nl_type): the first pass returns 0 at the first conversion *)
Definition apcore0_realizesU (pc : Z) : Prop :=
forall ly S U W regs mem md sp0 f ps,
snk_base ly S U W mem md sp0 -> snk_regs regs (sp0 + OSP_PC) -> rom_viewN segs B W mem ->
getr regs 10 = w64 0 -> getr regs 11 = w64 f -> getr regs 12 = w64 (sp0 + OSP_PC) ->
getr regs 13 = w64 (sp0 + OSP_PC + 0x60) -> getr regs 14 = w64 (sp0 + OSP_PC + 0x108) ->
In (f, ps) FM_SN_FMTS ->
SRr segs W (cfg_at segs pc regs mem md)
(snk_post ly S U W regs mem md sp0 (sp0 + OSP_PC) (fun _ => False) 0 (fun _ => True)).
(* ASan's printf_common (ctx, format, aq) for one of fm's formats: the %s read checks pass; it writes only its stack
   window [sp - STK_PCOM, sp) *)
Definition STK_PCOM : Z := 2 * ESTACK.
Definition apcommon_realizesU (pc : Z) : Prop :=
forall ly S U W regs mem md f ps P args d n out,
ecall_preU segs B ly S U W regs mem md -> alloc_ceiling <= ly_stk_lo ly ->
ly_stk_lo ly + STK_PCOM <= spZ regs -> (forall a, spZ regs - STK_PCOM <= a < spZ regs -> apresent (w_H W) mem a) ->
rom_viewN segs B W mem -> getr regs 11 = w64 f -> getr regs 12 = w64 P ->
spZ regs <= P -> P + 8 * Z.of_nat (length args) <= ly_stk_hi ly ->
In (f, ps) FM_SN_FMTS -> slots_at W mem P args -> frender segs W mem d n ps args out ->
Z.of_nat (length out) + 1 <= n <= 2 ^ 30 ->
SRr segs W (cfg_at segs pc regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at segs (raZ regs) regs' mem' md' /\
ARU segs B ly S U W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - STK_PCOM <= a < spZ regs) ->
aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
(* ---- runtime calls the walks make, over ARU (Poison's FMupoison.v); proved by ports of the donor's contracts ---- *)
(* memcpy (OCpy) / memset (OSet) interceptor, as YG0d.v aintrin_realizes with ARU in and out. *)
Definition aintrin_realizesU (op : memop) (pc : Z) : Prop :=
forall ly S U W regs mem md d x n,
ecall_preU segs B ly S U W regs mem md ->
getr regs 10 = w64 d -> getr regs 11 = w64 x -> getr regs 12 = w64 n -> 0 <= n < 2 ^ 32 -> 0 <= d -> d + n <= 2 ^ 63 ->
dest_ok segs B ly S W regs mem d n -> amem_range d n ->
range_addressable (aview segs (w_H W) mem) SHADOW_OFF d n -> (0 < n -> shadow_hull_vis (aview segs (w_H W) mem) d n) ->
(match op with
| OCpy => 0 <= x /\ x + n <= 2 ^ 63 /\ src_ok segs W regs mem x n /\ (d + n <= x \/ x + n <= d) /\ amem_range x n /\
range_addressable (aview segs (w_H W) mem) SHADOW_OFF x n /\ (0 < n -> shadow_hull_vis (aview segs (w_H W) mem) x n)
| OSet => True end) ->
SRr segs W (cfg_at segs pc regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at segs (raZ regs) regs' mem' md' /\
ARU segs B ly S U W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = w64 d /\
(forall i, 0 <= i < n -> aview segs (w_H W) mem' (d + i) =
match op with OCpy => aview segs (w_H W) mem (x + i) | OSet => Some (x mod 256) end) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + n) -> ~ (spZ regs - ESTACK <= a < spZ regs) ->
aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
(* strnlen interceptor, NUL found at k with k + 8 <= n: A/AE39.v astrnlen_realizesM with ARU in and out. *)
Definition astrnlen_realizesU (pc : Z) : Prop :=
forall ly S U W regs mem md x n k,
ecall_preU segs B ly S U W regs mem md ->
ly_stk_lo ly + 2 * ESTACK <= spZ regs -> (forall a, spZ regs - 2 * ESTACK <= a < spZ regs -> apresent (w_H W) mem a) ->
getr regs 10 = w64 x -> getr regs 11 = w64 n -> 0 <= n < 2 ^ 63 -> 0 < x ->
0 <= k -> k + 8 <= n -> k + 1 < 2 ^ 32 -> x + k + 1 <= 2 ^ 63 ->
first_byte segs W mem x n 0 k ->
src_ok segs W regs mem x (k + 1) -> (forall a, x <= a <= x + k -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs)) -> amem_range x (k + 1) ->
range_addressable (aview segs (w_H W) mem) SHADOW_OFF x (k + 1) ->
shadow_hull_vis (aview segs (w_H W) mem) x (k + 1) ->
(forall a, x + k < a < x + k - (x + k) mod 8 + 8 -> aview segs (w_H W) mem a <> None) ->
mconsts_view W mem ->
SRr segs W (cfg_at segs pc regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at segs (raZ regs) regs' mem' md' /\
ARU segs B ly S U W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = w64 k /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs) -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
(* strnlen interceptor, no NUL among the first n bytes (the %.*s case): it returns n and reads exactly x .. x + n - 1. *)
Definition astrnlenN_realizesU (pc : Z) : Prop :=
forall ly S U W regs mem md x n,
ecall_preU segs B ly S U W regs mem md ->
ly_stk_lo ly + 2 * ESTACK <= spZ regs -> (forall a, spZ regs - 2 * ESTACK <= a < spZ regs -> apresent (w_H W) mem a) ->
getr regs 10 = w64 x -> getr regs 11 = w64 n -> 1 <= n < 2 ^ 31 -> 0 < x -> x + n <= 2 ^ 63 ->
first_byte segs W mem x n 0 n ->
src_ok segs W regs mem x n -> (forall a, x <= a < x + n -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs)) -> amem_range x n ->
range_addressable (aview segs (w_H W) mem) SHADOW_OFF x n ->
shadow_hull_vis (aview segs (w_H W) mem) x n ->
mconsts_view W mem ->
SRr segs W (cfg_at segs pc regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at segs (raZ regs) regs' mem' md' /\
ARU segs B ly S U W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = w64 n /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs) -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
End i.

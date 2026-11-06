(* fm program part: the runtime contracts fm's target code needs that the donor core does not state, in the donor's
   per-call form (YG0d.v:317-419: ecall_pre, argument registers, range premises on aview, SRr to the return address with
   AR kept, callee-saved registers kept, same_but_materialized, a memory frame). Statements only; the walks are
   a Theorem Labs lane's (strlen, strchr, strncmp, memchr), a Theorem Labs lane's (strstr, strncasecmp, isalnum) and a Theorem Labs lane's (snprintf);
   a sibling that proves its own donor-form Definition of the same name replaces the one here.
   bcmp: the donor's abcmp_realizes (YG0d.v:352) at PC_bcmp. Poison / unpoison: Poison's tfib_poison16 /
   tfib_unpoison16 (design/POISON.md section 7). Design: a Theorem Labs lane's design/HARNESS.md section 4. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YK11 YK0s YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YC20 YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison FMH_Base.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require ManifestModel.
Import ListNotations.
Local Open Scope Z_scope.

(* ---- pure models of the answers ---- *)
(* the first index of c in l *)
Definition first_at (l : list Z) (c : Z) (j : nat) : Prop :=
  (j < length l)%nat /\ nth j l 0 = c /\ ~ In c (firstn j l).
(* strncmp (s1, s2, k) = 0: the first k bytes of each string with its NUL agree (C stops at the first NUL) *)
Definition strn_eq (k : nat) (l1 l2 : list Z) : Prop := firstn k (l1 ++ [0]) = firstn k (l2 ++ [0]).
(* sanitizer_common's ToLower (ASCII) *)
Definition lc (c : Z) : Z := if (65 <=? c) && (c <=? 90) then c + 32 else c.
Definition strncase_eq (k : nat) (l1 l2 : list Z) : Prop :=
  map lc (firstn k (l1 ++ [0])) = map lc (firstn k (l2 ++ [0])).
(* w occurs in t at j *)
Definition occ_at (t w : list Z) (j : nat) : Prop := (j + length w <= length t)%nat /\ firstn (length w) (skipn j t) = w.
Definition first_occ (t w : list Z) (j : nat) : Prop := occ_at t w j /\ forall j', (j' < j)%nat -> ~ occ_at t w j'.
Definition no_occ (t w : list Z) : Prop := forall j, ~ occ_at t w j.
(* memchr (p, 0, n) reads up to and including the first NUL, or all n bytes *)
Definition mchr_len (l : list Z) : Z :=
  match ManifestModel.find_idx (fun c => c =? 0) l with Some k => Z.of_nat k + 1 | None => Z.of_nat (length l) end.

(* ---- snprintf formats: literal runs, %s, %.*s ---- *)
Inductive fpiece : Type := FLit (l : list Z) | FStr | FPStr.
Fixpoint fmt_bytes (ps : list fpiece) : list Z :=
  match ps with
  | [] => []
  | FLit l :: ps' => l ++ fmt_bytes ps'
  | FStr :: ps' => [37; 115] ++ fmt_bytes ps'
  | FPStr :: ps' => [37; 46; 42; 115] ++ fmt_bytes ps'
  end.
(* fm's seven formats and their pieces (MEASURED: these bytes are the .rodata bytes at each address) *)
Definition FM_SN_FMTS : list (Z * list fpiece) :=
  [(FMT_whole, [FLit [60]; FStr; FLit [62]]);
   (FMT_tw, [FLit [60]; FStr; FLit [62; 10; 32; 32; 32; 32; 97; 32; 108; 118; 50; 58; 80; 108; 117; 103; 105; 110; 32; 46; 10]]);
   (FMT_tx, [FLit [60]; FStr; FLit [88; 62; 10; 32; 32; 32; 32; 97; 32; 108; 118; 50; 58; 80; 108; 117; 103; 105; 110; 32; 46; 10]]);
   (FMT_t1, [FLit [64; 112; 114; 101; 102; 105; 120; 32; 112; 58; 32; 60]; FPStr; FLit [62; 32; 46; 10; 112; 58]; FStr;
             FLit [10; 32; 32; 32; 32; 97; 32; 108; 118; 50; 58; 80; 108; 117; 103; 105; 110; 32; 46; 10]]);
   (FMT_t2, [FLit [80; 82; 69; 70; 73; 88; 32; 112; 58; 32; 60]; FPStr; FLit [62; 10; 112; 58]; FStr;
             FLit [10; 32; 32; 32; 32; 97; 32; 108; 118; 50; 58; 80; 108; 117; 103; 105; 110; 32; 46; 10]]);
   (FMT_t3, [FLit [64; 112; 114; 101; 102; 105; 120; 32; 58; 32; 60]; FPStr; FLit [62; 32; 46; 10; 58]; FStr;
             FLit [10; 32; 32; 32; 32; 97; 32; 108; 118; 50; 58; 80; 108; 117; 103; 105; 110; 32; 46; 10]]);
   (FMT_t1x, [FLit [64; 112; 114; 101; 102; 105; 120; 32; 112; 58; 32; 60]; FPStr; FLit [62; 32; 46; 10; 112; 58]; FStr;
              FLit [88; 10; 32; 32; 32; 32; 97; 32; 108; 118; 50; 58; 80; 108; 117; 103; 105; 110; 32; 46; 10]])].

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* the output of the format pieces over the vararg register values (a3..a7); each %s / %.*s string a C string that does
   not overlap the destination [d, d + n); a %.*s precision is 1..len s, as fm uses it (fuzz_manifest.c:275-287:
   k in [1, n - 1]; a Theorem Labs lane) *)
Fixpoint frender (W : world segs) (mem : word -> option byte) (d n : Z) (ps : list fpiece) (args : list Z)
  (out : list Z) : Prop :=
  match ps with
  | [] => out = []
  | FLit l :: ps' => exists out', out = l ++ out' /\ frender W mem d n ps' args out'
  | FStr :: ps' =>
      match args with
      | p :: args' => exists s out', cstr_ok segs W mem p s /\ (p + Z.of_nat (length s) + 1 <= d \/ d + n <= p) /\
          out = s ++ out' /\ frender W mem d n ps' args' out'
      | [] => False
      end
  | FPStr :: ps' =>
      match args with
      | k :: p :: args' => exists s out', 1 <= k <= Z.of_nat (length s) /\ cstr_ok segs W mem p s /\
          (p + Z.of_nat (length s) + 1 <= d \/ d + n <= p) /\
          out = firstn (Z.to_nat k) s ++ out' /\ frender W mem d n ps' args' out'
      | _ => False
      end
  end.

(* the post of a call that writes nothing but its stack window: return to ra, AR kept, a0 = v with R v *)
Definition rt_post_ro (STK : Z) ly S W regs mem md (R : Z -> Prop) : world segs -> config -> Prop :=
  fun W' c' => W' = W /\ exists regs' mem' md' (v : Z),
    c' = cfg_at segs (raZ regs) regs' mem' md' /\
    AR segs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
    getr regs' 10 = w64 v /\ 0 <= v < 2 ^ 64 /\ R v /\
    (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - STK <= a < spZ regs) -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
    (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a).
(* the same with user-poisoned ranges U live across the call (strstr runs inside fm's poison window, POISON.md 8) *)
Definition rt_post_roU (STK : Z) ly S (U : list (Z * Z)) W regs mem md (R : Z -> Prop) : world segs -> config -> Prop :=
  fun W' c' => W' = W /\ exists regs' mem' md' (v : Z),
    c' = cfg_at segs (raZ regs) regs' mem' md' /\
    AR segs B ly S W (unpoison U mem') md' /\ upoisoned segs W mem' U /\
    aregs_preserved regs regs' /\ same_but_materialized md md' /\
    getr regs' 10 = w64 v /\ 0 <= v < 2 ^ 64 /\ R v /\
    (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - STK <= a < spZ regs) -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
    (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a).

(* strlen interceptor (fm.asan __interceptor_strlen 0x41364, REAL = musl strlen 0x92c08): ASAN_READ_RANGE (s, len + 1) *)
Definition astrlen_realizes (pc : Z) : Prop :=
  forall ly S W regs mem md x (l : list Z),
  ecall_pre_k segs B STK_RT_STR ly S W regs mem md -> rom_viewN segs B W mem ->
  getr regs 10 = w64 x -> cstr_ok segs W mem x l ->
  SRr segs W (cfg_at segs pc regs mem md)
    (rt_post_ro STK_RT_STR ly S W regs mem md (fun v => v = Z.of_nat (length l))).

(* strchr interceptor (0x42e88, REAL = musl strchr 0x92ab4): READ_STRING (s, (r ? r - s : strlen s) + 1); c <> 0 *)
Definition astrchr_realizes (pc : Z) : Prop :=
  forall ly S W regs mem md x c (l : list Z),
  ecall_pre_k segs B STK_RT_STR ly S W regs mem md -> rom_viewN segs B W mem -> rom_viewO segs B W mem ->
  getr regs 10 = w64 x -> getr regs 11 = w64 c -> 0 < c < 256 -> cstr_ok segs W mem x l ->
  SRr segs W (cfg_at segs pc regs mem md)
    (rt_post_ro STK_RT_STR ly S W regs mem md
      (fun v => (v = 0 /\ ~ In c l) \/ (exists j, first_at l c j /\ v = x + Z.of_nat j))).

(* strncmp interceptor (0x41dc4): compares itself, READ_RANGE (s1, min (i1 + 1, n)), (s2, min (i2 + 1, n)) *)
Definition astrncmp_realizes (pc : Z) : Prop :=
  forall ly S W regs mem md x y n (l1 l2 : list Z),
  ecall_pre_k segs B STK_RT_STR ly S W regs mem md -> rom_viewN segs B W mem -> rom_viewO segs B W mem ->
  getr regs 10 = w64 x -> getr regs 11 = w64 y -> getr regs 12 = w64 n -> 0 <= n < 2 ^ 63 ->
  cstr_ok segs W mem x l1 -> cstr_ok segs W mem y l2 ->
  SRr segs W (cfg_at segs pc regs mem md)
    (rt_post_ro STK_RT_STR ly S W regs mem md (fun v => v = 0 <-> strn_eq (Z.to_nat n) l1 l2)).

(* strncasecmp interceptor (0x423a0): as strncmp with CharCaseCmp (ToLower) *)
Definition astrncasecmp_realizes (pc : Z) : Prop :=
  forall ly S W regs mem md x y n (l1 l2 : list Z),
  ecall_pre_k segs B STK_RT_STR ly S W regs mem md -> rom_viewN segs B W mem -> rom_viewO segs B W mem ->
  getr regs 10 = w64 x -> getr regs 11 = w64 y -> getr regs 12 = w64 n -> 0 <= n < 2 ^ 63 ->
  cstr_ok segs W mem x l1 -> cstr_ok segs W mem y l2 ->
  SRr segs W (cfg_at segs pc regs mem md)
    (rt_post_ro STK_RT_STR ly S W regs mem md (fun v => v = 0 <-> strncase_eq (Z.to_nat n) l1 l2)).

(* memchr (p, 0, n) interceptor (0x43b78, REAL = musl memchr 0x924a8): READ_RANGE (p, r ? r - p + 1 : n); the found and
   the not-found case (the donor's amemchr0_realizes, YG0d.v:383, has only a NUL found with 8 bytes after it) *)
Definition amemchr_realizes (pc : Z) : Prop :=
  forall ly S W regs mem md x n (l : list Z),
  ecall_pre_k segs B STK_RT_STR ly S W regs mem md -> rom_viewN segs B W mem -> rom_viewO segs B W mem ->
  getr regs 10 = w64 x -> getr regs 11 = w64 0 -> getr regs 12 = w64 n -> 0 <= n < 2 ^ 32 ->
  bytes_at segs W mem x l -> Z.of_nat (length l) = n -> 4096 <= x -> x + n + 8 <= alloc_ceiling ->
  amem_range x (n + 8) ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF x (mchr_len l) ->
  (0 < n -> shadow_hull_vis (aview segs (w_H W) mem) x (mchr_len l)) ->
  SRr segs W (cfg_at segs pc regs mem md)
    (rt_post_ro STK_RT_STR ly S W regs mem md
      (fun v => match ManifestModel.find_idx (fun c => c =? 0) l with
                | None => v = 0
                | Some k => v = x + Z.of_nat k
                end)).

(* strstr interceptor (0x4295c, REAL = musl strstr 0x92fac, then StrstrCheck: READ_STRING (s1, r ? r - s1 + len2 :
   len1 + 1), READ_RANGE (s2, len2 + 1)); called inside the poison window, so over ARU *)
Definition astrstr_realizes (pc : Z) : Prop :=
  forall ly S (U : list (Z * Z)) W regs mem md x y (lt lw : list Z),
  ecall_preU_k segs B STK_RT_STRSTR ly S U W regs mem md -> rom_viewN segs B W mem -> rom_viewO segs B W mem ->
  getr regs 10 = w64 x -> getr regs 11 = w64 y ->
  cstr_ok segs W mem x lt -> cstr_ok segs W mem y lw ->
  SRr segs W (cfg_at segs pc regs mem md)
    (rt_post_roU STK_RT_STRSTR ly S U W regs mem md
      (fun v => (v = 0 /\ no_occ lt lw) \/ (exists j, first_occ lt lw j /\ v = x + Z.of_nat j))).

(* musl isalnum (0x88350): registers only *)
Definition aisalnum_realizes (pc : Z) : Prop :=
  forall ly S W regs mem md c,
  ecall_pre_k segs B STK_RT_ISALNUM ly S W regs mem md ->
  getr regs 10 = w64 c -> 0 <= c < 256 ->
  SRr segs W (cfg_at segs pc regs mem md)
    (rt_post_ro STK_RT_ISALNUM ly S W regs mem md (fun v => v <> 0 <-> ManifestModel.is_alnum c = true)).

(* snprintf interceptor (0x45c90 -> vsnprintf interceptor 0x458a0: printf_common's %s checks, REAL = musl vsnprintf
   0x91f0c, then WRITE_RANGE (str, min (size, res + 1))) for fm's seven formats; the output fits (fm's sizes always
   do); called inside the poison window (lv2_locate.c:97), so over ARU. The image facts musl's printf_core reads:
   rom_viewN (formats, word constants) and the stack-protector cells. *)
Definition asnprintf_realizes (pc : Z) : Prop :=
  forall ly S (U : list (Z * Z)) W regs mem md d sz f (ps : list fpiece) (out : list Z),
  ecall_preU_k segs B STK_RT_PRINTF ly S U W regs mem md -> rom_viewN segs B W mem ->
  (exists cval, val_mem segs (rdW W mem) FM_GOT_canary 8 FM_canary /\ val_mem segs (rdW W mem) FM_canary 8 cval /\
     0 <= cval < 2 ^ 64) ->
  getr regs 10 = w64 d -> getr regs 11 = w64 sz -> getr regs 12 = w64 f ->
  In (f, ps) FM_SN_FMTS -> cstr_ok segs W mem f (fmt_bytes ps) ->
  frender W mem d sz ps (map (fun r : Z => bv_unsigned (getr regs (Z_to_bv 5 r))) [13; 14; 15; 16; 17]) out ->
  Z.of_nat (length out) + 1 <= sz <= 2 ^ 30 ->
  wdest_ok segs B STK_RT_PRINTF ly S W regs mem d (Z.of_nat (length out) + 1) ->
  (d + Z.of_nat (length out) + 1 <= FM_canary \/ FM_canary + 8 <= d) -> 0 < d ->
  (forall a, d <= a < d + Z.of_nat (length out) + 1 -> ~ in_rom segs a) ->
  SRr segs W (cfg_at segs pc regs mem md)
    (fun W' c' => W' = W /\ exists regs' mem' md',
       c' = cfg_at segs (raZ regs) regs' mem' md' /\
       AR segs B ly S W (unpoison U mem') md' /\ upoisoned segs W mem' U /\
       aregs_preserved regs regs' /\ same_but_materialized md md' /\
       getr regs' 10 = w64 (Z.of_nat (length out)) /\
       bytes_at segs W mem' d (out ++ [0]) /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + Z.of_nat (length out) + 1) ->
          ~ (spZ regs - STK_RT_PRINTF <= a < spZ regs) -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
       (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).

(* the runtime interface fm's walks take, one record (donor AsanAPI style, YG0d.v:530-545) *)
Record FmRt : Prop := {
  fr_strlen : astrlen_realizes PC_strlen;
  fr_strchr : astrchr_realizes PC_strchr;
  fr_strncmp : astrncmp_realizes PC_strncmp;
  fr_strncasecmp : astrncasecmp_realizes PC_strncasecmp;
  fr_memchr : amemchr_realizes PC_memchr;
  fr_strstr : astrstr_realizes PC_strstr;
  fr_isalnum : aisalnum_realizes PC_isalnum;
  fr_snprintf : asnprintf_realizes PC_snprintf;
  fr_bcmp : abcmp_realizes segs B PC_bcmp
}.
End c.

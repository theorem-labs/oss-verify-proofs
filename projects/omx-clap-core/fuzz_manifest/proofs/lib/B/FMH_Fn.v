(* B twin (fm.asan-ubsan, pin ca61e5c9eabc0050) of lib/A/FMH_Fn.v at a working branch 0d38fb8ac64, relocated A->B by
   Theorem Labs tools over the unstripped twins, every image numeral re-derived by symbol / section / string
   content and checked by revcheck (reports in (internal path)). Imports: lib.Reusable kernel kept;
   the per-image root files from lib.ReusableB; fm's own per-image files from lib.B; FMupoison shared from lib.A. *)
(* fm program part: one ASan contract per target function of fm.asan-ubsan, in the donor's per-function form (cgif_file
   lib/YC21.v:33-132: afn_pre, the call context in CTX for functions that allocate, argument registers, data premises,
   st_nev / blocks_bytes room, SRr to the return address through apost_base / ajournal). The meaning of every value comes
   from fm's pure models (lib/Prog/ManifestModel.v); fm's plain contracts lib/Prog/*_c.v are the templates for what each
   function computes. Every abort() is unreachable under the premises: each contract's post says the function returns.
   Statements only. Design: a Theorem Labs lane's design/HARNESS.md section 2. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK11 YK0s YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YC20 YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.ReusableB Require Import YCej.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMPstat FMH_Base FMH_Rt.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require ManifestModel.
Import ListNotations.
Local Open Scope Z_scope.

(* ---- pure facts restated from fm's plain proof (lib/Prog/check_round_trip_c.v:49-70, ManifestB.v:31) ---- *)
Fixpoint rt_used (u : list Z) (k fuel : nat) : nat :=
  match fuel with
  | O => O
  | S fuel' =>
      if (k <? length u)%nat && negb (ManifestModel.byte_at u (k - 1) =? 62)
      then ((if ManifestModel.plain_name (skipn k u) then 1 else 0) + rt_used u (S k) fuel')%nat
      else O
  end.
Definition rt_nk (u : list Z) : nat := rt_used u 1 (length u).
(* reader calls with a non-empty URI that check_round_trip makes: each is one fuzz_malloc (g_count + 1) *)
Definition rt_calls (u : list Z) : Z := match u with [] => 0 | _ :: _ => 3 + 4 * Z.of_nat (rt_nk u) end.
Definition rt_peak (u : list Z) (live peak : Z) : Z :=
  match u with [] => peak | _ :: _ => Z.max peak (live + Z.of_nat (length u) + 3) end.
(* no reader allocation fails in the next k: g_fail_at = SIZE_MAX and g_count stays far from it *)
Definition quiet (cnt fail k : Z) : Prop := fail = SIZE_MAXZ /\ 0 <= cnt /\ cnt + k < 2 ^ 33.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* the stack-protector cells musl's printf_core reads (asnprintf_realizes) *)
Definition fm_canary (W : world segs) (mem : word -> option byte) : Prop :=
  exists cval, val_mem segs (rdW W mem) FM_GOT_canary 8 FM_canary /\ val_mem segs (rdW W mem) FM_canary 8 cval /\
  0 <= cval < 2 ^ 64.
(* the read-only strings fm's code passes to the reader and the runtime besides the snprintf formats (FM_SN_FMTS):
   "" (fuzz_manifest.c:262), "prefix" (expected, .str and ex_prefix_word.word), "prefix" and "PREFIX" (lv2_locate.c);
   registered asan globals with redzones (fm-fn-measure.md 4.1) *)
Definition FM_RO_STRS : list (Z * list Z) :=
  [(STR_empty, []); (0x20d00, [112; 114; 101; 102; 105; 120]); (0x20d20, [112; 114; 101; 102; 105; 120]);
   (0x20fc0, [112; 114; 101; 102; 105; 120]); (0x20fe0, [80; 82; 69; 70; 73; 88])].
(* the image facts fm's code and runtime calls take, as one constant fact about B: rom_viewN (musl's word constants),
   the stack-protector cells (printf_core), cstr_ok of every read-only string and format (their shadow is the registered
   globals' constant shadow, which no journal frames), and their home in non-owned read-only bytes (str_homeA's image
   arm: the string bytes and NUL are not runtime-owned; their redzones are, fm A/AF0m.v:561). They follow from AR and the
   relro view at every state; groups take fm_img_facts as a Section hypothesis and the final instance proves it once for
   fm's TfibB (G5, G6). *)
Definition fm_img_facts : Prop :=
  forall ly S (W : world segs) mem md, AR segs B ly S W mem md ->
  arodata_okP segs FM_RLO FM_RHI B (aview segs (w_H W) mem) ->
  rom_viewN segs B W mem /\ rom_viewO segs B W mem /\ fm_canary W mem /\
  Forall (fun r => cstr_ok segs W mem (fst r) (snd r) /\
                   str_homeA segs B ly S (fst r) (Z.of_nat (length (snd r)) + 1)) FM_RO_STRS /\
  (forall f ps, In (f, ps) FM_SN_FMTS -> cstr_ok segs W mem f (fmt_bytes ps) /\
                str_homeA segs B ly S f (Z.of_nat (length (fmt_bytes ps)) + 1)).
(* the allocation traces fm's sites use are in B's universe (fm A/ACej.v Tfib_universe, 24 traces; TfibB's as_universe,
   A/AD2l.v): the premise the malloc/free call-site rules need (YC5d.v:65, :85, :106). Shared name for every group (G1). *)
Definition fm_univ : Prop := incl Tfib_universe (as_universe B).
(* the premises every fm function takes besides its own: the donor's afn_pre and the relro/rom view (it rides through
   ajournal's image clause). (The zero stack shadow, stk_sh0, follows from AR: FMH_Base.v.) *)
Definition fpre (STK : Z) ly S (W : world segs) regs mem md ch : Prop :=
  afn_pre segs B STK ly S W regs mem md ch /\
  arodata_okP segs FM_RLO FM_RHI B (aview segs (w_H W) mem).
(* the donor's apost_base *)
Definition fpost (STK : Z) (FP : list (Z * Z)) regs ly S W mem md (k : Z)
  (Q : alayout -> astate -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
  : world segs -> config -> Prop :=
  apost_base segs B STK FP regs ly S W mem md k Q.
(* a C string the function keeps using across a program call: in a live block's requested bytes (the callee's ajournal
   keeps them; AR gives their shadow), or a suffix of one of fm's read-only strings and formats (fm_img_facts gives the
   whole string's cstr_ok at every state, and a suffix's follows; ajournal frames no shadow byte below alloc_ceiling,
   G5). Suffix-closed because readings passes `u + o` on to has_prefixed (G3); k = 0 is the listed string itself. *)
Definition cstr_kept ly S (p : Z) (l : list Z) : Prop :=
  (exists b m, In (b, m) (ablocks B ly S) /\ b <= p /\ p + Z.of_nat (length l) + 1 <= b + m) \/
  (exists p0 l0 k, (In (p0, l0) FM_RO_STRS \/ (exists ps, In (p0, ps) FM_SN_FMTS /\ l0 = fmt_bytes ps)) /\
     (k <= length l0)%nat /\ p = p0 + Z.of_nat k /\ l = skipn k l0).
(* a byte window the harness copies from (memcpy source, aintrin_realizes OCpy premises, YG0d.v:317-326) *)
Definition src_rd (W : world segs) (mem : word -> option byte) (p : Z) (l : list Z) : Prop :=
  bytes_at segs W mem p l /\ 4096 <= p /\ p + Z.of_nat (length l) + 8 <= alloc_ceiling /\
  amem_range p (Z.of_nat (length l)) /\
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF p (Z.of_nat (length l)) /\
  (0 < Z.of_nat (length l) -> shadow_hull_vis (aview segs (w_H W) mem) p (Z.of_nat (length l))).
(* what one reader call (lv2_locate_manifest_names / _readings) answers and does to fuzz/alloc.c's statics
   (fm plain names_c.v:40-45): no URI; the allocation set to fail; or the rule's answer *)
Definition names_res (tb ub : list Z) (live peak cnt fail res : Z) (W' : world segs) (mem' : word -> option byte) : Prop :=
  (ub = [] /\ res = 0 /\ fm_glob segs W' mem' live peak cnt fail)
  \/ (ub <> [] /\ cnt = fail /\ res = 0 /\ fm_glob segs W' mem' live peak (cnt + 1) SIZE_MAXZ)
  \/ (ub <> [] /\ cnt <> fail /\ res = ManifestModel.names tb ub /\
      fm_glob segs W' mem' live (Z.max peak (live + Z.of_nat (length ub) + 3)) (cnt + 1) fail).

(* ======== alloc.c ======== *)

(* fuzz_alloc_live 0x81e24 (alloc.c:118-121): returns g_live *)
Definition fuzz_alloc_live_spec : Prop :=
  forall ly S W regs mem md ch live peak cnt fail,
  fpre STK_fuzz_alloc ly S W regs mem md ch -> fm_glob segs W mem live peak cnt fail ->
  SRr segs W (cfg_at segs A_fuzz_alloc_live regs mem md)
    (fpost STK_fuzz_alloc [] regs ly S W mem md 0 (fun ly' S' W' regs' mem' md' =>
       getr regs' 10 = w64 live /\ ablocks B ly' S' = ablocks B ly S /\ fm_glob segs W' mem' live peak cnt fail)).

(* fuzz_alloc_peak 0x81e30 (alloc.c:123-126): returns g_peak *)
Definition fuzz_alloc_peak_spec : Prop :=
  forall ly S W regs mem md ch live peak cnt fail,
  fpre STK_fuzz_alloc ly S W regs mem md ch -> fm_glob segs W mem live peak cnt fail ->
  SRr segs W (cfg_at segs A_fuzz_alloc_peak regs mem md)
    (fpost STK_fuzz_alloc [] regs ly S W mem md 0 (fun ly' S' W' regs' mem' md' =>
       getr regs' 10 = w64 peak /\ ablocks B ly' S' = ablocks B ly S /\ fm_glob segs W' mem' live peak cnt fail)).

(* fuzz_alloc_peak_reset 0x81e3c (alloc.c:128-131): g_peak = g_live *)
Definition fuzz_alloc_peak_reset_spec : Prop :=
  forall ly S W regs mem md ch live peak cnt fail,
  fpre STK_fuzz_alloc ly S W regs mem md ch -> fm_glob segs W mem live peak cnt fail ->
  SRr segs W (cfg_at segs A_fuzz_alloc_peak_reset regs mem md)
    (fpost STK_fuzz_alloc FM_PSTAT_FP regs ly S W mem md 0 (fun ly' S' W' regs' mem' md' =>
       ablocks B ly' S' = ablocks B ly S /\ fm_glob segs W' mem' live live cnt fail)).

(* fuzz_alloc_fail 0x81e50 (alloc.c:138-141): g_fail_at = k < SIZE_MAX - g_count ? g_count + k : SIZE_MAX *)
Definition fuzz_alloc_fail_spec : Prop :=
  forall ly S W regs mem md ch live peak cnt fail k,
  fpre STK_fuzz_alloc ly S W regs mem md ch -> fm_glob segs W mem live peak cnt fail ->
  getr regs 10 = w64 k -> 0 <= k < 2 ^ 64 ->
  SRr segs W (cfg_at segs A_fuzz_alloc_fail regs mem md)
    (fpost STK_fuzz_alloc FM_PSTAT_FP regs ly S W mem md 0 (fun ly' S' W' regs' mem' md' =>
       ablocks B ly' S' = ablocks B ly S /\
       fm_glob segs W' mem' live peak cnt (if cnt + k <? 2 ^ 64 then cnt + k else SIZE_MAXZ))).

(* fuzz_malloc 0x81b88 (on B `own` is outlined at 0x81bfc and fuzz_malloc tail-calls it) (alloc.c:61-66, own :41-49): failing() then malloc (n + 16), the head holds n and is poisoned
   (U' = [(res - 16, 16)]); or the one allocation set to fail answers NULL. Called at U = []. *)
Definition fuzz_malloc_spec (CTX : list (list Z)) : Prop :=
  forall ly S W regs mem md ch n live peak cnt fail,
  fpre STK_fuzz_malloc ly S W regs mem md ch -> In (raZ regs :: spine ch) CTX ->
  getr regs 10 = w64 n -> 1 <= n -> n + HEAD < MALLOC_MAX ->
  fm_glob segs W mem live peak cnt fail -> live + n < 2 ^ 33 -> cnt + 1 < 2 ^ 33 ->
  st_nev S + 1 <= EV_MAX -> blocks_bytes S + (n + HEAD) <= LIVE_MAX ->
  SRr segs W (cfg_at segs A_fuzz_malloc regs mem md)
    (fun W' c' =>
       (cnt = fail /\ fpost STK_fuzz_malloc FM_PSTAT_FP regs ly S W mem md 0 (fun ly' S' W' regs' mem' md' =>
          getr regs' 10 = w64 0 /\ ablocks B ly' S' = ablocks B ly S /\
          fm_glob segs W' mem' live peak (cnt + 1) SIZE_MAXZ) W' c')
       \/
       (cnt <> fail /\ exists res, apost_baseU segs B STK_fuzz_malloc FM_PSTAT_FP regs ly S W mem md 1 [] [(res - HEAD, HEAD)]
          (fun ly' S' W' regs' mem' md' =>
             getr regs' 10 = w64 res /\ 4096 + HEAD <= res /\
             ablocks B ly' S' = ablocks B ly S ++ [(res - HEAD, n + HEAD)] /\
             fm_rblock segs B ly' S' W' mem' res n /\
             range_addressable (aview segs (w_H W') mem') SHADOW_OFF res n /\
             (0 < n -> shadow_hull_vis (aview segs (w_H W') mem') res n) /\
             fm_glob segs W' mem' (live + n) (Z.max peak (live + n)) (cnt + 1) fail) W' c')).

(* fuzz_free 0x81cf4 (alloc.c:107-116, disown :51-59): unpoison the head, g_live -= n, tail-call free (p - 16);
   p = 0 returns. The tail call's free trace is [pc_free_ra0; ra] (fm-traces.md), hence the CTX premise. *)
Definition fuzz_free_spec (CTX : list (list Z)) : Prop :=
  forall ly S W regs mem md ch p n live peak cnt fail,
  In (raZ regs :: spine ch) CTX -> getr regs 10 = w64 p ->
  fm_glob segs W mem live peak cnt fail ->
  ((p = 0 /\ fpre STK_fuzz_free ly S W regs mem md ch) \/
   (p <> 0 /\ afn_preU segs B STK_fuzz_free ly S [(p - HEAD, HEAD)] W regs mem md ch /\
    arodata_okP segs FM_RLO FM_RHI B (aview segs (w_H W) mem) /\
    fm_rblock segs B ly S W mem p n /\ n <= live)) ->
  st_nev S + 1 <= EV_MAX ->
  SRr segs W (cfg_at segs A_fuzz_free regs mem md)
    (fun W' c' =>
       (p = 0 /\ fpost STK_fuzz_free [] regs ly S W mem md 0 (fun ly' S' W' regs' mem' md' =>
          ablocks B ly' S' = ablocks B ly S /\ fm_glob segs W' mem' live peak cnt fail) W' c')
       \/
       (p <> 0 /\ apost_baseU segs B STK_fuzz_free (ablocks_fp [(p - HEAD, n + HEAD)] ++ FM_PSTAT_FP) regs ly S W mem md 1
          [(p - HEAD, HEAD)] []
          (fun ly' S' W' regs' mem' md' =>
             (exists l1 l2, ablocks B ly S = l1 ++ (p - HEAD, n + HEAD) :: l2 /\ ablocks B ly' S' = l1 ++ l2) /\
             fm_glob segs W' mem' (live - n) peak cnt fail) W' c')).

(* ======== lv2_locate.c ======== *)

(* name_char 0x825ac (lv2_locate.c:36-39): isalnum, '_', '-', ':', '%', '\\', >= 0x80. RISC-V `char` is unsigned: both
   callers zero-extend (has_prefixed's two text-byte reads `lbu s6` / `lbu a0`; on B has_prefixed+0xf4 / +0x130), so a0 = c with 0 <= c < 256 (G2's correction) *)
Definition name_char_spec : Prop :=
  forall ly S W regs mem md ch c live peak cnt fail,
  fpre STK_name_char ly S W regs mem md ch -> fm_glob segs W mem live peak cnt fail ->
  getr regs 10 = w64 c -> 0 <= c < 256 ->
  SRr segs W (cfg_at segs A_name_char regs mem md)
    (fpost STK_name_char [] regs ly S W mem md 0 (fun ly' S' W' regs' mem' md' =>
       getr regs' 10 = w64 (if ManifestModel.name_char c then 1 else 0) /\
       ablocks B ly' S' = ablocks B ly S /\ fm_glob segs W' mem' live peak cnt fail)).

(* has_prefixed 0x823e4 (lv2_locate.c:57-78): prefix = text + q (fm plain has_prefixed_c.v:12-36) *)
Definition has_prefixed_spec : Prop :=
  forall ly S W regs mem md ch t q plen lp (tb lb : list Z) live peak cnt fail,
  fpre STK_has_prefixed ly S W regs mem md ch -> fm_glob segs W mem live peak cnt fail ->
  getr regs 10 = w64 t -> getr regs 11 = w64 (t + q) -> getr regs 12 = w64 plen -> getr regs 13 = w64 lp ->
  cstr_ok segs W mem t tb -> cstr_ok segs W mem lp lb -> cstr_kept ly S t tb -> cstr_kept ly S lp lb -> lb <> [] ->
  0 <= q -> 0 <= plen -> q + plen <= Z.of_nat (length tb) -> Z.of_nat (length tb) <= MANIFEST_MAX ->
  SRr segs W (cfg_at segs A_has_prefixed regs mem md)
    (fpost STK_has_prefixed [] regs ly S W mem md 0 (fun ly' S' W' regs' mem' md' =>
       getr regs' 10 = w64 (if ManifestModel.token tb (firstn (Z.to_nat plen) (skipn (Z.to_nat q) tb)) lb then 1 else 0) /\
       ablocks B ly' S' = ablocks B ly S /\ fm_glob segs W' mem' live peak cnt fail)).

(* lv2_locate_manifest_readings 0x81e94 (lv2_locate.c:87-149), called only from lv2_locate_manifest_names with the
   out-parameter at the caller's sp (`mv a2, sp`, 0x81e80): rp = sp, so its journal window reaches sp + 16 (astk_ok
   wants a 16-aligned sp0) and the post keeps [sp + 8, sp + 16) (names' saved ra) unchanged (G3)
   (fm plain readings_c.v:46-72). The poison window (U = [(whole - 16, 16)]) opens and closes inside. *)
(* B only (a Theorem Labs lane 07:48Z, a Theorem Labs lane's case): B's readings keeps rp in s0 (`mv s0, a2` at 0x81ecc; A kept the shadow base
   there), so at its fuzz_malloc / fuzz_free calls achain walks one frame from s0 = entry sp; the trace is the fixed
   [0x81f00; 0x81e88] / [0x81f38; 0x81e88] only when entry sp + 16 < ly_top. Hence the STRICT premise below, and names_spec
   asks spZ regs < ly_top (names passes sp - 16); each caller discharges it from its own frame. *)
Definition readings_spec (CTX : list (list Z)) : Prop :=
  forall ly S W regs mem md ch t u rp v (tb ub : list Z) live peak cnt fail,
  afn_pre segs B STK_readings ly S W regs mem md ch -> In (raZ regs :: spine ch) CTX ->
  arodata_okP segs FM_RLO FM_RHI B (aview segs (w_H W) mem) ->
  getr regs 10 = w64 t -> getr regs 11 = w64 u -> getr regs 12 = w64 rp -> rp = spZ regs ->
  (forall a, rp <= a < rp + 16 -> apresent (w_H W) mem a) -> spZ regs + 16 < ly_top ly ->
  val_mem segs (rdW W mem) rp 8 v -> 0 <= v < 2 ^ 63 ->
  cstr_ok segs W mem t tb -> cstr_ok segs W mem u ub -> cstr_kept ly S t tb -> cstr_kept ly S u ub ->
  (length ub <= 255)%nat -> Z.of_nat (length tb) <= MANIFEST_MAX ->
  fm_glob segs W mem live peak cnt fail -> live + Z.of_nat (length ub) + 3 < 2 ^ 33 -> cnt + 1 < 2 ^ 33 ->
  st_nev S + EV_names <= EV_MAX -> blocks_bytes S + LIVE_names <= LIVE_MAX ->
  SRr segs W (cfg_at segs A_readings regs mem md)
    (fun W' c' => exists ly' S' regs' mem' md' res,
       c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
       ajournal segs B (STK_readings + 16) (spZ regs + 16) FM_PSTAT_FP ly S W mem md [] ly' S' W' mem' md' EV_names /\
       (forall a, spZ regs + 8 <= a < spZ regs + 16 -> aview segs (w_H W') mem' a = aview segs (w_H W) mem a) /\
       aregs_preserved regs regs' /\
       getr regs' 10 = w64 res /\ Permutation (ablocks B ly' S') (ablocks B ly S) /\
       names_res tb ub live peak cnt fail res W' mem' /\
       val_mem segs (rdW W' mem') rp 8
         (if (length ub =? 0)%nat || (cnt =? fail) then v else v + Z.of_nat (ManifestModel.nreadings tb ub))).

(* lv2_locate_manifest_names 0x81e74 (lv2_locate.c:80-85; fm plain names_c.v:48-73) *)
Definition names_spec (CTX : list (list Z)) : Prop :=
  forall ly S W regs mem md ch t u (tb ub : list Z) live peak cnt fail,
  fpre STK_names ly S W regs mem md ch -> In (raZ regs :: spine ch) CTX -> spZ regs < ly_top ly ->
  getr regs 10 = w64 t -> getr regs 11 = w64 u ->
  cstr_ok segs W mem t tb -> cstr_ok segs W mem u ub -> cstr_kept ly S t tb -> cstr_kept ly S u ub ->
  (length ub <= 255)%nat -> Z.of_nat (length tb) <= MANIFEST_MAX ->
  fm_glob segs W mem live peak cnt fail -> live + Z.of_nat (length ub) + 3 < 2 ^ 33 -> cnt + 1 < 2 ^ 33 ->
  st_nev S + EV_names <= EV_MAX -> blocks_bytes S + LIVE_names <= LIVE_MAX ->
  SRr segs W (cfg_at segs A_names regs mem md)
    (fpost STK_names FM_PSTAT_FP regs ly S W mem md EV_names (fun ly' S' W' regs' mem' md' => exists res,
       getr regs' 10 = w64 res /\ Permutation (ablocks B ly' S') (ablocks B ly S) /\
       names_res tb ub live peak cnt fail res W' mem')).

(* ======== fuzz_manifest.c: the rule ======== *)

(* plain 0x81988 (fuzz_manifest.c:71-81; fm plain plain_c.v:12-23) *)
Definition plain_spec : Prop :=
  forall ly S W regs mem md ch s (l : list Z) live peak cnt fail,
  fpre STK_plain ly S W regs mem md ch -> fm_glob segs W mem live peak cnt fail ->
  getr regs 10 = w64 s -> cstr_ok segs W mem s l -> (length l <= 255)%nat ->
  SRr segs W (cfg_at segs A_plain regs mem md)
    (fpost STK_plain [] regs ly S W mem md 0 (fun ly' S' W' regs' mem' md' =>
       getr regs' 10 = w64 (if ManifestModel.plain_name l then 1 else 0) /\
       ablocks B ly' S' = ablocks B ly S /\ fm_glob segs W' mem' live peak cnt fail)).

(* expected 0x81274 (fuzz_manifest.c:125-172; fm plain expected_c.v:13-30): the rule's answer is ManifestModel.names *)
Definition expected_spec : Prop :=
  forall ly S W regs mem md ch t u (tb ub : list Z) live peak cnt fail,
  fpre STK_expected ly S W regs mem md ch -> fm_glob segs W mem live peak cnt fail ->
  getr regs 10 = w64 t -> getr regs 11 = w64 u ->
  cstr_ok segs W mem t tb -> cstr_ok segs W mem u ub -> cstr_kept ly S t tb -> cstr_kept ly S u ub ->
  (length ub <= 255)%nat -> Z.of_nat (length tb) <= MANIFEST_MAX ->
  SRr segs W (cfg_at segs A_expected regs mem md)
    (fpost STK_expected [] regs ly S W mem md 0 (fun ly' S' W' regs' mem' md' =>
       getr regs' 10 = w64 (ManifestModel.names tb ub) /\
       ablocks B ly' S' = ablocks B ly S /\ fm_glob segs W' mem' live peak cnt fail)).

(* ======== fuzz_manifest.c: the checks; each returns, so none of the aborts is reached ======== *)

(* check_bounded_alloc 0x80f04 (fuzz_manifest.c:191-197): held <= uri_len + 3 *)
Definition check_bounded_alloc_spec : Prop :=
  forall ly S W regs mem md ch held ul live peak cnt fail,
  fpre STK_check_bounded_alloc ly S W regs mem md ch -> fm_glob segs W mem live peak cnt fail ->
  getr regs 10 = w64 held -> getr regs 11 = w64 ul -> 0 <= held <= ul + 3 -> 0 <= ul < 2 ^ 63 ->
  SRr segs W (cfg_at segs A_check_bounded_alloc regs mem md)
    (fpost STK_check_bounded_alloc [] regs ly S W mem md 0 (fun ly' S' W' regs' mem' md' =>
       ablocks B ly' S' = ablocks B ly S /\ fm_glob segs W' mem' live peak cnt fail)).

(* check_as_written 0x80f2c (fuzz_manifest.c:199-215): named = the rule's answer *)
Definition check_as_written_spec : Prop :=
  forall ly S W regs mem md ch t u (tb ub : list Z) live peak cnt fail,
  fpre STK_check_as_written ly S W regs mem md ch -> fm_glob segs W mem live peak cnt fail ->
  getr regs 10 = w64 t -> getr regs 11 = w64 u -> getr regs 12 = w64 (ManifestModel.names tb ub) ->
  cstr_ok segs W mem t tb -> cstr_ok segs W mem u ub -> cstr_kept ly S t tb -> cstr_kept ly S u ub ->
  (length ub <= 255)%nat -> Z.of_nat (length tb) <= MANIFEST_MAX ->
  SRr segs W (cfg_at segs A_check_as_written regs mem md)
    (fpost STK_check_as_written [] regs ly S W mem md 0 (fun ly' S' W' regs' mem' md' =>
       ablocks B ly' S' = ablocks B ly S /\ fm_glob segs W' mem' live peak cnt fail)).

(* check_reject_clean 0x80f68 (fuzz_manifest.c:217-223): g_live = live_before *)
Definition check_reject_clean_spec : Prop :=
  forall ly S W regs mem md ch live peak cnt fail,
  fpre STK_check_reject_clean ly S W regs mem md ch -> fm_glob segs W mem live peak cnt fail ->
  getr regs 10 = w64 live ->
  SRr segs W (cfg_at segs A_check_reject_clean regs mem md)
    (fpost STK_check_reject_clean [] regs ly S W mem md 0 (fun ly' S' W' regs' mem' md' =>
       ablocks B ly' S' = ablocks B ly S /\ fm_glob segs W' mem' live peak cnt fail)).

(* check_reject_clean_starved 0x80f9c (fuzz_manifest.c:226-234): the reader's one allocation fails (fuzz_alloc_fail(0)),
   it holds nothing, fuzz_alloc_fail(SIZE_MAX) restores g_fail_at (fm plain check_reject_clean_starved_c.v:25-63) *)
Definition check_reject_clean_starved_spec (CTX : list (list Z)) : Prop :=
  forall ly S W regs mem md ch t u (tb ub : list Z) live peak cnt fail,
  fpre STK_check_reject_clean_starved ly S W regs mem md ch -> In (raZ regs :: spine ch) CTX ->
  getr regs 10 = w64 t -> getr regs 11 = w64 u ->
  cstr_ok segs W mem t tb -> cstr_ok segs W mem u ub -> cstr_kept ly S t tb -> cstr_kept ly S u ub ->
  (length ub <= 255)%nat -> Z.of_nat (length tb) <= MANIFEST_MAX ->
  fm_glob segs W mem live peak cnt fail -> quiet cnt fail 1 -> live + Z.of_nat (length ub) + 3 < 2 ^ 33 ->
  st_nev S + EV_check_reject_clean_starved <= EV_MAX -> blocks_bytes S + LIVE_names <= LIVE_MAX ->
  SRr segs W (cfg_at segs A_check_reject_clean_starved regs mem md)
    (fpost STK_check_reject_clean_starved FM_PSTAT_FP regs ly S W mem md EV_check_reject_clean_starved
       (fun ly' S' W' regs' mem' md' =>
          Permutation (ablocks B ly' S') (ablocks B ly S) /\
          fm_glob segs W' mem' live peak (if (length ub =? 0)%nat then cnt else cnt + 1) SIZE_MAXZ)).

(* as_ruled 0x81ac8 (fuzz_manifest.c:244-251; fm plain as_ruled_c.v:38-61): the reader answers what the rule says *)
Definition as_ruled_spec (CTX : list (list Z)) : Prop :=
  forall ly S W regs mem md ch t u (tb ub : list Z) live peak cnt fail,
  fpre STK_as_ruled ly S W regs mem md ch -> In (raZ regs :: spine ch) CTX ->
  getr regs 10 = w64 t -> getr regs 11 = w64 u ->
  cstr_ok segs W mem t tb -> cstr_ok segs W mem u ub -> cstr_kept ly S t tb -> cstr_kept ly S u ub ->
  (length ub <= 255)%nat -> Z.of_nat (length tb) <= MANIFEST_MAX ->
  fm_glob segs W mem live peak cnt fail -> quiet cnt fail 1 -> live + Z.of_nat (length ub) + 3 < 2 ^ 33 ->
  st_nev S + EV_as_ruled <= EV_MAX -> blocks_bytes S + LIVE_as_ruled <= LIVE_MAX ->
  SRr segs W (cfg_at segs A_as_ruled regs mem md)
    (fpost STK_as_ruled FM_PSTAT_FP regs ly S W mem md EV_as_ruled (fun ly' S' W' regs' mem' md' =>
       Permutation (ablocks B ly' S') (ablocks B ly S) /\
       fm_glob segs W' mem' live (rt_peak ub live peak) (if (length ub =? 0)%nat then cnt else cnt + 1) SIZE_MAXZ)).

(* check_no_overread 0x80bd4 (fuzz_manifest.c:176-189; fm plain check_no_overread_c.v:40-60): four padded copies, the
   reader asked twice answers the same; the copies are freed (the last by a tail call, trace [pc_free_ra0; ra]) *)
Definition check_no_overread_spec (CTX : list (list Z)) : Prop :=
  forall ly S W regs mem md ch up tp (ub tb : list Z) live peak cnt fail,
  fpre STK_check_no_overread ly S W regs mem md ch -> In (raZ regs :: spine ch) CTX ->
  getr regs 10 = w64 up -> getr regs 11 = w64 (Z.of_nat (length ub)) ->
  getr regs 12 = w64 tp -> getr regs 13 = w64 (Z.of_nat (length tb)) ->
  src_rd W mem up ub -> src_rd W mem tp tb -> Forall (fun c => c <> 0) ub -> Forall (fun c => c <> 0) tb ->
  (* the input windows are empty or inside a live block (the input, tfib_lib_pre_x); an image window's shadow is not
     framed across the copies' mallocs (G5) *)
  (ub = [] \/ exists b m, In (b, m) (ablocks B ly S) /\ b <= up /\ up + Z.of_nat (length ub) <= b + m) ->
  (tb = [] \/ exists b m, In (b, m) (ablocks B ly S) /\ b <= tp /\ tp + Z.of_nat (length tb) <= b + m) ->
  (length ub <= 255)%nat -> Z.of_nat (length tb) <= MANIFEST_MAX ->
  fm_glob segs W mem live peak cnt fail -> quiet cnt fail 2 -> live + Z.of_nat (length ub) + 3 < 2 ^ 33 ->
  st_nev S + EV_check_no_overread <= EV_MAX -> blocks_bytes S + LIVE_check_no_overread <= LIVE_MAX ->
  SRr segs W (cfg_at segs A_check_no_overread regs mem md)
    (fpost STK_check_no_overread FM_PSTAT_FP regs ly S W mem md EV_check_no_overread (fun ly' S' W' regs' mem' md' =>
       Permutation (ablocks B ly' S') (ablocks B ly S) /\
       fm_glob segs W' mem' live (rt_peak ub live peak) (if (length ub =? 0)%nat then cnt else cnt + 2) SIZE_MAXZ)).

(* check_round_trip 0x80ff8 (fuzz_manifest.c:253-291; fm plain check_round_trip_c.v:89-105): the empty text names
   nothing, "<uri>" names it, "<uriX>" answers as ruled, and per split point k the three prefix spellings name it and
   the X spelling answers as ruled (ManifestModel rt_empty :169, rt_whole :204, rt_t1 :280, rt_t2 :301, rt_t3 :322);
   its own malloc (3 n + 64) is granted *)
Definition check_round_trip_spec (CTX : list (list Z)) : Prop :=
  forall ly S W regs mem md ch u (ub : list Z) live peak cnt fail,
  fpre STK_check_round_trip ly S W regs mem md ch -> In (raZ regs :: spine ch) CTX ->
  getr regs 10 = w64 u -> cstr_ok segs W mem u ub -> cstr_kept ly S u ub -> (length ub <= 255)%nat ->
  fm_glob segs W mem live peak cnt fail -> quiet cnt fail (3 + 4 * 254) -> live + Z.of_nat (length ub) + 3 < 2 ^ 33 ->
  st_nev S + EV_check_round_trip <= EV_MAX -> blocks_bytes S + LIVE_check_round_trip <= LIVE_MAX ->
  SRr segs W (cfg_at segs A_check_round_trip regs mem md)
    (fpost STK_check_round_trip FM_PSTAT_FP regs ly S W mem md EV_check_round_trip (fun ly' S' W' regs' mem' md' =>
       Permutation (ablocks B ly' S') (ablocks B ly S) /\
       fm_glob segs W' mem' live (rt_peak ub live peak) (cnt + rt_calls ub) SIZE_MAXZ)).

(* the program part below LLVMFuzzerTestOneInput, one record (each field instantiated with fm's CTX_<fn> lists of
   lib/A/ACej.v) *)
Record FmFns (CTX_fuzz_malloc CTX_fuzz_free CTX_readings CTX_names CTX_starved CTX_as_ruled CTX_cno CTX_crt
  : list (list Z)) : Prop := {
  ff_alloc_live : fuzz_alloc_live_spec;
  ff_alloc_peak : fuzz_alloc_peak_spec;
  ff_alloc_peak_reset : fuzz_alloc_peak_reset_spec;
  ff_alloc_fail : fuzz_alloc_fail_spec;
  ff_malloc : fuzz_malloc_spec CTX_fuzz_malloc;
  ff_free : fuzz_free_spec CTX_fuzz_free;
  ff_name_char : name_char_spec;
  ff_has_prefixed : has_prefixed_spec;
  ff_readings : readings_spec CTX_readings;
  ff_names : names_spec CTX_names;
  ff_plain : plain_spec;
  ff_expected : expected_spec;
  ff_bounded_alloc : check_bounded_alloc_spec;
  ff_as_written : check_as_written_spec;
  ff_reject_clean : check_reject_clean_spec;
  ff_starved : check_reject_clean_starved_spec CTX_starved;
  ff_as_ruled : as_ruled_spec CTX_as_ruled;
  ff_no_overread : check_no_overread_spec CTX_cno;
  ff_round_trip : check_round_trip_spec CTX_crt
}.
End c.
